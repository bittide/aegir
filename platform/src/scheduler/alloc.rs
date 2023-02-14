// Copyright 2023 Google LLC
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::app::CommsHandle;
use crate::app::ServiceHandle;
use crate::calendar::Buffering;
use crate::mailbox::MailBox;
use crate::scheduler::path;
use crate::scheduler::path::Path;
use crate::scheduler::RandomAllocation;
use itertools::Itertools;
use petgraph::prelude::*;
use rand::Rng;
use std::collections::HashMap;

use crate::{Application, Error, HardwareSpec};
use crate::{LinkSpec, NodeSpec};

use crate::MappingConfiguration1x1;
use crate::MappingConfiguration1x1Network;

/// Batching parameters computed for a a path.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PathBatching {
    pub src_cycles: usize,
    pub dst_cycles: HashMap<EdgeIndex, usize>,
    pub batch_size: usize,
}

/// Represents the allocation of nodes to system nodes and links to system
/// physical links.
#[derive(Clone, Debug)]
pub struct SystemAllocation {
    /// maps app_node => sys_node
    pub nodes: HashMap<ServiceHandle, NodeIndex>,
    /// maps app_link => Path. If the endpoints of the connection are co-located,
    /// then there's no corresponding path.
    pub links: HashMap<CommsHandle, Option<Path>>,

    /// The number of required cycles to evaluate a Service node via the
    /// Allocation's mapping to a Compute node. Key is an Service node index,
    /// value is number of cycles.
    pub compute_cycles: HashMap<ServiceHandle, usize>,
}

impl SystemAllocation {
    fn new() -> Self {
        Self {
            nodes: HashMap::new(),
            links: HashMap::new(),
            compute_cycles: HashMap::new(),
        }
    }
}

/// Components operating at different frequencies need to communicate data
/// in batches, i.e., bundles of frames. The primary motivation for doing so
/// are that components can not operate on a fractional number of frames.
/// Links are expected to send one frame per cycle.
///
/// Batches occur on links connecting the gather (tx) of node i, to the
/// scatter (rx) of node j, over link L_{i,j}.
///
/// For example, let f_G = 30, f_L = 100, f_S = 20 then
///
/// frequency(Gather) = f_G = c_i * f_L, e.g., c_i = 3/10
///
/// frequency(Scatter) = f_S = c_j * f_L, e.g., c_j = 1/5
///
/// the batch size on this link is B = LCM(1, 1/c_i, 1/c_j)
///
/// B = LCM(1, 10/3, 5/1) = LCM(10, 5) = 10
///
/// The gather unit sends 10 frames every B * c_i = 3 node i ticks.
///
/// The scatter unit receives 10 frames every B * c_j = 2 node j ticks
///
/// The link transmits 1 frame per link tick.
pub fn compute_batch_size(sys_spec: &HardwareSpec, path: &Path) -> PathBatching {
    let (src_node_id, _) = sys_spec.get_link_endpoints(path.source());
    let dst_node_ids = path
        .destinations()
        .iter()
        .map(|link_id| sys_spec.get_link_endpoints(*link_id).1)
        .collect::<Vec<_>>();
    let src_node = sys_spec.get_node(src_node_id);
    let src_freq = src_node
        .borrow()
        .into_provisioned_node()
        .unwrap()
        .frequency()
        .value;
    let dst_freqs = dst_node_ids
        .iter()
        .map(|dst_node| {
            sys_spec
                .get_node(*dst_node)
                .borrow()
                .into_provisioned_node()
                .unwrap()
                .frequency()
                .value
        })
        .collect::<Vec<_>>();
    // Link frequencies and frame sizes must all be the same.
    let link_freq = sys_spec
        .get_link(path.source())
        .into_provisioned_link()
        .unwrap()
        .frequency()
        .value;
    assert!(path.all_links().iter().all(|link_id| {
        sys_spec
            .get_link(*link_id)
            .into_provisioned_link()
            .unwrap()
            .frequency()
            .value
            == link_freq
    }));
    let link_frame_size = sys_spec.get_link(path.source()).frame_size();
    assert!(path
        .all_links()
        .iter()
        .all(|link_id| sys_spec.get_link(*link_id).frame_size() == link_frame_size));
    // Given c_i = f_G / f_L,
    // 1 / c_i = (f_L  / gcd(f_L, f_G)) / (f_G / gcd(f_L, f_G))
    // N = f_L  / gcd(f_L, f_G)
    // M = f_G / gcd(f_L, f_G)
    //
    // batch-size B = lcm(1, 1/ci, {1/cj})
    //
    // given 1/ci = N/M, and similarly 1/cj = P/Q where both fractions N/M & P/Q are
    // simplified then,
    //
    // lcm(1, N/M, {P/Q})
    //   = lcm(1, N, {P}) / gcd(1, M, {Q})
    //   = lcm(N, {P})
    //
    // since gcd(1, M, {Q}) = 1
    let inverse_ci_numerator = link_freq / num::integer::gcd(src_freq, link_freq);
    let inverse_cj_numerator = dst_freqs
        .iter()
        .map(|dst_freq| link_freq / num::integer::gcd(*dst_freq, link_freq))
        .collect::<Vec<_>>();
    let batch_size = inverse_cj_numerator
        .iter()
        .fold(inverse_ci_numerator, |accum, x| {
            num::integer::lcm(accum, *x)
        });
    PathBatching {
        src_cycles: (batch_size * src_freq) / link_freq,
        batch_size: batch_size,
        dst_cycles: path
            .destinations()
            .iter()
            .zip(dst_freqs.iter())
            .map(|(edge_id, dst_freq)| (*edge_id, (batch_size * dst_freq) / link_freq))
            .collect::<HashMap<_, _>>(),
    }
}

pub(super) fn alloc_1x1_network(
    app_spec: &Application,
    sys_spec: &HardwareSpec,
    cfg: &MappingConfiguration1x1Network,
) -> Result<SystemAllocation, Error> {
    let mut alloc = SystemAllocation::new();
    // for a 1:1 mapping, the order in which the system nodes were created
    // is the same as the order in which the service nodes were iterated, so we can
    // pair them. For N service nodes, the first N nodes of the sys_spec iteration
    // order are the compute nodes.
    let app_node_count = app_spec.iter_nodes().count();
    assert_eq!(2 * app_node_count, sys_spec.iter_nodes().count());
    // The app node s(i), the compute node c(i) to which it was mapped and the switch
    // node X(i) off of which c(i) hangs.
    let node_map = app_spec
        .iter_nodes()
        .zip(
            sys_spec
                .iter_nodes()
                .take(app_node_count)
                .zip(sys_spec.iter_nodes().dropping(app_node_count)),
        )
        .collect::<HashMap<_, _>>();
    let mut mailboxes = HashMap::<NodeIndex, MailBox>::new();
    for (app_node_id, (compute_node_id, switch_node_id)) in node_map.iter() {
        // Sanity check: all outputs of the compute node terminate on the switch node
        // and all inputs to the compute node originate from the switch node.
        assert!(
            sys_spec.get_input_links(*compute_node_id).all(|edge_ref| {
                let (src_node_id, _) = sys_spec.get_link_endpoints(edge_ref.id());
                src_node_id == *switch_node_id
            }) && sys_spec.get_output_links(*compute_node_id).all(|edge_ref| {
                let (_, dst_node_id) = sys_spec.get_link_endpoints(edge_ref.id());
                dst_node_id == *switch_node_id
            })
        );
        let mut mailbox = MailBox::new(app_spec, &[*app_node_id]);
        let app_node = ServiceHandle::new(app_spec.id(), *app_node_id);
        alloc.nodes.insert(app_node.clone(), *compute_node_id);
        alloc
            .compute_cycles
            .insert(app_node.clone(), cfg.compute_cycles_per_service_node);
        let src_app_input_port_count = app_spec.get_input_links(*app_node_id).count();
        for edge_ref in app_spec.get_output_links(*app_node_id).into_iter() {
            let (_, app_dst_node_id) = app_spec.get_link_endpoints(edge_ref.id());
            let (dst_compute_node_id, dst_switch_node_id) = node_map[&app_dst_node_id];
            let (src_port, dst_port) = edge_ref.weight().get_ports();
            log::debug!(
                "alloc_1x1_network src_node {:?} src_port {} dst_node {:?} dst_port {}",
                compute_node_id,
                src_port,
                dst_compute_node_id,
                dst_port
            );
            let src_port: usize = src_port.into();
            let dst_port: usize = dst_port.into();
            let dst_app_output_port_count = app_spec.get_output_links(dst_compute_node_id).count();
            // l(c(i), X(i))
            let compute_to_switch_edge = sys_spec
                .get_output_links(*compute_node_id)
                .find(|edge_ref| {
                    let edge_src_port: usize = edge_ref.weight().src_port().into();
                    edge_src_port == src_port
                })
                .unwrap();
            log::trace!(
                "alloc_1x1_network src_compute to src_switch edge: {:?}",
                compute_to_switch_edge.id()
            );
            // l(X(i), X(j))
            let switch_to_switch_edge = sys_spec
                .get_output_links(*switch_node_id)
                .find(|edge_ref| {
                    let edge_src_port: usize = edge_ref.weight().src_port().into();
                    // src-app inputs are src-switch outputs
                    edge_src_port == src_app_input_port_count + src_port
                })
                .unwrap();
            log::trace!(
                "alloc_1x1_network src_switch to dst_switch edge: {:?}",
                switch_to_switch_edge.id()
            );
            let switch_to_switch_edge_check = sys_spec
                .get_input_links(dst_switch_node_id)
                .find(|edge_ref| {
                    let edge_dst_port: usize = edge_ref.weight().dst_port().into();
                    // dst-app outputs are dst-switch inputs
                    edge_dst_port == dst_app_output_port_count + dst_port
                })
                .unwrap();
            assert_eq!(switch_to_switch_edge.id(), switch_to_switch_edge_check.id());
            // l(X(j), c(j))
            let switch_to_compute_edge = sys_spec
                .get_output_links(dst_switch_node_id)
                .find(|edge_ref| {
                    let edge_dst_port: usize = edge_ref.weight().dst_port().into();
                    edge_dst_port == dst_port
                })
                .unwrap();
            log::trace!(
                "alloc_1x1_network dst_switch to dst_compute edge: {:?}",
                switch_to_compute_edge.id()
            );
            // Allocate the path l(c(i), X(i)) -> l(X(i), X(j)) -> l(X(j), c(j)) for the app link c(s(i), s(j))
            let sys_spec_path = vec![
                compute_to_switch_edge.id(),
                switch_to_switch_edge.id(),
                switch_to_compute_edge.id(),
            ];
            let app_edge = CommsHandle::new(app_spec.id(), edge_ref.id());
            mailbox.map_connection_src_to_gather(app_edge.clone(), sys_spec, sys_spec_path[0])?;
            alloc
                .links
                .insert(app_edge.clone(), Some(Path::new(&sys_spec_path)?));
            log::trace!(
                "1:1 mapping: compute {}:{} --> switch {}:{} --> switch {}:{} --> compute dst {}:{}, batch size: {:?}",
                sys_spec.get_node(*compute_node_id).borrow().name(),
                src_port,
                sys_spec.get_node(*switch_node_id).borrow().name(),
                src_port,
                sys_spec.get_node(dst_switch_node_id).borrow().name(),
                dst_port,
                sys_spec.get_node(dst_compute_node_id).borrow().name(),
                dst_port,
                compute_batch_size(sys_spec, alloc.links[&app_edge].as_ref().unwrap())
            );
        }
        mailboxes.insert(*app_node_id, mailbox);
    }
    for app_node_id in app_spec.iter_nodes() {
        let mut mailbox = mailboxes.remove(&app_node_id).unwrap();
        for edge_ref in app_spec.get_input_links(app_node_id) {
            let app_edge = CommsHandle::new(app_spec.id(), edge_ref.id());
            let path_last_hop = alloc.links[&app_edge].as_ref().unwrap().destinations()[0];
            mailbox.map_connection_dst_to_scatter(app_edge, sys_spec, path_last_hop)?;
        }
        mailbox.materialize_addresses(sys_spec)?;
        let (sys_node_id, _) = node_map[&app_node_id];
        sys_spec
            .get_node(sys_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(mailbox);
    }
    log::trace!("Allocation: {:?}", alloc);
    Ok(alloc)
}

pub(super) fn alloc_1x1(
    app_spec: &Application,
    sys_spec: &HardwareSpec,
    cfg: &MappingConfiguration1x1,
) -> Result<SystemAllocation, Error> {
    let mut alloc = SystemAllocation::new();

    // for a 1:1 mapping, the order in which the system nodes were created
    // is the same as the order in which the app nodes were iterated, so we can pair them.
    let mut mailboxes = HashMap::<NodeIndex, MailBox>::new();
    for (app_node_id, sys_node) in app_spec.iter_nodes().zip(sys_spec.iter_nodes()) {
        let app_node = ServiceHandle::new(app_spec.id(), app_node_id);
        alloc.nodes.insert(app_node.clone(), sys_node);
        alloc
            .compute_cycles
            .insert(app_node.clone(), cfg.compute_cycles_per_service_node);
        let mut mailbox = MailBox::new(app_spec, &[app_node_id]);
        // the order in which the links are created does not necessarily
        // make edge indices to correspond to the same ports, so we need to
        // search for the right port.
        for link in app_spec.get_output_links(app_node_id).into_iter() {
            let src_port = link.weight().src_port();
            let mut found = false;
            for sys_link in sys_spec.get_output_links(sys_node) {
                let (src_node_id, dst_node_id) = sys_spec.get_link_endpoints(sys_link.id());
                if sys_link.weight().src_port() == src_port {
                    let app_edge = CommsHandle::new(app_spec.id(), link.id());
                    alloc
                        .links
                        .insert(app_edge.clone(), Some(Path::new(&[sys_link.id()])?));
                    found = true;
                    mailbox.map_connection_src_to_gather(
                        app_edge.clone(),
                        sys_spec,
                        sys_link.id(),
                    )?;
                    let dst_port = sys_link.weight().dst_port();
                    log::trace!(
                        "1:1 mapping, src {}:{} --> dst {}:{}, batch size: {:?}",
                        sys_spec.get_node(src_node_id).borrow().name(),
                        src_port,
                        sys_spec.get_node(dst_node_id).borrow().name(),
                        dst_port,
                        compute_batch_size(sys_spec, alloc.links[&app_edge].as_ref().unwrap())
                    );
                    break;
                }
            }
            if !found {
                return Err(Error::InvalidPort(app_node_id, link.id(), src_port));
            }
        }
        mailboxes.insert(app_node_id, mailbox);
    }
    for app_node_id in app_spec.iter_nodes() {
        let mut mailbox = mailboxes.remove(&app_node_id).unwrap();
        for edge_ref in app_spec.get_input_links(app_node_id) {
            let app_edge = CommsHandle::new(app_spec.id(), edge_ref.id());
            let sys_link_id = alloc.links[&app_edge].as_ref().unwrap().destinations()[0];
            mailbox.map_connection_dst_to_scatter(app_edge, sys_spec, sys_link_id)?;
        }
        mailbox.materialize_addresses(sys_spec)?;
        let app_node = ServiceHandle::new(app_spec.id(), app_node_id);
        let sys_node_id = alloc.nodes[&app_node];
        sys_spec
            .get_node(sys_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(mailbox);
    }
    log::trace!("Allocation: {:?}", alloc);
    Ok(alloc)
}

/// Service nodes are randomly assigned to compute nodes: one service per
/// compute node. Connections are randomly mapped.
pub fn alloc_random<const BUFFERING: Buffering>(
    app_specs: &[&Application],
    sys_spec: &HardwareSpec,
    alloc_type: &RandomAllocation,
) -> Result<SystemAllocation, Error> {
    let mut alloc = SystemAllocation::new();
    let mut compute_nodes = sys_spec.compute_nodes();
    let apps_by_id = app_specs
        .iter()
        .map(|app_spec| (app_spec.id(), app_spec))
        .collect::<HashMap<_, _>>();
    if let RandomAllocation::NodesOneToOne = alloc_type {
        if app_specs.len() != 1 {
            log::error!("Can not allocate multiple applications in a 1x1 setting.");
            return Err(Error::InvalidAllocation);
        }
        let app_spec = &app_specs[0];
        assert!(compute_nodes.len() >= app_spec.iter_nodes().count());
    }
    let mut rng = rand::thread_rng();
    let mut mailboxes = HashMap::<ServiceHandle, MailBox>::new();
    for app_spec in app_specs {
        // map services to compute
        for app_node_id in app_spec.iter_nodes() {
            let sys_node = match alloc_type {
                RandomAllocation::NodesOneToOne => {
                    if sys_spec.compute_nodes().len() < app_spec.iter_nodes().count() {
                        log::error!("There should be at least as many service nodes as compute nodes for the random 1x1 mapping.");
                        return Err(Error::InvalidAllocation);
                    }
                    let sys_node_idx = rng.gen_range(0..compute_nodes.len());
                    compute_nodes.swap_remove(sys_node_idx)
                }
                RandomAllocation::NodesAny => {
                    let k = rng.gen_range(0..compute_nodes.len());
                    compute_nodes[k]
                }
            };
            let app_node = ServiceHandle::new(app_spec.id(), app_node_id);
            alloc.nodes.insert(app_node.clone(), sys_node);
            alloc.compute_cycles.insert(app_node.clone(), 1);
            let mailbox = MailBox::new(app_spec, &[app_node_id]);
            mailboxes.insert(app_node.clone(), mailbox);
        }

        // map connections to paths
        for app_edge_id in app_spec.iter_links() {
            let app_edge = CommsHandle::new(app_spec.id(), app_edge_id);
            let (app_src_node_id, app_dst_node_id) = app_spec.get_link_endpoints(app_edge_id);
            let app_src_node = ServiceHandle::new(app_spec.id(), app_src_node_id);
            let src_sys_node = alloc.nodes[&app_src_node];
            let dst_sys_node = alloc.nodes[&ServiceHandle::new(app_spec.id(), app_dst_node_id)];
            let outbox = mailboxes.get_mut(&app_src_node).unwrap();
            let path = if src_sys_node == dst_sys_node {
                outbox.map_connection_src_to_self_edge(app_edge, sys_spec, src_sys_node)?;
                None
            } else {
                let path = path::random_path(sys_spec, src_sys_node, &[dst_sys_node])?
                    .ok_or(Error::InvalidPath)?;
                outbox.map_connection_src_to_gather(app_edge, sys_spec, path.source())?;
                Some(path)
            };
            alloc
                .links
                .insert(CommsHandle::new(app_spec.id(), app_edge_id), path);
        }
    }
    for (app_node, mailbox) in &mut mailboxes {
        let app_spec = apps_by_id[&app_node.app_id];
        for edge_ref in app_spec.get_input_links(app_node.service_id) {
            let app_edge = CommsHandle::new(app_node.app_id.clone(), edge_ref.id());
            match alloc.links[&app_edge].as_ref() {
                Some(path) => {
                    for sys_link_id in path.destinations() {
                        mailbox.map_connection_dst_to_scatter(
                            app_edge.clone(),
                            sys_spec,
                            sys_link_id,
                        )?;
                    }
                }
                None => mailbox.map_connection_dst_to_self_edge(
                    app_edge,
                    sys_spec,
                    alloc.nodes[&app_node],
                )?,
            }
        }
    }
    let mut app_knapsack: HashMap<NodeIndex, Vec<ServiceHandle>> = HashMap::new();
    for (app_node, sys_node_id) in alloc.nodes.iter() {
        if !app_knapsack.contains_key(&sys_node_id) {
            app_knapsack.insert(*sys_node_id, vec![app_node.clone()]);
        } else {
            app_knapsack
                .get_mut(&sys_node_id)
                .unwrap()
                .push(app_node.clone());
        }
    }
    let mut merged_mailboxes = app_knapsack
        .iter()
        .map(|(sys_node_id, app_nodes)| {
            let mut merged_mailbox = mailboxes[&app_nodes[0]].clone();
            for app_node in &app_nodes[1..] {
                merged_mailbox.merge(&mailboxes[app_node]);
            }
            (sys_node_id, merged_mailbox)
        })
        .collect::<HashMap<_, _>>();
    for (sys_node_id, mut mailbox) in merged_mailboxes.drain() {
        // Once all the incoming/outgoing/self edges of a mailbox have been mapped, addresses
        // can be materialized.
        mailbox.materialize_addresses(sys_spec)?;
        log::debug!("Mailbox of sys node {:?} {:#?}", sys_node_id, mailbox);
        sys_spec
            .get_node(*sys_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_mailbox(mailbox);
    }

    log::trace!("Allocation: {:#?}", alloc);
    Ok(alloc)
}

#[cfg(test)]
mod tests {
    use crate::scheduler::{generate_physical_system_1x1, MappingConfiguration1x1};
    use crate::specs::SystemContext;
    use crate::NodeSpec;
    use crate::*;
    fn no_action(
        _loopback: LoopbackRef,
        _input: &[InputFrameRef],
        _output: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
    }

    #[test]
    // test that the invariant that node sequences are the same for app spec
    // and system spec in a 1x1 mapping.
    fn test_node_index_seq() {
        const NODES: usize = 10;
        let mut app_spec = Application::new();
        for n in 0..NODES {
            app_spec.add_node(Service::new(
                format!("node {}", n).as_str(),
                no_action,
                None,
                FrequencyFactor(1),
            ));
        }
        // connect all to all
        for node_id in app_spec.iter_nodes() {
            for n in 0..NODES {
                if node_id.index() != n {
                    // connect port n on node_id to port node_id on node n.
                    let link = Connection::new_for_testing(n, node_id.index(), 8);
                    app_spec.link_simplex_framing(
                        node_id,
                        NodeIndex::new(n),
                        link,
                        FramingLead::Src,
                    );
                }
            }
        }

        let sys_spec = generate_physical_system_1x1(&app_spec, &MappingConfiguration1x1::default());

        for (app_node, sys_node) in app_spec.iter_nodes().zip(sys_spec.iter_nodes()) {
            // the names of the nodes identified by the same index must match!
            assert_eq!(
                app_spec.get_node(app_node).borrow().name(),
                sys_spec.get_node(sys_node).borrow().name()
            );
            assert_eq!(
                sys_spec
                    .get_node(sys_node)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .frequency(),
                MappingConfiguration1x1::default().node_frequency
            );
        }
        for link_id in sys_spec.iter_links() {
            let link = sys_spec.get_link(link_id);
            assert_eq!(
                link.into_provisioned_link().unwrap().frequency(),
                MappingConfiguration1x1::default().link_frequency
            );
            assert_eq!(
                link.latency(),
                MappingConfiguration1x1::default().link_latency
            )
        }
    }
}
