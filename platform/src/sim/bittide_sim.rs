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

use std::rc::Rc;

use crate::app::ServiceHandle;
use crate::calendar::CalendarVariant;
use crate::calendar::IOCalendarVariant;
use crate::calendar::BUFFERING_DOUBLE;
use crate::scheduler::AllocateTrait;
use crate::scheduler::ScheduleTrait;
use crate::scheduler::*;
use crate::sim::FailureProperties;
use crate::sim::HardwareSystemSimulation;
use crate::sim::SoftwareSystemSimulation;
use crate::sim::SystemSimulationTrait;
use crate::specs::NodeSpec;
use crate::specs::ProvisionedNode;
use crate::vcd::VcdWriter;
use crate::Buffering;
use crate::{Application, Cycle, Error, HardwareSpec};

use super::OptionSimCallbacks;

/// A type to allow us to define a function to inspect the state of the
/// simulation, and the application at each cycle.
///
/// The arguments are:
///    - current simulation cycle.
///    - a reference to the system simulation, enabling access to the system spec nodes.
///    - a reference to the app spec, enabling access to the state of the application.
///
/// Caveat: as this is a function, we do not have access inside the body to
/// any of the variables that we used to define the system.
pub type InspectSoftwareSimulation = fn(Cycle, &SoftwareSystemSimulation, &Application);

/// A type to allow us to define a function to inspect the state of the
/// simulation, and the application at each cycle.
///
/// The arguments are:
///    - current metacycle.
///    - current simulation cycle within the metacycle.
///    - a reference to the system simulation, enabling access to the system spec nodes.
///    - a reference to the app spec, enabling access to the state of the application.
///    - a reference to the hardware spec, enabling access to nodes in the system under simulation.
///
/// Caveat: as this is a function, we do not have access inside the body to
/// any of the variables that we used to define the system.
pub type InspectHardwareSimulation<const BUFFERING: Buffering> =
    fn(Cycle, Cycle, &HardwareSystemSimulation<BUFFERING>, &Application, &HardwareSpec);

pub enum InspectType<const BUFFERING: Buffering> {
    SW(InspectSoftwareSimulation),
    HW(InspectHardwareSimulation<BUFFERING>),
}

pub type Inspect = InspectType<{ BUFFERING_DOUBLE }>;

/// simulate a bittide system
///
/// Args:
///   - system_spec: the system specification. Will construct a machine that is isomorphic to it.
///   - app_spec: the suite of applications to run; mutated through the reference in system spec.
///   - policy: bittide allocation policy to use for mapping this application
///   - cycles: number of metacycles to run the simulation
///   - cycles_per_metacycle: boottime value
pub fn simulate_bittide(
    system_spec: &HardwareSpec,
    app_specs: &[&Application],
    policy: AllocationPolicy,
    inspect_fn: Option<Inspect>,
    metacycles: usize,
    callbacks: OptionSimCallbacks,
    properties: FailureProperties,
) -> Result<(), Error> {
    let alloc = system_spec.allocate(app_specs, &policy)?;
    let sched = system_spec.schedule(app_specs, &policy, &alloc)?;

    // set the calendars and node functions according to the schedule.
    for app_spec in app_specs {
        for n in app_spec.iter_nodes() {
            let sys_node_id = alloc
                .nodes
                .get(&ServiceHandle::new(app_spec.id(), n))
                .unwrap();
            let sys_node = system_spec.get_node(*sys_node_id);

            sys_node.borrow_mut().register_app(
                ServiceHandle::new(app_spec.id(), n),
                Rc::clone(&app_spec.get_node(n)),
            );
        }
    }
    for (switch_node_id, calendar) in &sched.switch_schedules {
        log::trace!(
            "Setting switch {:?} calendar {:#?}",
            switch_node_id,
            calendar
        );
        system_spec
            .get_node(*switch_node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_calendar(CalendarVariant::<BUFFERING_DOUBLE>::Crossbar(
                calendar.clone(),
            ));
    }
    for (node_id, node_calendar) in &sched.node_schedules {
        log::trace!(
            "Setting compute node {:?} calendars {:#?}",
            node_id,
            node_calendar
        );
        system_spec
            .get_node(*node_id)
            .borrow_mut()
            .into_mut_provisioned_node()
            .unwrap()
            .set_calendar(CalendarVariant::<BUFFERING_DOUBLE>::Node(
                node_calendar.clone(),
            ));
    }
    for sys_link_id in system_spec.iter_links() {
        let sys_link = system_spec.get_link(sys_link_id);
        let (sys_src_node, sys_dst_node) = system_spec.get_link_endpoints(sys_link_id);
        // get the hardware nodes
        let hw_src_node = system_spec.get_node(sys_src_node);
        let hw_dst_node = system_spec.get_node(sys_dst_node);
        let (src_port, dst_port) = sys_link.get_ports();
        if let Some(link_calendars) = sched.link_schedules.get(&sys_link_id) {
            let [(tx_cal0, rx_cal0), (tx_cal1, rx_cal1)] = link_calendars;
            let tx_cal = [tx_cal0.clone(), tx_cal1.clone()];
            let rx_cal = [rx_cal0.clone(), rx_cal1.clone()];
            log::trace!(
                "Setting calendars for nodes {} => {}, link {}, ports {} -> {}\ntx_cal: {:#?}\nrx_cal: {:#?}",
                sys_src_node.index(),
                sys_dst_node.index(),
                sys_link_id.index(),
                src_port,
                dst_port,
                tx_cal,
                rx_cal,
            );
            hw_src_node
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_io_calendar(IOCalendarVariant::Output(tx_cal), src_port);
            hw_dst_node
                .borrow_mut()
                .into_mut_provisioned_node()
                .unwrap()
                .set_io_calendar(IOCalendarVariant::Input(rx_cal), dst_port);
        } else {
            return Err(Error::InvalidSchedule);
        }
    }

    callbacks.vcd(|writer| VcdWriter::write_header(writer, &system_spec));
    let mut simulation = HardwareSystemSimulation::new(system_spec, properties);
    let sim_cpm = simulation.sim_cycles_per_metacycle(system_spec);
    for metacycle in 0..metacycles {
        for cycle in 0..sim_cpm[metacycle % sim_cpm.len()] {
            log::debug!("metacycle {} cycle {}", metacycle, cycle);
            simulation.simulate_system_one_cycle(system_spec, callbacks);
            // allow the caller to inspect the state of the simulation
            if let Some(Inspect::HW(inspect)) = inspect_fn {
                for app_spec in app_specs {
                    (inspect)(metacycle, cycle, &simulation, &app_spec, &system_spec);
                }
            }
        }
    }
    Ok(())
}

pub fn generate_system_spec(
    app_spec: &Application,
    allocation_policy: &AllocationPolicy,
) -> HardwareSpec {
    match allocation_policy {
        AllocationPolicy::OneToOne(ref mapping_cfg) => {
            generate_physical_system_1x1(app_spec, &mapping_cfg)
        }
        &AllocationPolicy::OneToOneNetwork(ref mapping_cfg) => {
            generate_physical_system_1x1_network(app_spec, mapping_cfg)
        }
        _ => unimplemented!("Allocation policy currently unimplemented."),
    }
}

// simulate an app
//
// Implement the 1:1 mapping of apps to bittide, so we generate a physical
// system that matches the needs of the application.
pub fn simulate_bittide_app(
    app_spec: &Application,
    inspect_fn: Option<Inspect>,
    cycles: usize,
    allocation_policy: AllocationPolicy,
    callbacks: OptionSimCallbacks,
    properties: FailureProperties,
) -> Result<(), Error> {
    let system_spec = generate_system_spec(app_spec, &allocation_policy);
    log::debug!("sys spec:\n{}", system_spec);
    simulate_bittide(
        &system_spec,
        &[app_spec],
        allocation_policy.clone(),
        inspect_fn,
        cycles,
        callbacks,
        properties,
    )?;
    callbacks.vcd(|writer| writer.borrow_mut().flush_after_simulation());
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sim::SystemSimulationCallbacks;
    use crate::specs::{ApplicationNode, SystemContext};
    use crate::*;
    use bits::Bits;

    fn source_fn(
        maybe_loopback: LoopbackRef,
        _input: &[InputFrameRef],
        output: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let mut loopback = maybe_loopback.unwrap();
        let counter: u64 = <u64 as Bits>::unpack(&loopback.as_bitslice());
        let n_outputs: u64 = output.len() as u64;
        for (port, out) in output.iter_mut().enumerate() {
            // send a different data value on each link.
            let val: u64 = n_outputs * counter + port as u64;
            println!("port {}: value written {}", port, val);
            val.pack_to(&mut out.data);
            out.valid = true;
        }
        (counter + 1).pack_to(&mut loopback);
    }

    fn sink_fn(
        maybe_loopback: LoopbackRef,
        maybe_inputs: &[InputFrameRef],
        _output: &mut [OutputFrameRef],
        _sys: &dyn SystemContext,
    ) {
        let mut loopback = maybe_loopback.unwrap();
        //println!("sink input {:?}", maybe_input);
        for (port, inp) in maybe_inputs.iter().flatten().enumerate() {
            let input_val = <u64 as Bits>::unpack(&inp.as_bitslice());
            println!("port {}: value read {}", port, input_val);
            input_val.pack_to(&mut loopback);
        }
    }

    #[test]
    fn test_single_link() {
        let _logger = env_logger::builder().is_test(true).try_init();

        let mut app_spec = Application::new();
        const FRAME_SIZE: usize = 64;

        let source = app_spec.add_node(Service::new(
            "source",
            source_fn,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let sink = app_spec.add_node(Service::new(
            "sink",
            sink_fn,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let link = Connection::new_for_testing(0, 0, FRAME_SIZE);
        // The app-spec needs to specify message sizes on port properties of the Application.
        app_spec
            .get_node(source)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[(
                PortLabel::Number(1),
                PortProperties {
                    frame_size: crate::FrameSize::Number(FRAME_SIZE),
                    direction: Direction::Outgoing,
                    ..Default::default()
                },
            )]);
        app_spec
            .get_node(sink)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[(
                PortLabel::Number(0),
                PortProperties {
                    frame_size: crate::FrameSize::Number(FRAME_SIZE),
                    direction: Direction::Incoming,
                    ..Default::default()
                },
            )]);
        app_spec.link_simplex_framing(source, sink, link, FramingLead::Src);
        log::debug!("app spec:\n{}", app_spec);
        let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1::default());
        let system_spec = generate_system_spec(&app_spec, &allocation_policy);
        simulate_bittide(
            &system_spec,
            &[&app_spec],
            allocation_policy,
            None,
            10,
            &mut sim::SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .expect("Failed simulation");
        // TODO(cascaval): implement validation
    }

    #[test]
    fn test_criss_cross_links() {
        let _logger = env_logger::builder().is_test(true).try_init();
        let mut app_spec = Application::new();
        const FRAME_SIZE: usize = 64;

        let source = app_spec.add_node(Service::new(
            "source",
            source_fn,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let sink = app_spec.add_node(Service::new(
            "sink",
            sink_fn,
            Some(u64::pack(&0).into_boxed_bitslice()),
            FrequencyFactor(1),
        ));
        let link1 = Connection::new_for_testing(0, 1, FRAME_SIZE);
        app_spec.link_simplex_framing(source, sink, link1, FramingLead::Src);
        let link2 = Connection::new_for_testing(1, 0, FRAME_SIZE);
        app_spec.link_simplex_framing(source, sink, link2, FramingLead::Src);
        // The app-spec needs to specify message sizes on port properties of the Application.
        app_spec
            .get_node(source)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
            ]);
        app_spec
            .get_node(sink)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
            ]);
        log::debug!("app spec:\n{}", app_spec);
        let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1::default());
        let system_spec = generate_system_spec(&app_spec, &allocation_policy);
        simulate_bittide(
            &system_spec,
            &[&app_spec],
            allocation_policy,
            None,
            10,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .expect("Failed simulation");
        // TODO(cascaval): implement validation
    }
}
