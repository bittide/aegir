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
use crate::calendar::Buffering;
use crate::specs::GraphId;
use crate::{app::Application, HardwareSpecType, NodeSpec};
use crate::{Error, LinkSpec};
use crate::{HardwareSpec, Port};
use itertools::Itertools;
use petgraph::prelude::*;
use std::collections::HashMap;
use std::iter::FromIterator;

#[derive(Clone, Debug)]
pub struct MappedAttrs {
    /// The base address of the memory region for the mailbox.
    pub base_address: Option<usize>,

    /// The endpoint's frame size in number of bits.
    pub frame_size: usize,

    /// The endpoint's memory size in number of frames.
    pub memory_size: usize,

    /// The corresponding HW IO index.
    pub hw_io_index: Option<usize>,
}

#[derive(Clone, Debug)]
pub struct ConnectionAttrs {
    /// The connection edge which defined this mailbox.
    pub connection_id: CommsHandle,

    /// The message size in number of bits.
    pub message_size: usize,

    /// The io index on the service node.
    pub service_io_index: usize,

    /// Service name.
    pub service_name: String,

    /// Attributes for the mailbox owned endpoint of the connection, i.e., if
    /// these attributes are for an inbox, then the mapped attributes are for
    /// the corresponding scatter. (Similarly, the attributes are for the
    /// corresponding gather if this is an outbox.)
    pub mapped_endpoint: Option<MappedAttrs>,
}

#[derive(Clone, Debug)]
pub struct MailBox {
    /// Inboxes managed by the mailbox.
    pub inboxes: Vec<ConnectionAttrs>,

    /// Outboxes managed by the mailbox.
    pub outboxes: Vec<ConnectionAttrs>,
}

impl MailBox {
    pub fn new(app_spec: &Application, app_node_ids: &[NodeIndex]) -> Self {
        let outboxes = app_node_ids
            .iter()
            .map(|app_node_id| {
                let service_name = app_spec.get_node(*app_node_id).borrow().name().to_string();
                app_spec
                    .get_output_links(*app_node_id)
                    .map(move |edge_ref| ConnectionAttrs {
                        connection_id: CommsHandle::new(app_spec.id(), edge_ref.id()),
                        message_size: app_spec.get_link(edge_ref.id()).frame_size(),
                        service_io_index: edge_ref.weight().src_port().into(),
                        mapped_endpoint: None,
                        service_name: service_name.clone(),
                    })
            })
            .flatten()
            .collect::<Vec<_>>();
        let inboxes = app_node_ids
            .iter()
            .map(|app_node_id| {
                let service_name = app_spec.get_node(*app_node_id).borrow().name().to_string();
                app_spec
                    .get_input_links(*app_node_id)
                    .map(move |edge_ref| ConnectionAttrs {
                        connection_id: CommsHandle::new(app_spec.id(), edge_ref.id()),
                        message_size: app_spec.get_link(edge_ref.id()).frame_size(),
                        service_io_index: edge_ref.weight().dst_port().into(),
                        mapped_endpoint: None,
                        service_name: service_name.clone(),
                    })
            })
            .flatten()
            .collect::<Vec<_>>();
        Self {
            inboxes: inboxes,
            outboxes: outboxes,
        }
    }

    /// Materialize addresses for the mailbox. This function assigns an address
    /// to every box for their respective gather/scatter memories.
    pub fn materialize_addresses<const BUFFERING: Buffering>(
        &mut self,
        _sys_spec: &HardwareSpecType<BUFFERING>,
    ) -> Result<(), Error> {
        if !self
            .inboxes
            .iter()
            .chain(self.outboxes.iter())
            .all(|b| b.mapped_endpoint.is_some())
        {
            log::error!("A mailbox can only be materialized if all the boxes have mappings, which requires a complete allocation.");
            return Result::Err(Error::InvalidAllocation);
        }
        // Assigns address to mailbox and returns the next available address.
        fn assign_address(address: usize, mailbox: &mut ConnectionAttrs) -> Result<usize, Error> {
            let mapped_endpoint = mailbox.mapped_endpoint.as_mut().unwrap();
            mapped_endpoint.base_address = Some(address);
            // Now compute the next address
            let msg_frame_count = mailbox.message_size / mapped_endpoint.frame_size
                + usize::from(mailbox.message_size % mapped_endpoint.frame_size != 0);
            if address + msg_frame_count - 1 > mapped_endpoint.memory_size {
                log::error!("The mapped endpoint's memory isn't large enough to materialize all assigned mailboxes. (address: {} msg frame count: {}, memory size: {})", address, msg_frame_count, mapped_endpoint.memory_size);
                return Err(Error::InvalidAllocation);
            }
            Ok(address + msg_frame_count)
        }
        fn assign_io_addresses(
            next_address: &mut HashMap<usize, usize>,
            boxes: Vec<&mut ConnectionAttrs>,
        ) -> Result<(), Error> {
            for mailbox in boxes {
                let mapped_endpoint = mailbox.mapped_endpoint.as_mut().unwrap();
                let hw_io_index = mapped_endpoint.hw_io_index.unwrap();
                let address = next_address[&hw_io_index];
                *next_address.get_mut(&hw_io_index).unwrap() = assign_address(address, mailbox)?;
            }
            Ok(())
        }
        // assign input/output addresses
        for mailboxes in [&mut self.inboxes, &mut self.outboxes] {
            let mut next_address =
                HashMap::<usize, usize>::from_iter(mailboxes.iter().filter_map(|mailbox| {
                    mailbox
                        .mapped_endpoint
                        .as_ref()
                        .unwrap()
                        .hw_io_index
                        .map(|idx| (idx, 0))
                }));
            let io_mailboxes = mailboxes
                .iter_mut()
                .filter(|inbox| {
                    inbox
                        .mapped_endpoint
                        .as_ref()
                        .unwrap()
                        .hw_io_index
                        .is_some()
                })
                .collect::<Vec<_>>();
            assign_io_addresses(&mut next_address, io_mailboxes)?;
        }

        // Host mailbox (self-edge) addresses
        let mut next_address = 0;
        for outbox in self.outboxes.iter_mut().filter(|outbox| {
            outbox
                .mapped_endpoint
                .as_ref()
                .unwrap()
                .hw_io_index
                .is_none()
        }) {
            next_address = assign_address(next_address, outbox)?;
        }
        for inbox in self.inboxes.iter_mut().filter(|inbox| {
            inbox
                .mapped_endpoint
                .as_ref()
                .unwrap()
                .hw_io_index
                .is_none()
        }) {
            self.outboxes
                .iter()
                .find(|outbox| outbox.connection_id == inbox.connection_id)
                .map_or_else(
                    || {
                        log::error!("Couldn't find corresponding self-edge outbox.");
                        Err(Error::InvalidAllocation)
                    },
                    |outbox| {
                        inbox.mapped_endpoint.as_mut().unwrap().base_address = Some(
                            outbox
                                .mapped_endpoint
                                .as_ref()
                                .unwrap()
                                .base_address
                                .unwrap(),
                        );
                        Ok(())
                    },
                )?;
        }
        Ok(())
    }

    /// Returns the mailbox for the given service name. The inboxes and
    /// outboxes are in the same order as the corresponding service function's
    /// IO.
    pub fn get_app_mailboxes(&self, app_id: GraphId, service_node_name: &str) -> Option<Self> {
        let app_inboxes = self
            .inboxes
            .iter()
            .filter(|attrs| {
                attrs.connection_id.app_id == app_id && attrs.service_name == service_node_name
            })
            .sorted_by(|x, y| Ord::cmp(&x.service_io_index, &y.service_io_index))
            .cloned()
            .collect::<Vec<_>>();
        let app_outboxes = self
            .outboxes
            .iter()
            .filter(|attrs| {
                attrs.connection_id.app_id == app_id && attrs.service_name == service_node_name
            })
            .sorted_by(|x, y| Ord::cmp(&x.service_io_index, &y.service_io_index))
            .cloned()
            .collect::<Vec<_>>();
        if app_inboxes.len() == 0 && app_outboxes.len() == 0 {
            None
        } else {
            Some(Self {
                inboxes: app_inboxes,
                outboxes: app_outboxes,
            })
        }
    }

    pub fn get_src_port_outboxes(&self, hw_io_index: usize) -> Vec<ConnectionAttrs> {
        self.outboxes
            .iter()
            .filter(|attrs| {
                attrs.mapped_endpoint.as_ref().unwrap().hw_io_index == Some(hw_io_index)
            })
            .cloned()
            .collect::<Vec<_>>()
    }

    pub fn get_dst_port_inboxes(&self, hw_io_index: usize) -> Vec<ConnectionAttrs> {
        self.inboxes
            .iter()
            .filter(|attrs| {
                attrs.mapped_endpoint.as_ref().unwrap().hw_io_index == Some(hw_io_index)
            })
            .cloned()
            .collect::<Vec<_>>()
    }

    /// Associates the service connection's source and destination to a self-edge.
    pub fn map_connection_src_to_self_edge(
        &mut self,
        app_edge: CommsHandle,
        sys_spec: &HardwareSpec,
        node_id: NodeIndex,
    ) -> Result<(), Error> {
        let word_size = sys_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_compute_node()
            .unwrap()
            .get_host_memory_cfg()
            .word_size();
        let memory_size = sys_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_compute_node()
            .unwrap()
            .get_host_memory_cfg()
            .out_mailbox()
            .size();
        self.outboxes
            .iter_mut()
            .find(|attrs| attrs.connection_id == app_edge)
            .map(|outbox| {
                outbox.mapped_endpoint = Some(MappedAttrs {
                    base_address: None,
                    hw_io_index: None,
                    frame_size: word_size,
                    memory_size,
                })
            })
            .ok_or_else(|| {
                log::error!(
                    "Couldn't find the associated outbox for application link {:?}",
                    app_edge
                );
                Error::InvalidAllocation
            })?;
        Ok(())
    }

    /// Associates the service connection's destination to a self-edge.
    pub fn map_connection_dst_to_self_edge(
        &mut self,
        app_edge: CommsHandle,
        sys_spec: &HardwareSpec,
        node_id: NodeIndex,
    ) -> Result<(), Error> {
        let frame_size = sys_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_compute_node()
            .unwrap()
            .get_host_memory_cfg()
            .word_size();
        let memory_size = sys_spec
            .get_node(node_id)
            .borrow()
            .into_provisioned_compute_node()
            .unwrap()
            .get_host_memory_cfg()
            .in_mailbox()
            .size();
        self.inboxes
            .iter_mut()
            .find(|attrs| attrs.connection_id == app_edge)
            .map(|inbox| {
                inbox.mapped_endpoint = Some(MappedAttrs {
                    base_address: None,
                    hw_io_index: None,
                    frame_size,
                    memory_size,
                })
            })
            .ok_or_else(|| {
                log::error!(
                    "Couldn't find the associated inbox for the application link {:?}",
                    app_edge
                );
                Error::InvalidAllocation
            })?;
        Ok(())
    }

    /// Associates the service connection's source to the gather of the
    /// corresponding compute node.
    pub fn map_connection_src_to_gather<const BUFFERING: Buffering>(
        &mut self,
        app_edge: CommsHandle,
        sys_spec: &HardwareSpecType<BUFFERING>,
        sys_link_id: EdgeIndex,
    ) -> Result<(), Error> {
        if let Some(attrs) = self
            .outboxes
            .iter_mut()
            .find(|attrs| attrs.connection_id == app_edge)
        {
            let hw_io_index: usize = sys_spec.get_link(sys_link_id).src_port().into();
            attrs.mapped_endpoint = Some(MappedAttrs {
                base_address: None,
                hw_io_index: Some(hw_io_index),
                frame_size: sys_spec.get_link(sys_link_id).frame_size(),
                memory_size: sys_spec
                    .get_node(sys_spec.get_link_endpoints(sys_link_id).0)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .get_gather_memory_size(Port::new_out(hw_io_index)),
            });
            Ok(())
        } else {
            Result::Err(Error::InvalidAllocation)
        }
    }

    /// Associates the service connection's destination to the scatter of the
    /// corresponding compute node.
    pub fn map_connection_dst_to_scatter<const BUFFERING: Buffering>(
        &mut self,
        app_edge: CommsHandle,
        sys_spec: &HardwareSpecType<BUFFERING>,
        sys_link_id: EdgeIndex,
    ) -> Result<(), Error> {
        if let Some(attrs) = self
            .inboxes
            .iter_mut()
            .find(|attrs| attrs.connection_id == app_edge)
        {
            let hw_io_index: usize = sys_spec.get_link(sys_link_id).dst_port().into();
            attrs.mapped_endpoint = Some(MappedAttrs {
                base_address: None,
                hw_io_index: Some(hw_io_index),
                frame_size: sys_spec.get_link(sys_link_id).frame_size(),
                memory_size: sys_spec
                    .get_node(sys_spec.get_link_endpoints(sys_link_id).1)
                    .borrow()
                    .into_provisioned_node()
                    .unwrap()
                    .get_scatter_memory_size(Port::new_in(hw_io_index)),
            });
            Ok(())
        } else {
            Result::Err(Error::InvalidAllocation)
        }
    }

    pub fn merge(&mut self, other: &MailBox) {
        self.inboxes.extend_from_slice(other.inboxes.as_slice());
        self.outboxes.extend_from_slice(other.outboxes.as_slice());
    }
}

#[cfg(test)]
mod mailbox_tests {}
