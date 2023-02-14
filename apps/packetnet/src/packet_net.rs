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

use std::convert::TryInto;
use std::fmt;
use std::mem;

use bits_derive::*;

use crate::logging::*;

/// Newtype representing an application cycle.
#[derive(Bits, Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Cycle(pub u64);

impl fmt::Display for Cycle {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Debug for Cycle {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Clone, Copy, Bits)]
pub struct GridSize {
    pub(crate) rows: u32,
    pub(crate) cols: u32,
}

#[derive(Clone, Copy, Eq, PartialEq, Hash, Bits)]
pub struct PacketNetAddress {
    pub(crate) row: u32,
    pub(crate) col: u32,
}

impl PacketNetAddress {
    pub fn row(self) -> u32 {
        self.row
    }
    pub fn col(self) -> u32 {
        self.col
    }
}

impl fmt::Display for PacketNetAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{},{}", self.row, self.col)
    }
}

impl fmt::Debug for PacketNetAddress {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{},{}", self.row, self.col)
    }
}

/// A message we send over bittide links --- an application message plus some networking metadata.
///
/// Ideally this would not be exposed to applications and would be pub(crate) or private.
/// Currently it has to be, because there is no way to declare application nodes without naming
/// the types of messages that will be passed over all links.
#[derive(Bits)]
pub struct PacketNetMessage<T> {
    /// Useful for logging to track packet movement across the network.
    source: PacketNetAddress,
    /// Useful for logging to track packet movement across the network.
    source_cycle: Cycle,
    destination: PacketNetAddress,
    payload: T,
}

/// The per-application-node state of the packet network driver.
#[derive(Bits)]
pub struct PacketNetState<T, const QUEUE_MAX: usize> {
    self_address: PacketNetAddress,
    /// We need the grid size to compute shortest paths that wrap around the edges of the grid.
    grid_size: GridSize,
    /// Messages we need to send.
    queue: [Option<PacketNetMessage<T>>; QUEUE_MAX],
    /// Current cycle number.
    cycle: Cycle,
    /// Handle to shared logging object.
    logging: PacketNetLogHandle,
}

impl<T, const QUEUE_MAX: usize> PacketNetState<T, QUEUE_MAX> {
    /// Create a new driver state for an application node.
    pub fn new(
        self_address: PacketNetAddress,
        grid_size: GridSize,
        logging: PacketNetLogHandle,
    ) -> PacketNetState<T, QUEUE_MAX> {
        let queue = (0..QUEUE_MAX)
            .map(|_| None)
            .collect::<Vec<Option<PacketNetMessage<T>>>>();
        let Ok(queue) = queue.try_into() else {
            panic!("Length mismatch can't happen!");
        };
        PacketNetState {
            self_address,
            grid_size,
            queue,
            cycle: Cycle(0),
            logging,
        }
    }
    pub fn grid_size(&self) -> GridSize {
        self.grid_size
    }
    /// Call this at the start of an application action function, passing in the messages received
    /// along incoming links. Processes the incoming messages and returns a PacketInterface
    /// representing the interface to the packet network which can be used during the application
    /// action function, to read the received application payloads and send messages.
    pub fn receive<'a>(
        &'a mut self,
        inputs: Vec<Option<PacketNetMessage<T>>>,
    ) -> PacketInterface<'a, T, QUEUE_MAX> {
        let mut queue = Vec::new();
        let mut received = Vec::new();
        let self_address = self.self_address;
        let cycle = self.cycle;
        let logging = self.logging;
        let mut handle_packet = |packet: PacketNetMessage<T>| {
            if packet.destination == self_address {
                logging.log(PacketNetLog::MessageReceived {
                    from: packet.source,
                    from_cycle: packet.source_cycle,
                    to: packet.destination,
                    to_cycle: cycle,
                });
                received.push(packet.payload);
            } else {
                queue.push(packet);
            }
        };
        for queued in self.queue.iter_mut() {
            if let Some(packet) = queued.take() {
                // We need to call handle_packet in case this node sent a packet to itself
                // last cycle.
                handle_packet(packet);
            } else {
                // No more packets after the first None entry in the queue.
                break;
            }
        }
        for input in inputs {
            if let Some(packet) = input {
                handle_packet(packet);
            }
        }
        PacketInterface {
            state: self,
            received,
            queue,
        }
    }
}

/// Link index of the "North" link.
pub(crate) const NORTH: usize = 0;
/// Link index of the "East" link.
pub(crate) const EAST: usize = 1;
/// Link index of the "South" link.
pub(crate) const SOUTH: usize = 2;
/// Link index of the "West" link.
pub(crate) const WEST: usize = 3;

/// The interface to the packet network driver during an application action function.
#[derive(Bits)]
pub struct PacketInterface<'a, T, const QUEUE_MAX: usize> {
    state: &'a mut PacketNetState<T, QUEUE_MAX>,
    received: Vec<T>,
    /// During the application action function we store our message queue here. This lets us
    /// temporarily exceed the maximum queue length that we're storing in the application node.
    queue: Vec<PacketNetMessage<T>>,
}

fn closest_direction(
    from: u32,
    to: u32,
    size: u32,
    increasing_direction: usize,
    decreasing_direction: usize,
) -> usize {
    assert_ne!(from, to);
    assert!(from < size);
    assert!(to < size);
    let increasing_distance = if from < to {
        to - from
    } else {
        to + size - from
    };
    let decreasing_distance = if from > to {
        from - to
    } else {
        from + size - to
    };
    if increasing_distance <= decreasing_distance {
        increasing_direction
    } else {
        decreasing_direction
    }
}

impl<'a, T, const QUEUE_MAX: usize> PacketInterface<'a, T, QUEUE_MAX> {
    pub fn cycle(&self) -> Cycle {
        self.state.cycle
    }
    pub fn grid_size(&self) -> GridSize {
        self.state.grid_size
    }
    /// Retrieve the application messages. Can only be called once (per application cycle).
    pub fn received(&mut self) -> Vec<T> {
        mem::replace(&mut self.received, Vec::new())
    }
    pub fn self_address(&self) -> PacketNetAddress {
        self.state.self_address
    }
    /// Send a message.
    /// Sending to self is allowed; the message will arrive in the next application cycle.
    /// Messages to the same destination follow the same path and are received in the order
    /// they were sent.
    /// Messages can be dropped due to queue overruns but not otherwise.
    pub fn send(&mut self, payload: T, destination: PacketNetAddress) {
        self.state.logging.log(PacketNetLog::MessageSent {
            from: self.self_address(),
            from_cycle: self.cycle(),
            to: destination,
        });
        self.queue.push(PacketNetMessage {
            source: self.self_address(),
            source_cycle: self.cycle(),
            destination,
            payload,
        });
    }
    /// Call this at the end of the application action function. Returns the messages that should
    /// be sent over the links.
    pub fn transmit(mut self) -> [Option<PacketNetMessage<T>>; 4] {
        let mut new_queue = Vec::new();
        let self_address = self.self_address();
        let mut outputs = [None, None, None, None];
        let logging = self.state.logging;
        let cycle = self.cycle();
        for packet in self.queue.drain(..) {
            // Implement Y-first routing.
            let link_index;
            if packet.destination.row == self_address.row {
                if packet.destination.col == self_address.col {
                    // Nowhere to forward it; just put it in the queue to be received next cycle.
                    new_queue.push(packet);
                    continue;
                }
                link_index = closest_direction(
                    self_address.col,
                    packet.destination.col,
                    self.state.grid_size.cols,
                    EAST,
                    WEST,
                );
            } else {
                link_index = closest_direction(
                    self_address.row,
                    packet.destination.row,
                    self.state.grid_size.rows,
                    SOUTH,
                    NORTH,
                );
            }
            if outputs[link_index].is_some() {
                // Link already busy, queue the packet for later transmission.
                new_queue.push(packet);
            } else {
                logging.log(PacketNetLog::MessageForwarded {
                    from: packet.source,
                    from_cycle: packet.source_cycle,
                    to: packet.destination,
                    at: self_address,
                    at_cycle: cycle,
                    direction: link_index as u8,
                });
                outputs[link_index] = Some(packet);
            }
        }
        if new_queue.len() > QUEUE_MAX {
            for packet in new_queue.drain(QUEUE_MAX..) {
                logging.log(PacketNetLog::MessageDropped {
                    from: packet.source,
                    from_cycle: packet.source_cycle,
                    to: packet.destination,
                    at: self_address,
                    at_cycle: cycle,
                });
            }
        }
        for (index, packet) in new_queue.into_iter().enumerate() {
            self.state.queue[index] = Some(packet);
        }
        self.state.cycle.0 += 1;
        outputs
    }
}
