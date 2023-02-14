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

//! interface for link properties

use super::*;

pub trait LinkSpec {
    /// all links should have a constructor like this
    // fn new(src_port: Port, dst_port: Port, frame_size: usize, latency: Latency) -> dyn LinkSpec;

    /// return the pair of (src_port, dst_port)
    fn get_ports(&self) -> (Port, Port);

    /// source port
    fn src_port(&self) -> Port;

    /// destination port
    fn dst_port(&self) -> Port;

    /// frame size in bits
    ///
    /// one frame both enters and leaves the link each cycle
    fn frame_size(&self) -> usize;

    /// the time spend "on the wire" in cycles.
    ///
    /// cycles are in units of GCD(src frequency, dst frequency). the
    /// latency is the number of cycles that data spends between the input
    /// and output buffers at the ends of the link.
    ///
    /// a latency of zero implies that data can be read on the next
    /// GCD-based cycle immediately after being written; as the GCD of node
    /// frequencies, which are relative factors to the system root, this is
    /// similarly a factor relative to the root frequency
    fn latency(&self) -> Latency;

    /// Set the latency of the link (i.e., any buffering delay).
    fn set_latency(&mut self, latency: Latency);

    // TODO(cascaval): why are we not stepping links (just like nodes)?
    // Allegedly we need to support links with zero latency, so we have the
    // nodes driving the links. For hw, we actually step the links as part
    // of the compute node cycle by calling scatter/gather on the links. In
    // the case of the application level simulation, we call
    // get_next_src/dst_frames as part of the SystemSimulation. It's worth
    // considering whether we can fold that functionality into the link
    // spec, just as we do for nodes.

    fn into_provisioned_link(&self) -> Option<&dyn ProvisionedLink> {
        None
    }

    fn into_mut_provisioned_link(&mut self) -> Option<&mut dyn ProvisionedLink> {
        None
    }
}

pub trait ProvisionedLink {
    fn frequency(&self) -> Frequency;
    fn set_frequency(&mut self, freq: Frequency);
}

/// Trait for links that don't support the framing semantics; this is used as a negative trait constraint.
pub trait NonFramingLinkTrait {}

/// Legacy attributes of SW links no longer used by the HW simulator. To be deprecated.
pub trait FramingLinkTrait {
    /// set the link parameters
    ///
    /// this is separate from the constructor, because we need to create a
    /// link object that implements LinkSpec, and we compute the parameters
    /// when the link is bound using link_simplex.
    /// Alternatively, we could pass all the parameters to link_simplex.
    fn set_framing(
        &mut self,
        framing_lead: FramingLead,
        lead_framing: FrequencyFactor,
        follower_framing: FrequencyFactor,
    );

    /// the lead side processes one frame per cycle, thus setting the link bandwidth
    /// (frame_size * frequency of that side)
    fn framing_lead(&self) -> FramingLead;

    /// batching represents how links process frames to accommodate nodes
    /// with different frequencies.
    ///
    /// the lead side processes one single frame per local cycle; the
    /// follower side processes a batch of follower_batch_size frames and
    /// changes that batch every follower_batch_cycles local cycles
    fn follower_batch_size(&self) -> usize;
    fn follower_batch_cycles(&self) -> usize;
}
