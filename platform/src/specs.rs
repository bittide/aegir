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

//! TOOD(cascaval): add module comments

use bitvec::prelude::*;

use crate::{Error, Port};

mod link;
pub use link::LinkSpec;
pub use link::{FramingLinkTrait, NonFramingLinkTrait};
mod node;
pub use link::ProvisionedLink;
pub use node::ApplicationNode;
pub use node::LinkStatus;
pub use node::NodeSpec;
pub use node::ProvisionedComputeNode;
pub use node::ProvisionedNode;
pub use node::ProvisionedSwitchNode;
pub use node::StatefulNode;
mod system;
pub use system::GraphId;
pub(crate) use system::SystemSpec;
mod visitor;
pub(crate) use visitor::MetacycleVisitor;

#[derive(Clone, Debug, PartialEq)]
pub struct LinkProperties {
    pub status: LinkStatus,
    // TODO: Consider adding these fields to the data exposed:
    //   * sender node name?
    //   * receiver node name?
    //   * input field name?
    //   * input port index?
    //   * output field name?
    //   * output port index?
    //   * status of the hops this path transits?
}

/// Details status of the system, i.e. whether each input/output links
/// are up/down, etc. Note this is based on information available
/// at the service node/action function only, so it doesn't give an overview
/// of the entire cluster.
pub trait SystemContext {
    /// Returns a vector of the properties of the input links arriving
    /// at this node.
    fn input_links(&self) -> Vec<LinkProperties>;

    /// Returns a vector of the properties of the output links sending
    /// data out of this node.
    fn output_links(&self) -> Vec<LinkProperties>;
}

/// An implementation of SystemContext, where the behavior can be specified.
/// Useful for tests.
pub struct MockSystemContext {
    input_links: Vec<LinkProperties>,
    output_links: Vec<LinkProperties>,
}

impl MockSystemContext {
    pub fn new(input_links: Vec<LinkProperties>, output_links: Vec<LinkProperties>) -> Self {
        Self {
            input_links,
            output_links,
        }
    }
}

impl SystemContext for MockSystemContext {
    fn input_links(&self) -> Vec<LinkProperties> {
        self.input_links.clone()
    }
    fn output_links(&self) -> Vec<LinkProperties> {
        self.output_links.clone()
    }
}

/// actions in a bittide system are functions from inputs to outputs (pure unless they reference
/// optional persistent_state); after booting the containing system, the action is evaluated
/// repeatedly at a specified frequency until the system is terminated
///
/// fixed size frames of data must be read/written from/to each action input/output during each
/// cycle; the size of each element in the input/output arrays is fixed across time, but different
/// elements may be different sizes (to accomodate differing input/output types)
pub type Action = fn(LoopbackRef, &[InputFrameRef], &mut [OutputFrameRef], &dyn SystemContext);

// OPINION(tammo): the data exchanged within our Rust simulation of a
// bittide system is explicitly untyped; the primary reason for this is that
// Rust does not readily support heterogeneous slices types; in this
// implementation the system specification is assembled at run-time; if Rust
// had more powerful compile-time-compute capability (ie dependent types and
// a compile time execution model in the vein of Idris, Agda, or Coq) then
// maybe systems could be fully specified at compile time and the types and
// sizes for all inputs and outputs would be compile-time known; consequence
// of being untyped includes not statically guaranteeing links between nodes
// have matching types (or even data sizes for that matter); data size is
// asserted against at runtime, which is better than nothing; one
// quasi-upside of using untyped data is highlighting that some data
// conversion (serialization into common formats) might be needed between
// nodes (if they ran on different micro-architectures, for example); my
// hope was to have the compiler worry about this long term and hide it from
// programmers, but making it visible now at this level does keep us from
// forgetting the existence of this complexity

// Note: the waves DLS hides from programmers the serialization; in waves,
// action inputs, outputs, and state are typed. waves is implemented as a
// set of macros (see ../waves/README.md) that generate the
// appropriate serialization to untyped data.

/// fixed-sized block of bits
pub type Data = BitBox<usize, Lsb0>;

/// local persistent state available across cycles
pub type LoopbackRef<'a> = Option<&'a mut Data>;

/// Some(Frame) if the input is valid, and None if not
pub type InputFrameRef<'a> = Option<&'a Data>;

pub type OutputFrameRef<'a> = &'a mut DataWithValidity;

/// output data, which actions can label as invalid (if they do not or cannot provide valid data)
#[derive(Clone, Debug, PartialEq)]
pub struct DataWithValidity {
    pub data: Data,
    pub valid: bool,
}

// TODO(pouyad) Remove usage of tuple structs.

// relative frequency versus the system root frequency; the system root frequency itself is unit-
// less and is assigned meaning only when the system is physically provisioned at which point a
// physical frequency will be determined to satisfy provided performance constraints; for
// simulation, the root frequency is assumed to be unit-valued (1) and all other frequencies in the
// system are specified via multiplicative factor (how many times faster they are than the root)
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FrequencyFactor(pub usize);

/// Raw absolute frequency of a component.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Frequency {
    pub value: usize,
}

impl Frequency {
    pub fn new(value: usize) -> Self {
        Self { value }
    }
}

// cycles in units of the GCD between the node frequencies on either side of a link
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Latency(pub usize);

/// which side of a link determines the link frequency (frame rate); the
/// lead produces or consumes one frame per local cycle
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum FramingLead {
    Src,
    Dst,
}
