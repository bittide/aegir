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

use crate::{Direction, FramingLead};
use std::collections::HashMap;
use std::convert::{From, Into};

#[derive(Ord, PartialOrd, Eq, PartialEq, Hash, Clone, Copy, Debug)]
pub enum PortLabel {
    Array(&'static str, usize),
    Name(&'static str),
    Number(usize),
}

impl From<&'static str> for PortLabel {
    fn from(name: &'static str) -> Self {
        Self::Name(name)
    }
}

impl From<usize> for PortLabel {
    fn from(number: usize) -> Self {
        Self::Number(number)
    }
}

impl From<(&'static str, usize)> for PortLabel {
    fn from(pair: (&'static str, usize)) -> Self {
        Self::Array(pair.0, pair.1)
    }
}

impl std::fmt::Display for PortLabel {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match &self {
            Self::Array(name, index) => write!(f, "{}[{}]", name, index),
            Self::Name(name) => name.fmt(f),
            Self::Number(number) => number.fmt(f),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FrameSize {
    /// for application level ports, we compute frame sizes from the data type.
    Computed(RttiType),
    /// for all other ports, we specify the frame_size explicitly
    Number(usize),
    /// default value.
    Undefined,
}

impl From<usize> for FrameSize {
    fn from(bits_count: usize) -> FrameSize {
        FrameSize::Number(bits_count)
    }
}

impl Default for FrameSize {
    fn default() -> Self {
        FrameSize::Undefined
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PortProperties {
    /// coming or going?
    pub direction: Direction,
    /// actual index for scalar ports, start index for array ports.
    pub index: usize,
    /// who's the lead?
    pub framing_lead: FramingLead,
    /// the frame size
    pub frame_size: FrameSize,
}

impl PortProperties {
    pub fn frame_size(&self) -> usize {
        match self.frame_size {
            FrameSize::Computed(ty) => ty.get_size(),
            FrameSize::Number(sz) => sz,
            FrameSize::Undefined => panic!("Can't quantify undefined frame size."),
        }
    }
}

impl Default for PortProperties {
    fn default() -> Self {
        Self {
            direction: Direction::Incoming,
            index: 0,
            framing_lead: FramingLead::Src,
            frame_size: FrameSize::default(),
        }
    }
}

/// Ports are interesting little beasts!
///
/// They may range from a single number (the index as defined in a hardware
/// configuration) that sends or receives a certain frame size, to
/// application level ports, that are named and typed.
///
/// All this information is collected at various places in building a
/// topology, and should be used to validate a connection, when finally two
/// ports are bound by a link.
#[derive(Ord, PartialOrd, Hash, Clone, Copy, Debug)]
pub struct Port {
    index: usize,
    properties: IgnoreEq<PortProperties>,
}

// enable conversion into usize, so that we can index with Ports.
impl Into<usize> for Port {
    fn into(self) -> usize {
        self.index
    }
}

// enable the creation of ports with just a number; although it is better to
// use `numbered` and give a port direction as well. Default is incoming.
impl From<usize> for Port {
    fn from(index: usize) -> Self {
        Self {
            index,
            properties: IgnoreEq::new(PortProperties::default()),
        }
    }
}

impl PartialEq for Port {
    fn eq(&self, other: &Port) -> bool {
        self.direction() == other.direction() && self.index == other.index
    }
}
impl Eq for Port {}

impl Port {
    pub fn new(index: usize, properties: &PortProperties) -> Self {
        Self {
            index,
            properties: IgnoreEq::new(properties.clone()),
        }
    }
    pub fn new_in(index: usize) -> Self {
        Self {
            index,
            properties: IgnoreEq::new(PortProperties {
                direction: Direction::Incoming,
                ..Default::default()
            }),
        }
    }
    pub fn new_out(index: usize) -> Self {
        Self {
            index,
            properties: IgnoreEq::new(PortProperties {
                direction: Direction::Outgoing,
                ..Default::default()
            }),
        }
    }
    pub fn direction(&self) -> Direction {
        self.properties.0.direction
    }

    pub fn frame_size(&self) -> usize {
        self.properties.0.frame_size()
    }
    pub fn framing_lead(&self) -> FramingLead {
        self.properties.0.framing_lead
    }
    pub fn set_framing_lead(&mut self, lead: FramingLead) {
        self.properties.0.framing_lead = lead;
    }
}

impl Default for Port {
    fn default() -> Self {
        Port::from(0)
    }
}

impl std::fmt::Display for Port {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        write!(f, "{}", self.index)
    }
}

pub type PortMap = HashMap<PortLabel, Port>;

/// takes an array of port specifications, and turns it into a portmap.
///
/// For each array port, the label has the name and the size of the array,
/// and we expand it to the all individual ports.
/// For all the other ports (named or numbered), we give them the right
/// indices.
pub fn to_portmap(ports: &[(PortLabel, PortProperties)]) -> PortMap {
    let mut input_ports = 0;
    let mut output_ports = 0;
    log::trace!("Port specs: {:#?}", ports);
    ports
        .iter()
        .map(|(label, props)| {
            let base_count = match props.direction {
                Direction::Incoming => &mut input_ports,
                Direction::Outgoing => &mut output_ports,
            };
            match label {
                PortLabel::Array(name, index) => {
                    let mut res = Vec::new();
                    for idx in 0..*index {
                        res.push((
                            PortLabel::from((*name, idx)),
                            Port::new(*base_count + idx, props),
                        ));
                    }
                    *base_count += index;
                    res
                }
                PortLabel::Name(name) => {
                    let res = vec![(PortLabel::from(*name), Port::new(*base_count, props))];
                    *base_count += 1;
                    res
                }
                PortLabel::Number(n) => {
                    let res = vec![(PortLabel::from(*n), Port::new(*base_count, props))];
                    *base_count += 1;
                    res
                }
            }
        })
        .flatten()
        .collect::<PortMap>()
}

/**
 * Mark a field as ignored when deriving Eq/PartialEq/Hash.
 *
 * It is passed through unchanged for Debug.
 */
#[derive(Copy, Clone)]
pub struct IgnoreEq<T>(T);
impl<T> IgnoreEq<T> {
    fn new(val: T) -> Self {
        Self(val)
    }
}

impl<T> PartialEq for IgnoreEq<T> {
    fn eq(&self, _other: &IgnoreEq<T>) -> bool {
        true
    }
}
impl<T> Eq for IgnoreEq<T> {}
impl<T> PartialOrd for IgnoreEq<T> {
    fn partial_cmp(&self, _: &Self) -> Option<std::cmp::Ordering> {
        Some(std::cmp::Ordering::Equal)
    }
}
impl<T> Ord for IgnoreEq<T> {
    fn cmp(&self, _: &Self) -> std::cmp::Ordering {
        std::cmp::Ordering::Equal
    }
}
impl<T> std::hash::Hash for IgnoreEq<T> {
    fn hash<H: std::hash::Hasher>(&self, _state: &mut H) {}
}
impl<T: std::fmt::Debug> std::fmt::Debug for IgnoreEq<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.0.fmt(f)
    }
}

/**
 * Exposes the name, size, and equality of a type dynamically.
 */
#[derive(Clone, Copy, PartialEq, Hash, Eq, Debug)]
pub struct RttiType {
    id: std::any::TypeId,
    size: usize,
    // name is IgnoreEq, because the name is not guaranteed to be canonacalized (see [docs]).
    // [docs]: https://doc.rust-lang.org/std/any/fn.type_name.html
    name: IgnoreEq<&'static str>,
}

impl RttiType {
    pub fn new<Type: 'static + Sized + bits::Bits>() -> Self {
        Self {
            id: std::any::TypeId::of::<Type>(),
            name: IgnoreEq::new(std::any::type_name::<Type>()),
            size: <Type as bits::Bits>::SIZE,
        }
    }

    pub fn get_name(&self) -> &'static str {
        self.name.0
    }

    pub fn get_size(&self) -> usize {
        self.size
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ignore_eq() {
        let p0 = &Port::new(
            0,
            &PortProperties {
                frame_size: FrameSize::Number(10),
                ..Default::default()
            },
        );
        let p1 = Port::new(
            0,
            &PortProperties {
                frame_size: FrameSize::Number(5),
                ..Default::default()
            },
        );
        assert_eq!(*p0, p1);
    }
    #[test]
    fn test_ports_to_portmap() {
        const IN_ARRAY1: usize = 5;
        const IN_ARRAY3: usize = 2;
        const OUT_ARRAY0: usize = 3;
        let inputs = vec![
            (
                PortLabel::from("in0"),
                PortProperties {
                    direction: Direction::Incoming,
                    frame_size: FrameSize::Computed(RttiType::new::<u64>()),
                    ..PortProperties::default()
                },
            ),
            (
                PortLabel::from(("in_array1", IN_ARRAY1)),
                PortProperties {
                    direction: Direction::Incoming,
                    frame_size: FrameSize::Computed(RttiType::new::<u16>()),
                    ..PortProperties::default()
                },
            ),
            (
                PortLabel::from(("out_array0", OUT_ARRAY0)),
                PortProperties {
                    direction: Direction::Outgoing,
                    frame_size: FrameSize::Computed(RttiType::new::<Option<u16>>()),
                    ..PortProperties::default()
                },
            ),
            (
                PortLabel::from("in2"),
                PortProperties {
                    direction: Direction::Incoming,
                    frame_size: FrameSize::Computed(RttiType::new::<u64>()),
                    ..PortProperties::default()
                },
            ),
            (
                PortLabel::from(("in_array3", IN_ARRAY3)),
                PortProperties {
                    direction: Direction::Incoming,
                    frame_size: FrameSize::Computed(RttiType::new::<Option<u64>>()),
                    ..PortProperties::default()
                },
            ),
            (
                // This creates a Nubmered(out_array0.len()) label in order
                // to test that path as well.
                PortLabel::from(OUT_ARRAY0),
                PortProperties {
                    direction: Direction::Outgoing,
                    frame_size: FrameSize::Computed(RttiType::new::<u16>()),
                    ..PortProperties::default()
                },
            ),
        ];
        let output_map = to_portmap(inputs.as_slice());

        let in0 = output_map
            .get(&PortLabel::from("in0"))
            .unwrap_or_else(|| panic!("Missing port in0"));
        assert_eq!(in0.index, 0);
        assert_eq!(in0.direction(), Direction::Incoming);
        assert_eq!(in0.frame_size(), 64);

        (0..IN_ARRAY1).for_each(|i| {
            let arr = output_map
                .get(&PortLabel::from(("in_array1", i)))
                .unwrap_or_else(|| panic!("Missing port in_array1[{}]", i));
            assert_eq!(arr.index, 1 + i);
            assert_eq!(arr.direction(), Direction::Incoming);
            assert_eq!(arr.frame_size(), 16);
        });

        let in2 = output_map
            .get(&PortLabel::from("in2"))
            .unwrap_or_else(|| panic!("Missing port in2"));
        assert_eq!(in2.index, 1 + IN_ARRAY1);
        assert_eq!(in2.direction(), Direction::Incoming);
        assert_eq!(in2.frame_size(), 64);

        (0..IN_ARRAY3).for_each(|i| {
            let arr = output_map
                .get(&PortLabel::from(("in_array3", i)))
                .unwrap_or_else(|| panic!("Missing port in_array3[{}]", i));
            assert_eq!(arr.index, 1 + 1 + IN_ARRAY1 + i);
            assert_eq!(arr.direction(), Direction::Incoming);
            assert_eq!(arr.frame_size(), 65);
        });

        let out1 = output_map
            .get(&OUT_ARRAY0.into())
            .unwrap_or_else(|| panic!("Missing port out1"));
        assert_eq!(out1.index, OUT_ARRAY0);
        assert_eq!(out1.direction(), Direction::Outgoing);
        assert_eq!(out1.frame_size(), 16);

        (0..OUT_ARRAY0).for_each(|i| {
            let arr = output_map
                .get(&PortLabel::from(("out_array0", i)))
                .unwrap_or_else(|| panic!("Missing port out_array0[{}]", i));
            assert_eq!(arr.index, i);
            assert_eq!(arr.direction(), Direction::Outgoing);
            assert_eq!(arr.frame_size(), 17);
        });
    }
}
