// Copyright 2020 Google LLC
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

use crate::NodeId;

/// Interface for a 2D projection of the topology
pub trait Layout2D {
    /// The X extent in a virtual canvas
    fn get_max_x(&self) -> usize;
    /// The Y extent in a virtual canvas
    fn get_max_y(&self) -> usize;
    /// Node coordinates in a the virtual canvas
    fn get_node_coordinates(&self, node_id: NodeId) -> Coordinates;
}

#[derive(Debug, PartialEq)]
pub struct Coordinates {
    pub x: usize,
    pub y: usize,
}

impl Coordinates {
    pub fn new(x: usize, y: usize) -> Self {
        Self { x, y }
    }
}
