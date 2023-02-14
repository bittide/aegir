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

use serde::{Deserialize, Serialize};
use structopt::StructOpt;

/// The argument specification to create topologies.
#[derive(Serialize, Deserialize, Debug, StructOpt, Clone)]
pub enum Options {
    /// A grid topology
    #[structopt(name = "mesh2d")]
    Mesh2D {
        #[structopt(name = "x-size", short = "x", long, default_value = "4")]
        x: usize,
        #[structopt(name = "y-size", short = "y", long, default_value = "4")]
        y: usize,
    },
    /// A 3D grid topology
    #[structopt(name = "mesh3d")]
    Mesh3D {
        #[structopt(name = "x-size", short = "x", long, default_value = "4")]
        x: usize,
        #[structopt(name = "y-size", short = "y", long, default_value = "4")]
        y: usize,
        #[structopt(name = "z-size", short = "z", long, default_value = "4")]
        z: usize,
    },
    /// A 2D torus topology
    #[structopt(name = "torus2d")]
    Torus2D {
        #[structopt(name = "x-size", short = "x", long, default_value = "4")]
        x: usize,
        #[structopt(name = "y-size", short = "y", long, default_value = "4")]
        y: usize,
    },
    /// A 3D torus topology
    #[structopt(name = "torus3d")]
    Torus3D {
        #[structopt(name = "x-size", short = "x", long, default_value = "4")]
        x: usize,
        #[structopt(name = "y-size", short = "y", long, default_value = "4")]
        y: usize,
        #[structopt(name = "z-size", short = "z", long, default_value = "4")]
        z: usize,
    },
    /// A hypercube topology
    Hypercube {
        #[structopt(short, long, default_value = "3")]
        degree: usize,
    },
    /// A tree toplogy
    Tree {
        #[structopt(short, long, default_value = "4")]
        height: usize,
        #[structopt(short, long, default_value = "2")]
        children: usize,
    },
    /// Star
    /// hosts + 1 hub
    Star {
        #[structopt(short, long, default_value = "8")]
        hosts: usize,
    },
    /// Line
    Line {
        #[structopt(short, long, default_value = "8")]
        nodes: usize,
    },

    /// Full
    Full {
        #[structopt(short, long, default_value = "8")]
        nodes: usize,
    },

    /// The triangle topology simulated by Tong's FPGA setup
    Triangle,
}

use crate::Topology;
use crate::{Edge, Vertex};
use crate::{FullyConnected, Hypercube, Line, Mesh, Star, Torus, Tree};

impl Options {
    pub fn get_topology<N, C>(&self) -> Topology<N, C>
    where
        N: Vertex,
        C: Edge + std::fmt::Debug,
    {
        match *self {
            Self::Full { nodes } => FullyConnected::full(nodes),
            Self::Hypercube { degree } => Hypercube::hypercube(degree),
            Self::Line { nodes } => Line::line(nodes),
            Self::Mesh2D { x, y } => Mesh::mesh(&[x, y]),
            Self::Mesh3D { x, y, z } => Mesh::mesh(&[x, y, z]),
            Self::Star { hosts } => Star::star(hosts),
            Self::Torus2D { x, y } => Torus::torus(&[x, y]),
            Self::Torus3D { x, y, z, .. } => Torus::torus(&[x, y, z]),
            Self::Tree { height, children } => Tree::tree(height, children),
            Self::Triangle => FullyConnected::full(3),
        }
    }
}
