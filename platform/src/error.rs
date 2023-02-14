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

use petgraph::prelude::*;
use std::fmt;

use crate::Port;

#[derive(Debug, Eq, PartialEq)]
pub enum Error {
    OutOfMemory,
    OutOfCalendar,
    InvalidAddress,
    InvalidAllocation,
    InvalidCalendar,
    InvalidLink(NodeIndex, EdgeIndex),
    InvalidNode,
    InvalidPort(NodeIndex, EdgeIndex, Port),
    InvalidSchedule,
    InvalidPath,
    InvalidMergeOffset,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            // return and break should never really print!!
            Self::InvalidLink(n, l) => {
                write!(
                    f,
                    "ERROR: Invalid link {} for node {}",
                    l.index(),
                    n.index()
                )
            }
            Self::InvalidPort(n, l, p) => {
                write!(
                    f,
                    "ERROR: Invalid port {} for node {}:{}",
                    p,
                    n.index(),
                    l.index()
                )
            }
            _ => write!(f, "{:?}", self),
        }
    }
}

// TODO(cascaval): properly implement the std::error::Error trait
// this is needed to allow `anyhow::Result` to accept our definition of
// errors. We use `anyhow` extensively in the abstract topology and
// financial exchange.
impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        // Some(&self)
        None
    }
}
