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

use rand::Rng;
use std::mem;

use bits_derive::Bits;

/// Block is a square container of individual life cells, implementing Conway's
/// Game of Life. A Block assumes it's being used in a distributed mode, where
/// the cells in the outermost rows/columns are assumed to be copied from the
/// neighboring blocks by some sort of coordination layer. We can then run the
/// life algorithm on the non-border cells.
/// Note: Block must be a fixed size due to the limitations of implementing
/// waves actions using macros.
#[derive(Bits, Clone, Debug)]
pub struct Block<const SIDE_LENGTH: usize, const AREA: usize> {
    /// cell holds the 'life' cells. 1 for alive, 0 for dead.
    cell: [u8; AREA],
    /// buffer holds a working area used by the life algorihm; when computing
    /// the next generation, we build up the result in `buffer` and then
    /// swap it with `cell` once complete. Note we can't just overwrite cells
    /// as we pass over them, as this rows' data is used when processing the
    /// following row; so if we modify it before running that row, we corrupt
    /// the next row's input data.
    buffer: [u8; AREA],
    /// id holds a unique ID specifed at construction. This is used to figure
    /// out where in the universe this block is in relation to the others.
    id: u64,
}

// Indexed by {0,1} (alive or dead) and the count of the neighboring squares,
// this lookup tells us whether a square should survive in the next generation.
// A live square should live if it has 2 or 3 live neighbors, a dead cell should
// come to life if it has 3 live neighbors.
const RULE_TABLE: [[u8; 9]; 2] = [
    [0, 0, 0, 1, 0, 0, 0, 0, 0], // Dead.
    [0, 0, 1, 1, 0, 0, 0, 0, 0], // Alive
];

impl<const SIDE_LENGTH: usize, const AREA: usize> Block<SIDE_LENGTH, AREA> {
    /// new returns a new Block with cells randomly live/dead as per the
    /// live_probability.
    pub fn new(id: u64, live_probability: f64) -> Block<SIDE_LENGTH, AREA> {
        let mut cell = [0u8; AREA];
        let mut rng = rand::thread_rng();
        for row_index in 1..(SIDE_LENGTH - 1) {
            for col_index in 1..(SIDE_LENGTH - 1) {
                cell[row_index * SIDE_LENGTH + col_index] = rng.gen_bool(live_probability) as u8;
            }
        }
        Block {
            cell: cell,
            buffer: [0u8; AREA],
            id: id,
        }
    }

    /// with_fill returns a new Block with every cell set to `value`.
    pub fn with_fill(id: u64, value: u8) -> Block<SIDE_LENGTH, AREA> {
        Block {
            cell: [value; AREA],
            buffer: [0u8; AREA],
            id: id,
        }
    }

    /// id returns id passed in at construction.
    pub fn id(&self) -> u64 {
        self.id
    }

    /// update runs Conway's game of life algorithm on the internal
    /// (non-border) cells of this Block. The border cells are assumed to be
    /// the cells from the neighboring blocks.
    pub fn update(&mut self) {
        let end = SIDE_LENGTH - 1;
        for row_index in 1..end {
            for col_index in 1..end {
                let count = self.neighbor_sum(row_index, col_index);
                let alive = RULE_TABLE[self.get(row_index, col_index) as usize][count as usize];
                self.buffer[row_index * SIDE_LENGTH + col_index] = alive;
            }
        }
        mem::swap(&mut self.buffer, &mut self.cell);
    }

    /// neighbor_sum returns the sum of the 8 cells centered at
    /// (row_index,col_index). Assumes row_index/col_index is not a border
    /// square.
    fn neighbor_sum(&self, row_index: usize, col_index: usize) -> u8 {
        let index = row_index * SIDE_LENGTH + col_index;
        return self.cell[index - SIDE_LENGTH - 1]
            + self.cell[index - SIDE_LENGTH]
            + self.cell[index - SIDE_LENGTH + 1]
            + self.cell[index - 1]
            + self.cell[index + 1]
            + self.cell[index + SIDE_LENGTH - 1]
            + self.cell[index + SIDE_LENGTH]
            + self.cell[index + SIDE_LENGTH + 1];
    }

    // get returns the cell value at specified row/col.
    pub fn get(&self, row_index: usize, col_index: usize) -> u8 {
        self.cell[row_index * SIDE_LENGTH + col_index]
    }

    // set updates the cell value at specified row/col.
    pub fn set(&mut self, row_index: usize, col_index: usize, value: u8) {
        self.cell[row_index * SIDE_LENGTH + col_index] = value;
    }

    pub fn copy_column(&self, v: &mut [u8], col_index: usize) {
        assert_eq!(v.len(), SIDE_LENGTH - 2);
        for i in 0..v.len() {
            v[i] = self.get(1 + i, col_index);
        }
    }

    pub fn set_column(&mut self, v: &[u8], col_index: usize) {
        assert_eq!(v.len(), SIDE_LENGTH - 2);
        for i in 0..v.len() {
            self.set(1 + i, col_index, v[i]);
        }
    }

    pub fn copy_row(&self, v: &mut [u8], row_index: usize) {
        assert_eq!(v.len(), SIDE_LENGTH - 2);
        let start = row_index * SIDE_LENGTH + 1;
        let end = (row_index + 1) * SIDE_LENGTH - 1;
        v.copy_from_slice(&self.cell[start..end]);
    }

    pub fn set_row(&mut self, v: &[u8], row_index: usize) {
        assert_eq!(v.len(), SIDE_LENGTH - 2);
        let start = row_index * SIDE_LENGTH + 1;
        let end = (row_index + 1) * SIDE_LENGTH - 1;
        let dst = &mut self.cell[start..end];
        dst.copy_from_slice(v);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_neighbor_sum() {
        let mut cell = Block::<6, 36>::with_fill(0, 0u8);

        // "Block" is still life.
        let block: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 1, 1, 0, 0, //
            0, 0, 1, 1, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        cell.cell = block.clone();
        cell.update();
        assert_eq!(cell.cell, block);

        // "Tub" is still life.
        let tub: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 1, 0, 0, //
            0, 0, 1, 0, 1, 0, //
            0, 0, 0, 1, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        cell.cell = tub.clone();
        cell.update();
        assert_eq!(cell.cell, tub);

        // Islands of two disappear.
        cell.cell = [
            0, 0, 0, 0, 0, 0, //
            0, 1, 1, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        cell.update();
        assert_eq!(cell.cell, [0u8; 36]);

        // "Blinker".
        let vertical_line: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 0, 1, 0, 0, 0, //
            0, 0, 1, 0, 0, 0, //
            0, 0, 1, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        let horizontal_line: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 1, 1, 1, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        cell.cell = vertical_line.clone();
        cell.update();
        assert_eq!(cell.cell, horizontal_line);
        cell.update();
        assert_eq!(cell.cell, vertical_line);

        // "Beacon"
        let beacon_open: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 1, 1, 0, 0, 0, //
            0, 1, 0, 0, 0, 0, //
            0, 0, 0, 0, 1, 0, //
            0, 0, 0, 1, 1, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        let beacon_closed: [u8; 36] = [
            0, 0, 0, 0, 0, 0, //
            0, 1, 1, 0, 0, 0, //
            0, 1, 1, 0, 0, 0, //
            0, 0, 0, 1, 1, 0, //
            0, 0, 0, 1, 1, 0, //
            0, 0, 0, 0, 0, 0, //
        ];
        cell.cell = beacon_open.clone();
        cell.update();
        assert_eq!(cell.cell, beacon_closed);
        cell.update();
        assert_eq!(cell.cell, beacon_open);
    }
}
