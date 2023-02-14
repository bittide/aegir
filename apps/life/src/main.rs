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

use life::Block;

use bits::Bits;
use bitvec::bitbox;
use platform;
use platform::specs::ApplicationNode;
use platform::FailureProperties;
use platform::MappingConfiguration1x1Network;
use platform::NodeSpec;
use platform::SystemSimulationCallbacks;
use with_checksum::WithChecksum;

use waves;

const LIFE_PROBABILITY: f64 = 0.2;
const BLOCK_SIDE_LENGTH: usize = 10;
const BLOCK_AREA: usize = BLOCK_SIDE_LENGTH * BLOCK_SIDE_LENGTH;
const NUM_GENERATIONS: usize = 100;

type LifeBlock = Block<BLOCK_SIDE_LENGTH, BLOCK_AREA>;

// Number of blocks square in the life universe. That is, the length of one side
// of the square grid in blocks.
const GRID_SQUARE_SIZE: usize = 5;

type Data = [u8; BLOCK_SIDE_LENGTH - 2];

type Border = WithChecksum<Data>;

/// Edge identifies a block's corner or edge. Cast to an array index in the
/// payloads send between blocks, as they're sharing their borders.
#[derive(Clone, Copy)]
enum Edge {
    TopLeftCorner,
    Top,
    TopRightCorner,
    Right,
    BottomRightCorner,
    Bottom,
    BottomLeftCorner,
    Left,
}

fn process_block(block: &mut LifeBlock, neighbors: Vec<Option<&Data>>) -> [Data; 8] {
    assert_eq!(neighbors.len(), 8);

    // Copy the neighboring cell's data into or block, if we have it.
    // We won't have it on the first generation.
    if let Some(line) = neighbors[Edge::TopLeftCorner as usize] {
        block.set(0, 0, line[0]);
    }
    if let Some(line) = neighbors[Edge::Top as usize] {
        block.set_row(line, 0);
    }
    if let Some(line) = neighbors[Edge::TopRightCorner as usize] {
        block.set(0, BLOCK_SIDE_LENGTH - 1, line[0]);
    }
    if let Some(line) = neighbors[Edge::Right as usize] {
        block.set_column(line, BLOCK_SIDE_LENGTH - 1);
    }
    if let Some(line) = neighbors[Edge::BottomRightCorner as usize] {
        block.set(BLOCK_SIDE_LENGTH - 1, BLOCK_SIDE_LENGTH - 1, line[0]);
    }
    if let Some(line) = neighbors[Edge::Bottom as usize] {
        block.set_row(line, BLOCK_SIDE_LENGTH - 1);
    }
    if let Some(line) = neighbors[Edge::BottomLeftCorner as usize] {
        block.set(BLOCK_SIDE_LENGTH - 1, 0, line[0]);
    }
    if let Some(line) = neighbors[Edge::Left as usize] {
        block.set_column(line, 0);
    }

    // If we had the neighboring cells' data sent to us, we can run our life
    // algorithm on our block. If we don't have data sent to us, this is the first
    // generation; we don't run life, we just send our border cells to our
    // neighbors, so that everyone can run next generation.
    if neighbors.iter().all(|x| x.is_some()) {
        block.update();
    }

    // Send our border cells to our neighbors.
    let mut output: [Data; 8] = [[0u8; BLOCK_SIDE_LENGTH - 2]; 8];

    output[Edge::TopLeftCorner as usize][0] = block.get(1, 1);
    block.copy_row(&mut output[Edge::Top as usize], 1);
    output[Edge::TopRightCorner as usize][0] = block.get(1, BLOCK_SIDE_LENGTH - 2);
    block.copy_column(&mut output[Edge::Right as usize], BLOCK_SIDE_LENGTH - 2);
    output[Edge::BottomRightCorner as usize][0] =
        block.get(BLOCK_SIDE_LENGTH - 2, BLOCK_SIDE_LENGTH - 2);
    block.copy_row(&mut output[Edge::Top as usize], BLOCK_SIDE_LENGTH - 2);
    output[Edge::BottomLeftCorner as usize][0] = block.get(1, BLOCK_SIDE_LENGTH - 2);
    block.copy_column(&mut output[Edge::Left as usize], 1);

    output
}

waves::action_fn! { block_step
    (block: LifeBlock)
    (neighbors: [Option<Border>; 8])
    -> (border: [Border; 8]) {
        // Validate that we received the neighbor data undamaged.
        // Note: On the first iteration after startup, all messages will be None.
        assert!(neighbors.iter().all(|n| n.is_none() || n.unwrap().is_ok()));

        // Create vector of references to neighbor data,
        // for easier consumption of process_block below.
        // i.e. convert from Vec<Option<WithChecksum<Data>>> to Vec<Option<&Data>>.
        let n: Vec<Option<&Data>> = neighbors
            .iter()
            .map(|n| n.as_ref().map(|x| x.borrow()))
            .collect();

        border = [Border::new([0u8; BLOCK_SIDE_LENGTH - 2]); 8];
        for (i, b) in process_block(&mut block, n).into_iter().enumerate() {
            border[i] = Border::new(b);
        }
    }
}

fn build_bittide_app() -> platform::Application {
    let mut app = platform::Application::new();
    let block_actions = (0..GRID_SQUARE_SIZE * GRID_SQUARE_SIZE)
        .map(|block_num| {
            let row = block_num / GRID_SQUARE_SIZE;
            let col = block_num % GRID_SQUARE_SIZE;
            let name = &format!("block_{}_{}", row, col);
            waves::action!(name in app
                    (block: LifeBlock)
                    (neighbors: [Option<Border>; 8])
                    -> (border: [Border; 8])
                {
                    type BlockState = (LifeBlock,);
                    let mut data = bitbox![0; <BlockState as Bits>::SIZE];
                    (LifeBlock::new(block_num as u64, LIFE_PROBABILITY)).pack_to(&mut data);
                    data
                }
                block_step

            )
        })
        .collect::<Vec<_>>();

    // Send link definitions.
    // (src_slot, dst_slot, d_row, d_col)
    // d_row/col is from src towards dst in grid of blocks.
    let links = [
        (
            Edge::TopLeftCorner,
            Edge::BottomRightCorner,
            GRID_SQUARE_SIZE - 1,
            GRID_SQUARE_SIZE - 1,
        ),
        (Edge::Top, Edge::Bottom, GRID_SQUARE_SIZE - 1, 0),
        (
            Edge::TopRightCorner,
            Edge::BottomLeftCorner,
            GRID_SQUARE_SIZE - 1,
            1,
        ),
        (Edge::Right, Edge::Left, 0, 1),
        (Edge::BottomRightCorner, Edge::TopLeftCorner, 1, 1),
        (Edge::Bottom, Edge::Top, 1, 0),
        (
            Edge::BottomLeftCorner,
            Edge::TopRightCorner,
            1,
            GRID_SQUARE_SIZE - 1,
        ),
        (Edge::Left, Edge::Right, 0, GRID_SQUARE_SIZE - 1),
    ];

    // Connect each block to its neighbors, to send/recv borders.
    for block_num in 0..GRID_SQUARE_SIZE * GRID_SQUARE_SIZE {
        let row = block_num / GRID_SQUARE_SIZE;
        let col = block_num % GRID_SQUARE_SIZE;
        for (src, dst, d_row, d_col) in links {
            let dst_row = (row + d_row) % GRID_SQUARE_SIZE;
            let dst_col = (col + d_col) % GRID_SQUARE_SIZE;
            let dst_index = dst_row * GRID_SQUARE_SIZE + dst_col;
            waves::link!(block_actions[block_num] border[src as usize] -> block_actions[dst_index] neighbors[dst as usize] in app);
        }
    }

    app
}

fn print_blocks(app: &platform::Application) {
    let mut blocks: Vec<LifeBlock> = app
        .iter_nodes()
        .map(|node_id| {
            let node = app.get_node(node_id);
            let node_ref = node.borrow();
            let stateful_node = node_ref.into_stateful_node().unwrap();
            let state = stateful_node.persistent_state().unwrap();
            LifeBlock::unpack(state)
        })
        .collect();
    blocks.sort_by_key(|a| a.id());

    let block_size = BLOCK_SIDE_LENGTH - 2;
    let sz = GRID_SQUARE_SIZE * block_size;
    let mut builder = String::with_capacity(GRID_SQUARE_SIZE * (block_size + 1));
    for row_index in 0..sz {
        for col_index in 0..sz {
            let block_row_index = row_index / block_size;
            let block_col_index = col_index / block_size;
            let v = blocks[block_row_index * GRID_SQUARE_SIZE + block_col_index]
                .get(1 + row_index % block_size, 1 + col_index % block_size);
            builder.push(('0' as u8 + v) as char);
        }
        builder.push('\n');
    }
    log::info!("\n{}", builder);
}

fn main() {
    env_logger::init();
    let app_spec = build_bittide_app();

    let allocation = platform::AllocationPolicy::OneToOneNetwork(MappingConfiguration1x1Network {
        frame_size: 64,
        ..Default::default()
    });
    let system_spec = platform::generate_system_spec(&app_spec, &allocation);

    let res = platform::simulate_bittide(
        &system_spec,
        &[&app_spec],
        allocation,
        None,
        NUM_GENERATIONS,
        &mut SystemSimulationCallbacks::default(),
        FailureProperties {
            frame_corruption_rate: 0.0001,
            ..Default::default()
        },
    );

    if let Err(e) = res {
        log::error!("{}", e);
    } else {
        log::info!("no errors");
    }

    print_blocks(&app_spec);
}
