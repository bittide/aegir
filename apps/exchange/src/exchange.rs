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

mod center;
mod common;
mod logger;
mod trader;

use bits::Bits;
use bitvec::prelude::*;
use common::*;
use platform::specs::ApplicationNode;
use platform::Application;
use platform::SystemSimulationCallbacks;
use platform::SystemSimulationTrait;
use rand::Rng;
use rand_pcg::Pcg64;
use rand_seeder::Seeder;
use waves::*;

pub use crate::exchange::common::TRADER_COUNT;

pub fn build_exchange(logname: &str, rng_seed: Option<&str>) -> anyhow::Result<Application> {
    let mut base_prices: AssetTable<AssetPrice> = AssetTable::new(0);
    let mut initial_inventories: [AssetTable<AssetQuantity>; TRADER_COUNT] =
        [AssetTable::new(0); TRADER_COUNT];
    let seed_str = rng_seed.unwrap_or("bittide financial exchange");
    let mut rng: Pcg64 = Seeder::from(seed_str).make_rng();
    for asset in &ASSETS {
        base_prices[asset] = rng.gen_range(100..1000);
        initial_inventories.iter_mut().for_each(|inv| {
            inv[asset] = rng.gen_range(0..10000);
        });
    }
    let mut app_spec = Application::new();
    let center = action!("center" in app_spec
        (base_prices: AssetTable<AssetPrice>)
        (requests: [Option<TradeRequest>; TRADER_COUNT])
        -> (result: ExchangeResult,
            responses: [Option<TradeResponse>; TRADER_COUNT])
        {
            let mut center_state = bitbox![0; <(AssetTable<AssetPrice>,) as Bits>::SIZE];
            (base_prices,).pack_to(&mut center_state);
            center_state
        }
        center::center);
    let trader_nodes = (0..TRADER_COUNT)
        .map(|t| {
            action!(&format!("trader_{}", t) in app_spec
                (
                    inventory: AssetTable<AssetQuantity>,
                    outstanding_orders: [AssetTable<OrderBook>; TRADER_ROUNDTRIP_HOPS],
                    cycle: u64,
                )
                (last_trade: Option<TradeResponse>)
                 -> (next_trade: TradeRequest)
                 {
                     type TraderState = (
                         AssetTable<AssetQuantity>,
                         [AssetTable<OrderBook>; TRADER_ROUNDTRIP_HOPS],
                         u64, // rng seed
                         u64, // cycle
                     );
                     let mut data = bitbox![0; <TraderState as Bits>::SIZE];
                     (
                         initial_inventories[t],
                         [AssetTable::new(OrderBook::new()); TRADER_ROUNDTRIP_HOPS as usize],
                         // the seed will be the trader number in the top 32 bits, and
                         // the cycle number in the lower 32 bits of a u64. After 4B
                         // cycles, some trader sequences will repeat!
                         (t << 32) as u64,
                         0_u64,
                     )
                         .pack_to(&mut data);
                     data
                 }
                trader::trader
            )
        })
        .collect::<Vec<_>>();

    let sink = action!("logger" in app_spec
                           (logname: FileName, len: u64)
                           (input: ExchangeResult)
                            -> ()
                            {
                                // a type to represent a serializable string: a fixed length for the
                                // bytes, and a length to represent the actual string length because
                                // otherwise, from_utf8 decodes the nul bytes as part of the string.
                                type PackedString = (
                                    FileName,
                                    u64, // length
                                );
                                let mut data = bitbox![0; <PackedString as Bits>::SIZE];
                                let path = std::path::Path::new(logname);
                                if path.exists() {
                                    std::fs::remove_file(path)?;
                                }
                                let len = logname.as_bytes().len();
                                let mut logfile: FileName = [0; 256];
                                logfile[..len].copy_from_slice(logname.as_bytes());
                                (logfile, len as u64).pack_to(&mut data);
                                data
                            }
                           logger::logger);

    // Create the links
    (0..TRADER_COUNT).for_each(|i| {
        link!(trader_nodes[i] next_trade -> center requests[i] in app_spec);
        link!(center responses[i] -> trader_nodes[i] last_trade in app_spec);
    });
    link!(center result -> sink input in app_spec);
    log::debug!("exchange:\n{}", app_spec);
    Ok(app_spec)
}

pub fn run_exchange_app(
    logname: &str,
    cycles: usize,
    rng_seed: Option<&str>,
) -> anyhow::Result<()> {
    let exchange = build_exchange(logname, rng_seed)?;
    let mut simulation = platform::SoftwareSystemSimulation::new(&exchange);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&exchange, &mut SystemSimulationCallbacks::default());
    }

    Ok(())
}
