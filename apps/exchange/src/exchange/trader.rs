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

use log::Level::Trace;
use log::{log_enabled, trace};
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64;
use std::cmp::{max, min};

use super::common::*;

// TODO(cascaval) Comment from cl/419871623 captured here:
//
// The fact that the trader code itself needs to account for the "latency" of
// communication between the trader and the exchange makes it non-portable (wrt
// outstanding_orders TRADER_ROUNDTRIP_HOPS). Of course, one can always use more
// buffering and thus allocate ensure that a placement will be possible, but it
// is an unnecessary burden on the programmer. Moreover, it also limits what the
// bittide scheduler can do to place nodes and route messages, because it
// requires to exactly fulfill this request -- the current implementation will
// be incorrect if the messages are not delivered exactly at those cycles since
// the response must be paired with the request. A more flexible implementation
// is possible but it would likely require tagging the messages.
waves::action_fn! { trader
    (
        inventory: AssetTable<AssetQuantity>,
        outstanding_orders: [AssetTable<OrderBook>; TRADER_ROUNDTRIP_HOPS],
        rng_seed: u64,
        cycle: u64,
    )
    (last_trade: Option<TradeResponse>)
     -> (next_trade: TradeRequest) {
        // create a reproducible sequence of orders by instantiating the
        // random number generator with seed that is specifing to the trader
        // and the current cycle. We do not want all the traders to generate
        // the same sequence every cycle.
        // The seed will be the trader number in the top 32 bits, and
        // the cycle number in the lower 32 bits of a u64. After 4B
        // cycles, some trader sequences will repeat!
        // rng_seed is set as part of the initial state and persisted.
        let mut rng = Pcg64::seed_from_u64(rng_seed);
        rng_seed += 1;
        let filled_orders = last_trade
            .as_ref()
            .map(|data| data.self_filled_orders)
            .unwrap_or_else(|| AssetTable::new(OrderBook::new()));
        next_trade = TradeRequest {
            order_books: AssetTable::new(OrderBook::new()),
        };
        for asset in &ASSETS {
            let actually_bought = filled_orders[asset]
                .bid
                .spread
                .iter()
                .sum::<AssetQuantity>();
            if actually_bought != 0 {
                trace!("Actually bought {} {:?}", actually_bought, asset);
            }
            inventory[asset] += actually_bought;

            let could_have_sold: AssetQuantity = outstanding_orders[cycle as usize]
                [asset]
                .ask
                .spread
                .iter()
                .sum();
            let actually_sold: AssetQuantity = filled_orders[asset].ask.spread.iter().sum();
            if (could_have_sold != 0) | (actually_sold != 0) {
                trace!(
                    "Actually sold {}, could have sold {} {:?}",
                    actually_sold,
                    could_have_sold,
                    asset
                );
            }
            assert!(
                actually_sold <= could_have_sold,
                "Exchange should not sell more than I asked, {} <= {} asset {:?}",
                actually_sold,
                could_have_sold,
                asset,
            );
            // refund the difference
            inventory[asset] += could_have_sold - actually_sold;

            let target_price: i32 = rng.gen_range(0..BOOK_DEPTH) as i32;
            let target_quantity = rng.gen_range(0..10000);
            let quantity_diff: i32 = target_quantity as i32 - inventory[asset] as i32;
            // 0 <= target_quantity < inf
            // quantity_diff := target_quantity - inventory
            // Therefore, -inventory <= quantity_diff < inf
            let target_price_lower_bound = max(0, target_price - 2);
            let target_price_upper_bound = min(BOOK_DEPTH as i32, target_price + 3);
            let target_price_spread = target_price_upper_bound - target_price_lower_bound;
            let uniform_spread_quantity_diff: i32 = quantity_diff.abs() / target_price_spread;
            for price_point in target_price_lower_bound..target_price_upper_bound {
                #[allow(clippy::comparison_chain)]
                if quantity_diff > 0 {
                    // Buy orders are unbounded
                    // 0 < quantity_diff < inf
                    next_trade.order_books[asset].bid.spread[price_point as usize] =
                    uniform_spread_quantity_diff as u32;
                } else if quantity_diff < 0 {
                    // Sell orders are bounded by inventory
                    // -inventory <= quantity_diff < 0
                    next_trade.order_books[asset].ask.spread[price_point as usize] =
                    uniform_spread_quantity_diff as u32;
                }
            }
            if log_enabled!(Trace) {
                let could_buy = next_trade.order_books[asset]
                    .bid
                    .spread
                    .iter()
                    .sum::<AssetQuantity>();
                if could_buy != 0 {
                    trace!("Buy at most {} {:?}", could_buy, asset);
                }
            }

            // Err on the side of underestimating inventory, lest it go negative.
            // Assume all sells succeeds (undo if exchange doesn't really fulfill).
            // Assume no buys will succeed (do the buy if the exchange really can fulfill).
            let could_sell = next_trade.order_books[asset]
                .ask
                .spread
                .iter()
                .sum::<AssetQuantity>();
            if could_sell != 0 {
                trace!("Sell at most {} {:?}", could_sell, asset);
            }
            assert!(
                could_sell <= inventory[asset],
                "This order book should not sell more asset shares than I have, {} <= {}.
                This can be caused by getting the roundtrip latency wrong, so I match the exchange's response with the wrong request.",
                could_sell,
                inventory[asset],
            );
            inventory[asset] -= could_sell;
        }

        outstanding_orders[cycle as usize] = next_trade.order_books;
        cycle = (cycle + 1) % (outstanding_orders.len() as u64);
    }
}
