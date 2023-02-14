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

use bits::Bits;
use bits_derive::Bits;
use serde::{Deserialize, Serialize};
use std::fmt::Debug;
use std::ops::{Index, IndexMut};

pub type AssetPrice = u32;

pub type AssetQuantity = u32;

pub type FileName = [u8; 256];

#[derive(Clone, Copy, Debug, Default)]
pub struct Asset {
    index: usize,
}

pub const ASSET_COUNT: usize = 6;

// TODO(sgrayson): Should we use an enum here?
pub const ASSETS: [Asset; ASSET_COUNT] = [
    Asset { index: 0 },
    Asset { index: 1 },
    Asset { index: 2 },
    Asset { index: 3 },
    Asset { index: 4 },
    Asset { index: 5 },
];

// TODO(sgrayson): Should this be its own type?
#[derive(Bits, Clone, Copy, PartialEq, Debug, Deserialize, Serialize)]
pub struct AssetTable<T: Bits> {
    table: [T; ASSET_COUNT],
}

impl<T: Copy + Bits> AssetTable<T> {
    pub fn new(t: T) -> Self {
        AssetTable {
            table: [t; ASSET_COUNT],
        }
    }
}

impl<T: Bits> Index<&Asset> for AssetTable<T> {
    type Output = T;
    fn index(&self, asset: &Asset) -> &Self::Output {
        &self.table[asset.index]
    }
}

impl<T: Bits> IndexMut<&Asset> for AssetTable<T> {
    fn index_mut(&mut self, asset: &Asset) -> &mut Self::Output {
        &mut self.table[asset.index]
    }
}

pub const BOOK_DEPTH: usize = 30;
pub const TRADER_COUNT: usize = 30;

// The high-level programming model is _synchronous dataflow_, so it doesn't care about latencies on
// each link. It only needs to care about the number of hops from A to B, as determined by the
// application's topology.
pub const TRADER_ROUNDTRIP_HOPS: usize = 2;
#[allow(dead_code)]
pub const TRADER_TO_EXCHANGE_LATENCY: usize = 1;

// In the future, this will be the application's demand of bittide, not a computed parameter.
// It takes one cycle to actually process the message and TRADER_EXCHANGE_LATENCY to send it.
// Hence, the effective latency of each hop is one cycle more than the link latency.
#[allow(dead_code)]
pub const TRADER_ROUNDTRIP_LATENCY: usize =
    TRADER_ROUNDTRIP_HOPS * (1 + TRADER_TO_EXCHANGE_LATENCY);

// Note that in order to derive Bits, this has to be pub.
#[derive(Bits, Clone, Copy, PartialEq, Debug, Deserialize, Serialize)]
pub struct QuantitySpread {
    // Quantities evenly distributed around an implicit price point;  spread[DEPTH / 2] is the
    // middle of the spread;  DEPTH ideally should be odd to allow for even price points on either
    // side.
    // XXX  #[serde(with = "serde_arrays")]
    pub(super) spread: [AssetQuantity; BOOK_DEPTH],
}

impl QuantitySpread {
    pub(super) fn new() -> Self {
        Self {
            spread: [0; BOOK_DEPTH],
        }
    }
}

#[derive(Bits, Clone, Copy, PartialEq, Debug, Deserialize, Serialize)]
pub struct OrderBook {
    pub bid: QuantitySpread,
    pub ask: QuantitySpread,
}

impl OrderBook {
    pub fn new() -> Self {
        Self {
            bid: QuantitySpread::new(),
            ask: QuantitySpread::new(),
        }
    }
}
impl Default for OrderBook {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Bits, PartialEq, Debug)]
pub struct TradeRequest {
    pub(super) order_books: AssetTable<OrderBook>,
}

/// This class is holds data that goes from the exchange to each trader
/// Therefore, it derives Bits.
#[derive(Bits, PartialEq, Debug)]
pub struct TradeResponse {
    pub(super) self_filled_orders: AssetTable<OrderBook>,
    pub(super) aggregated_filled_orders: AssetTable<QuantitySpread>,
    pub(super) aggregated_unfilled_orders: AssetTable<OrderBook>,
    pub(super) base_prices: AssetTable<AssetPrice>,
}

/// This class is holds data that is used by the actual exchange (doesn't get sent over the wire).
#[derive(Bits, Debug, Deserialize, Serialize)]
pub struct ExchangeResult {
    pub(super) filled_orders: [AssetTable<OrderBook>; TRADER_COUNT],
    pub(super) aggregated_filled_orders: AssetTable<QuantitySpread>,
    pub(super) aggregated_unfilled_orders: AssetTable<OrderBook>,
}
