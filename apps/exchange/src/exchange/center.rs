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

use log::trace;
use std::cmp::min;
use std::convert::TryInto;

use super::common::*;

impl ExchangeResult {
    fn new() -> Self {
        Self {
            filled_orders: [AssetTable::new(OrderBook::new()); TRADER_COUNT],
            aggregated_filled_orders: AssetTable::new(QuantitySpread::new()),
            aggregated_unfilled_orders: AssetTable::new(OrderBook::new()),
        }
    }

    fn fill_orders(
        &mut self,
        asset: &Asset,
        price_point: usize,
        asking_trader_index: usize,
        bidding_trader_index: usize,
        quantity: AssetQuantity,
    ) {
        trace!(
            "fill orders for {:?} at {:?} asker {:?} bidder {:?} quantity {:?}",
            asset,
            price_point,
            asking_trader_index,
            bidding_trader_index,
            quantity
        );
        self.filled_orders[asking_trader_index][asset].ask.spread[price_point] += quantity;
        self.filled_orders[bidding_trader_index][asset].bid.spread[price_point] += quantity;
        self.aggregated_filled_orders[asset].spread[price_point] += quantity;
    }

    fn unfilled_bid(&mut self, asset: &Asset, price_point: usize, quantity: AssetQuantity) {
        self.aggregated_unfilled_orders[asset].bid.spread[price_point] += quantity;
    }

    fn unfilled_ask(&mut self, asset: &Asset, price_point: usize, quantity: AssetQuantity) {
        self.aggregated_unfilled_orders[asset].ask.spread[price_point] += quantity;
    }

    fn calculate_next_base_prices(&mut self, base_prices: &mut AssetTable<AssetPrice>) {
        for asset in &ASSETS {
            let mut sum = 0;
            let mut total_volume = 0;
            for price_point in 0..BOOK_DEPTH {
                let volume = self.aggregated_filled_orders[asset].spread[price_point] as i32;
                sum += price_point as i32 * volume;
                total_volume += volume;
            }
            if total_volume > 0 {
                let median_price_point = sum / total_volume;
                base_prices[asset] = (base_prices[asset] as i32
                    + (median_price_point - (BOOK_DEPTH / 2) as i32))
                    as u32;
            }
        }
    }
}

waves::action_fn! { center
    (base_prices: AssetTable<AssetPrice>)
    (requests: [Option<TradeRequest>; TRADER_COUNT])
     -> (result: ExchangeResult,
         responses: [Option<TradeResponse>; TRADER_COUNT]) {
  // This step function implements a "fair" matching;  other matching policies are also possible.
  result = ExchangeResult::new();

  // for each asset, for each price point, sum the total bid and ask volume and count the number
  // of active traders;  repeat { calculate the average per-trader volume and match up to that
  // amount, keeping a record of volume per trader } until matches have been exhausted (ask or bid
  // volume at the pricepoint is zero);
  for asset in &ASSETS {
      for price_point in 0..BOOK_DEPTH {
          let mut supply_table: Vec<(AssetQuantity, usize)> = Vec::new();
          let mut demand_table: Vec<(AssetQuantity, usize)> = Vec::new();
          let mut total_supply: AssetQuantity = 0;
          let mut total_demand: AssetQuantity = 0;
          requests.iter().enumerate().flat_map(|(i, result)| {
              result
                  .as_ref()
                  .map(|real_result| (i, real_result.order_books[asset]))
          })
          .for_each(|(trader_index, order_book)| {
              let supply_quantity = order_book.ask.spread[price_point];
              let demand_quantity = order_book.bid.spread[price_point];
              if supply_quantity > 0 {
                  supply_table.push((supply_quantity, trader_index));
                  total_supply += supply_quantity;
              }
              if demand_quantity > 0 {
                  demand_table.push((demand_quantity, trader_index));
                  total_demand += demand_quantity;
              }
          });

          let remaining_trade_volume = min(total_supply, total_demand);
          if remaining_trade_volume == 0 {
              continue;
          }
          trace!(
              "matching {:?} at {:?} -- supply {:?} demand {:?}",
              asset,
              price_point,
              supply_table,
              demand_table
          );

          supply_table.sort_unstable();
          demand_table.sort_unstable();

          // rust borrow avoidance: can't iterate the demand_table and also modify the elements
          let mut satisfied_demand = [0; TRADER_COUNT];

          for &(mut available_supply, asking_trader_index) in supply_table.iter() {
              for (demand_i, &(demand, bidding_trader_index)) in
                  demand_table.iter().enumerate()
              {
                  let buyer_count = demand_table.len() - demand_i;
                  let fair_supply = available_supply / (buyer_count as u32);
                  let remaining_fair_demand =
                      min(demand - satisfied_demand[bidding_trader_index], fair_supply);
                  if remaining_fair_demand == 0 {
                      continue;
                  }
                  let trade_volume = min(available_supply, remaining_fair_demand);

                  assert!(trade_volume > 0);
                  result.fill_orders(
                      asset,
                      price_point,
                      asking_trader_index,
                      bidding_trader_index,
                      trade_volume,
                  );
                  satisfied_demand[bidding_trader_index] += trade_volume;
                  available_supply -= trade_volume;
              }
              if available_supply > 0 {
                  result.unfilled_ask(asset, price_point, available_supply);
              }
          }
          // record all the unfulfilled demands, after we paired bidders with all askers.
          for &(demand, bidding_trader_index) in demand_table.iter() {
              let unsatisfied_demand = demand - satisfied_demand[bidding_trader_index];
              if unsatisfied_demand > 0 {
                  result.unfilled_bid(asset, price_point, unsatisfied_demand);
              }
          }
      }
  }
  result.calculate_next_base_prices(&mut base_prices);

  responses = (0..TRADER_COUNT)
      .map(|i| {
          Some(TradeResponse {
              self_filled_orders: result.filled_orders[i],
              aggregated_filled_orders: result.aggregated_filled_orders,
              aggregated_unfilled_orders: result.aggregated_unfilled_orders,
              base_prices,
          })
      })
      .collect::<Vec<Option<TradeResponse>>>()
      .try_into()
      .unwrap();
   }
}

#[cfg(test)]
mod tests {
    use platform::specs::{LinkProperties, LinkStatus, MockSystemContext};

    #[test]
    fn test_step_exchange() {
        use super::*;
        use env_logger::Target;
        use platform::{Data, DataWithValidity, InputFrameRef};
        use std::fs::File;
        use std::path::Path;

        let logpath = Path::new("/tmp/fx-logs");
        std::fs::create_dir_all(logpath)
            .expect(&format!("Failed to create logs dir: {}", logpath.display()));
        let logfile = File::create(logpath.join("test_step_exchange.log"))
            .expect("Failed to create log file");
        let _logger = env_logger::builder()
            .target(Target::Pipe(Box::new(logfile)))
            .is_test(true)
            .try_init();

        const BASE_PRICE: usize = 10;

        let base_prices = AssetTable::new(BASE_PRICE as u32);

        let mut order_books = vec![AssetTable::new(OrderBook::new()); TRADER_COUNT];
        order_books[0][&ASSETS[0]].ask.spread[0] = 10;
        order_books[1][&ASSETS[0]].ask.spread[0] = 20;
        order_books[2][&ASSETS[0]].bid.spread[0] = 20;
        order_books[3][&ASSETS[0]].bid.spread[0] = 20;
        let trade_requests: [TradeRequest; TRADER_COUNT] = order_books
            .into_iter()
            .map(|order_books| TradeRequest { order_books })
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        use bits::Bits;
        use bitvec::prelude::bitbox;
        let mut state_bits = bitbox![0; <AssetTable<AssetPrice> as Bits>::SIZE];
        base_prices.pack_to(&mut state_bits);

        let input_bits = (0..TRADER_COUNT)
            .map(|trader| {
                let mut data = bitbox![0; <TradeRequest as Bits>::SIZE];
                trade_requests[trader].pack_to(&mut data);
                data
            })
            .collect::<Vec<Data>>();

        log::debug!(
            "Option<TradeRequest> size: {} * {} = {}",
            <Option<TradeRequest> as Bits>::SIZE,
            TRADER_COUNT,
            <Option<TradeRequest> as Bits>::SIZE * TRADER_COUNT
        );
        log::debug!(
            "Option<TradeResponse> size: {} * {} = {}",
            <Option<TradeResponse> as Bits>::SIZE,
            TRADER_COUNT,
            <Option<TradeResponse> as Bits>::SIZE * TRADER_COUNT
        );
        log::debug!(
            "TradeResponse size: {} * {} = {}",
            <TradeResponse as Bits>::SIZE,
            TRADER_COUNT,
            <TradeResponse as Bits>::SIZE * TRADER_COUNT
        );

        let mut exchange_output: Vec<DataWithValidity> = Vec::new();
        exchange_output.push(DataWithValidity {
            data: bitbox![0; <ExchangeResult as Bits>::SIZE],
            valid: false,
        });
        (0..TRADER_COUNT).for_each(|_| {
            exchange_output.push(DataWithValidity {
                data: bitbox![0; <TradeResponse as Bits>::SIZE],
                valid: false,
            })
        });

        let input_links = input_bits
            .iter()
            .map(|_| LinkProperties {
                status: LinkStatus::Up,
            })
            .collect::<Vec<_>>();
        let output_links = exchange_output
            .iter()
            .map(|_| LinkProperties {
                status: LinkStatus::Up,
            })
            .collect::<Vec<_>>();
        let sys = MockSystemContext::new(input_links, output_links);

        super::center(
            Some(&mut state_bits),
            input_bits
                .iter()
                .map(|i| Some(i))
                .collect::<Vec<InputFrameRef>>()
                .as_slice(),
            exchange_output
                .iter_mut()
                .collect::<Vec<&mut DataWithValidity>>()
                .as_mut_slice(),
            &sys,
        );

        let exchange_result_bits = &exchange_output[0];
        assert!(exchange_result_bits.valid);
        (0..TRADER_COUNT).for_each(|trader| assert!(exchange_output[trader + 1].valid));

        let exchange_result = ExchangeResult::unpack(exchange_result_bits.data.as_bitslice());

        assert_eq!(
            exchange_result.aggregated_filled_orders[&ASSETS[0]].spread[0],
            30
        );
        assert_eq!(
            exchange_result.filled_orders[0][&ASSETS[0]].ask.spread[0],
            10
        );
        assert_eq!(
            exchange_result.filled_orders[1][&ASSETS[0]].ask.spread[0],
            20
        );
        assert_eq!(
            exchange_result.filled_orders[2][&ASSETS[0]].bid.spread[0],
            15
        );
        assert_eq!(
            exchange_result.filled_orders[3][&ASSETS[0]].bid.spread[0],
            15
        );
        assert_eq!(
            exchange_result.aggregated_unfilled_orders[&ASSETS[0]]
                .bid
                .spread[0],
            10
        );
    }
}
