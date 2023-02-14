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

use super::*;

use log;
use num_traits::FromPrimitive;
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64;
use std::convert::TryInto;
use waves;

/// Generates a request with random data
fn random_request(seed: u64) -> Request {
    // the key is picked with a seed to get overlapped requests
    let mut rng = Pcg64::seed_from_u64(seed);
    let key = rng.gen_range(0..(MAX_KEY as u64));
    // however, we want different operations and data for the keys.
    let mut rng = rand::thread_rng();
    let op = Operation::from_u64(rng.gen_range(0..(Operation::MaxOp as u64))).unwrap();
    let data = match op {
        Operation::Insert | Operation::Modify => {
            let arr: Data = (0..DATA_SIZE)
                .map(|_| rng.gen())
                .collect::<Vec<u8>>()
                .try_into()
                .unwrap();
            Some(arr)
        }
        _ => None,
    };
    Request { op, key, data }
}

/// Validates the response against the predefined set of responses and returns
/// the request from the predefined set of requests.
fn predefined_request_response(
    id: u32,
    cycle: usize,
    response: &Option<Response>,
    predefined_data: &ClientData,
) -> Option<Request> {
    let index = cycle % CLIENT_DATA_SIZE;
    assert_eq!(
        *response, predefined_data.responses[index],
        "Client {}: mismatched response in cycle {}",
        id, cycle
    );

    predefined_data.requests[index]
}

// Client action
waves::action_fn! { client
  (predefined_data: Option<ClientData>,
   cycle: u64,
   id: u32,
  )
  (response: Option<Response> )
   -> (request: Option<Request>) {
      if let Some(r) = &response {
          log::info!("{} @ cycle {}: {:?}", id, cycle, r);
      }

      request = match predefined_data {
          Some(ref data) => predefined_request_response(id, cycle as usize, &response, &data),
          None => Some(random_request(cycle + (id as u64))),
      };

      log::info!("{} @ cycle {}: {:?}", id, cycle, request);
      cycle += 1;
  }
}
