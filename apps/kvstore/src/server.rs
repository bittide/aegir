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
use std::convert::TryInto;
use waves;

use super::*;
use crate::store::Store;

fn process_request(store: &mut Store, request: &Option<Request>) -> Option<Response> {
    request.map(|req| {
        let data = match req.op {
            Operation::Query => store.get(&req.key),
            Operation::Insert => store.insert(&req.key, req.data.unwrap()),
            Operation::Modify => store.modify(&req.key, req.data.unwrap()),
            _ => panic!("Invalid operation: {:?}", req.op),
        };
        Response {
            op: req.op,
            key: req.key,
            data,
        }
    })
}

waves::action_fn! { server
  (store: Store)
  (requests: [Option<Request>; CLIENT_COUNT])
   -> (responses: [Option<Response>; CLIENT_COUNT]) {
      responses = requests.iter().map(|req| process_request(&mut store, req))
        .collect::<Vec<Option<Response>>>()
        .try_into()
        .unwrap();
  }
}

// ------------------------------------------------------------------------
// Sharding
// ------------------------------------------------------------------------
waves::action_fn! { sharded_frontend
  ()
  (requests: [Option<Request>; CLIENT_COUNT],
   fwd_responses: [ResponseSet; SHARD_COUNT])
  ->
  (fwd_requests: [RequestSet; SHARD_COUNT],
   responses: [Option<Response>; CLIENT_COUNT]) {
      fwd_requests = (0..SHARD_COUNT).map(|_| RequestSet::default())
        .collect::<Vec<RequestSet>>()
        .try_into()
        .unwrap();
      let blk_size = MAX_KEY / SHARD_COUNT;
      requests.iter().enumerate().for_each(|(client, request)|
          if let Some(req) = request {
              let shard = ((req.key / blk_size as u64) as usize) % SHARD_COUNT;
              fwd_requests[shard].requests[client] = Some(req.clone());
          }
      );
      // at most a single shard will have a reply
      responses = (0..CLIENT_COUNT).map(|client| {
          let reply = fwd_responses.iter()
              .map(|set| set.responses[client])
              .filter(|r| r.is_some())
              .collect::<Vec<Option<Response>>>();
          if reply.len() > 0 {
              reply[0]
          } else {
              None
          }
      })
      .collect::<Vec<Option<Response>>>()
      .try_into()
      .unwrap()
  }
}

// the main difference with the single server is that there is a single incoming
// link (from the frontend) that carries a set of requests and a single outgoing
// link back to the front end with a set of requests. The set of requests and
// responses are in fact an array of CLIENT_COUNT size.
waves::action_fn! { sharded_server
  (id: u32, store: Store)
  (requests: RequestSet)
   -> (responses: ResponseSet) {
      responses = ResponseSet::default();
      log::info!("shard {} serving: {:?}", id, requests);
      requests.requests.iter().enumerate().for_each(|(client, r)| {
          responses.responses[client] = process_request(&mut store, r);
      })
  }
}

// ------------------------------------------------------------------------
// Replication
// ------------------------------------------------------------------------
const SERVERS_COUNT: usize = SHARD_COUNT * REPLICA_COUNT;

waves::action_fn! { frontend_with_replicas
                    ()
  (requests: [Option<Request>; CLIENT_COUNT],
   fwd_responses: [ResponseSet; SERVERS_COUNT])
  ->
  (fwd_requests: [RequestSet; SERVERS_COUNT],
   responses: [Option<Response>; CLIENT_COUNT]) {
    fwd_requests = (0..SERVERS_COUNT)
        .map(|_| RequestSet::default())
        .collect::<Vec<RequestSet>>()
        .try_into()
        .unwrap();
    // we map REPLICA_COUNT servers as a "single shard" and pick one of them
    // as a representative to process the request.
    let mut rng = rand::thread_rng();
    let blk_size = MAX_KEY / SERVERS_COUNT;
    requests.iter().enumerate().for_each(|(client, request)| {
        if let Some(req) = request {
            let shard = ((req.key / blk_size as u64) as usize) % SHARD_COUNT;
            let replica = rng.gen_range(0..REPLICA_COUNT);
            log::debug!("forwarding client {} req {:?} to {}",
                        client, req, shard + replica);
            fwd_requests[shard + replica].requests[client] = Some(req.clone());
        }
    });
    // at most a single replica from a shard set will have a reply
    responses = (0..CLIENT_COUNT)
        .map(|client| {
            let reply = fwd_responses
                .iter()
                .map(|set| set.responses[client])
                .filter(|r| r.is_some())
                .collect::<Vec<Option<Response>>>();
            if reply.len() > 0 {
                reply[0]
            } else {
                None
            }
        })
        .collect::<Vec<Option<Response>>>()
        .try_into()
        .unwrap()
  }
}

waves::action_fn! { replicated_server
    (id: u32, store: Store)
    (
        requests: RequestSet, // connection to the front-end
        replica_requests: [Option<Request>; REPLICA_COUNT - 1], // connections to replicas
    )
     ->
    (
        responses: ResponseSet,  // connection back to the front-end first
        replica_updates: [Option<Request>; REPLICA_COUNT - 1], // connections to replicas
    ) {
        let shard_id = (id as usize) / REPLICA_COUNT;
        let replica_id = (id as usize) % REPLICA_COUNT;
        // process all the replica requests, such that if there is a client
        // request for a key that has been processed at a different shard,
        // we serve a consistent copy.
        // Note: this is predicated on having a single cycle latency between replicas.
        if replica_requests.iter().any(|req| req.is_some()) {
            log::info!("shard {}:{} replicating: {:?}", shard_id, replica_id, replica_requests);
            replica_requests.iter().for_each(|req| { process_request(&mut store, req); } );
        }

        replica_updates = [None; REPLICA_COUNT - 1];
        responses = ResponseSet::default();
        requests.requests.iter().enumerate().for_each(|(client, req)| {
            if req.is_some() {
                log::info!("shard {}:{} serving: {:?}", shard_id, replica_id, req);
                responses.responses[client] = process_request(&mut store, req);
                // send the same request to all replicas
                replica_updates = [*req; REPLICA_COUNT - 1];
            }
      })
  }
}
