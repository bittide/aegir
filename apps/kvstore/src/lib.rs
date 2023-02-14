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

//! A key-value store client-server.
//!
//! This application is a minimal microservice pipeline; it allows us to explore
//! various implementations of a service, compare the refactoring for scaling
//! burden on the programmer, and the limitations imposed by the bittide
//! programming model.
//!
//! The server maintains a database of key-value pairs and allows clients to
//! query, insert, or modify pairs.
//!
//! Clients issue requests to the server. All requests require a response, which
//! consists of an optional pair, as follows:
//!   - for a query: if the key exists, return Some(pair), None otherwise.
//!   - for a insertion: return Some(requested pair) if inserted, None
//!   if the key already exists.
//!   - for a modification: return Some(old pair) if key exists, None otherwise.
//!
//!  Insertions fail if the key already exists.
//!  Modifications fail if the key does not exist.
//!
//! We currently have 2 implementations:
//!   - **Simple**: a single server with a set of clients directly connected the server.
//!   - **Sharded**: a sharded server with a front-end node that directs
//!     requests according to a mapping function (currently chunks of key values
//!     based on the number of shards). Clients connect to the front-end, and are
//!     unchanged -- the front-end acts like the simple server.
//!
//! We also plan an implementation that supports replicated servers.
//!
use bits::Bits;
use bits_derive::Bits;
use bitvec::bitbox;
use num_derive::FromPrimitive;
use platform::specs::ApplicationNode;
use platform::FailureProperties;
use platform::{Application, SystemSimulationCallbacks, SystemSimulationTrait};
use std::cmp::Ordering;
use waves::*;

mod client;
mod modes;
mod server;
mod store;

pub use modes::{RunMode, ServerConfig};

pub const CLIENT_COUNT: usize = 10;
pub const MAX_KEY: usize = 100;
pub const DATA_SIZE: usize = 10;
pub const SHARD_COUNT: usize = 10;
pub const REPLICA_COUNT: usize = 3;
pub const CLIENT_DATA_SIZE: usize = 10;

pub type Key = u64;
pub type Data = [u8; DATA_SIZE];

/// Set of supported operations
#[derive(Bits, Clone, Copy, Debug, FromPrimitive, PartialEq, Eq)]
pub enum Operation {
    Query,
    Insert,
    Modify,
    MaxOp,
}

/// Client requests
#[derive(Bits, Clone, Copy, Debug)]
pub struct Request {
    pub(crate) op: Operation,
    pub(crate) key: Key,
    pub(crate) data: Option<Data>,
}

/// Encapsulates a set of requests.
///
/// This is because our interface interprets arrays as links, and we need to
/// send an entire group of requests to a single shard (or replica).
#[derive(Bits, Clone, Debug, Default)]
pub struct RequestSet {
    requests: [Option<Request>; CLIENT_COUNT],
}

/// Server responses
#[derive(Bits, Clone, Copy, Debug, PartialEq)]
pub struct Response {
    op: Operation,
    pub(crate) key: Key,
    pub(crate) data: Option<Data>,
}

/// Encapsulates a set of responses.
///
/// Same reason as the RequestSet.
#[derive(Bits, Clone, Debug, Default)]
pub struct ResponseSet {
    responses: [Option<Response>; CLIENT_COUNT],
}

/// A set of predefined requests and responses for clients.
///
/// This is mainly used for testing to create a predefined pattern of
/// requests and their corresponding responses.
#[derive(Bits, Clone, Debug)]
struct ClientData {
    requests: [Option<Request>; CLIENT_DATA_SIZE],
    responses: [Option<Response>; CLIENT_DATA_SIZE],
}

/// Defines the state for a client.
/// A None ClientData value implies that the client will generate a random set of requests.
/// If the ClientData is present, the client validates the responses.
type ClientState = (
    Option<ClientData>, // predefined data
    u64,                // cycle
    u32,                // id
);

type GetClientData = fn(usize) -> Option<ClientData>;

/// Used to initialize clients generating random requests.
fn empty_client_data(_client_id: usize) -> Option<ClientData> {
    None
}

fn build_single_server(client_data: GetClientData) -> anyhow::Result<Application> {
    let mut app = Application::new();

    let server = action!("server" in app
                         (store: store::Store)
                         (requests: [Option<Request>; CLIENT_COUNT])
                          -> (responses: [Option<Response>; CLIENT_COUNT])
                         {
                             let mut data = bitbox![0; <store::Store as bits::Bits>::SIZE];
                             let store = store::Store::new();
                             store.pack_to(&mut data);
                             data
                         }
                         server::server
    );

    let clients = (0..CLIENT_COUNT)
        .map(|client| {
            action!(&format!("client_{}", client) in app
                    (id: u32, cycle: u64)
                    (response: Option<Response>) -> (request: Option<Request>)
                    {
                        let mut data = bitbox![0; <ClientState as Bits>::SIZE];
                        (client_data(client), 0_u64, client as u32).pack_to(&mut data);
                        data
                    }
                    client::client
            )
        })
        .collect::<Vec<_>>();

    for client in 0..CLIENT_COUNT {
        link!(clients[client] request -> server requests[client] in app);
        link!(server responses[client] -> clients[client] response in app);
    }

    Ok(app)
}

fn build_sharded_server(client_data: GetClientData) -> anyhow::Result<Application> {
    let mut app = Application::new();

    let fe_server = action!("fe_server" in app
        ()
        (requests: [Option<Request>; CLIENT_COUNT],
         fwd_responses: [ResponseSet; SHARD_COUNT])
        ->
        (fwd_requests: [RequestSet; SHARD_COUNT],
         responses: [Option<Response>; CLIENT_COUNT])
        {  }
        server::sharded_frontend
    );

    let servers = (0..SHARD_COUNT)
        .map(|shard| {
            action!(&format!("server_{}", shard) in app
            (id: u32, store: store::Store)
            (requests: RequestSet)
             -> (responses: ResponseSet)
            {
                type ShardState = (u32, store::Store);
                let mut data = bitbox![0; <ShardState as Bits>::SIZE];
                (shard as u32,
                 store::Store::new()).pack_to(&mut data);
                data
            }
            server::sharded_server
            )
        })
        .collect::<Vec<_>>();

    let clients = (0..CLIENT_COUNT)
        .map(|client| {
            action!(&format!("client_{}", client) in app
               () (response: Option<Response>) -> (request: Option<Request>)
               {
                   let mut data = bitbox![0; <ClientState as Bits>::SIZE];
                   (client_data(client), 0_u64, client as u32).pack_to(&mut data);
                   data
               }
               client::client
            )
        })
        .collect::<Vec<_>>();

    for client in 0..CLIENT_COUNT {
        link!(clients[client] request -> fe_server requests[client] in app);
        link!(fe_server responses[client] -> clients[client] response in app);
    }
    for shard in 0..SHARD_COUNT {
        link!(fe_server fwd_requests[shard] -> servers[shard] requests in app);
        link!(servers[shard] responses -> fe_server fwd_responses[shard] in app);
    }

    log::debug!("app topology:\n{}", app);

    Ok(app)
}

fn build_replicated_server(client_data: GetClientData) -> anyhow::Result<Application> {
    let mut app = Application::new();
    const SERVER_COUNT: usize = SHARD_COUNT * REPLICA_COUNT;
    let fe_server = action!("fe_server" in app
        ()
        (requests: [Option<Request>; CLIENT_COUNT],
         fwd_responses: [ResponseSet; SERVER_COUNT])
        ->
        (fwd_requests: [RequestSet; SERVER_COUNT],
         responses: [Option<Response>; CLIENT_COUNT])
        {  }
        server::frontend_with_replicas
    );

    let servers = (0..SERVER_COUNT)
        .map(|server| {
            let shard_id = server / REPLICA_COUNT;
            let replica_id = server % REPLICA_COUNT;
            action!(&format!("server_{}:{}", shard_id, replica_id) in app
            (id: u32, store: store::Store)
                    (
                        requests: RequestSet,
                        replica_requests: [Option<Request>; REPLICA_COUNT - 1],

            )
             ->
                    (
                        responses: ResponseSet,
                        replica_updates: [Option<Request>; REPLICA_COUNT - 1],

            )
            {
                type ShardState = (u32, store::Store);
                let mut data = bitbox![0; <ShardState as Bits>::SIZE];
                (server as u32,
                 store::Store::new()).pack_to(&mut data);
                data
            }
            server::replicated_server
            )
        })
        .collect::<Vec<_>>();

    let clients = (0..CLIENT_COUNT)
        .map(|client| {
            action!(&format!("client_{}", client) in app
                    () (response: Option<Response>) -> (request: Option<Request>)
                    {
                        let mut data = bitbox![0; <ClientState as Bits>::SIZE];
                        (client_data(client), 0_u64, client as u32).pack_to(&mut data);
                        data
                    }
                    client::client
            )
        })
        .collect::<Vec<_>>();

    for client in 0..CLIENT_COUNT {
        link!(clients[client] request -> fe_server requests[client] in app);
        link!(fe_server responses[client] -> clients[client] response in app);
    }
    for server in 0..SERVER_COUNT {
        // fe connections
        link!(fe_server fwd_requests[server] -> servers[server] requests in app);
        link!(servers[server] responses -> fe_server fwd_responses[server] in app);
        // connect the replicas
        let shard_id = server / REPLICA_COUNT;
        let replica_id = server % REPLICA_COUNT;
        for replica in 0..REPLICA_COUNT {
            // each server(replica) establishes links with the other replicas in the shard:
            // to compute the source and destination ports we skip the replica_id port.
            // maybe there is a simpler trick to do this!
            if replica != replica_id {
                let replica_server = shard_id * REPLICA_COUNT + replica;
                let (src_link_id, dst_link_id) = match replica.cmp(&replica_id) {
                    Ordering::Equal => continue, // skip self-links.
                    Ordering::Less => (replica, replica_id - 1),
                    Ordering::Greater => (replica - 1, replica_id),
                };
                log::trace!(
                    "Link: {}:{} -> {}:{}",
                    server,
                    src_link_id,
                    replica_server,
                    dst_link_id
                );
                link!(servers[server] replica_updates[src_link_id] ->
                      servers[replica_server] replica_requests[dst_link_id] in app);
            }
        }
    }

    log::debug!("app topology:\n{}", app);

    Ok(app)
}

pub fn run_app(cycles: usize, server_config: ServerConfig) -> anyhow::Result<()> {
    let app = match server_config {
        ServerConfig::Single => build_single_server(empty_client_data)?,
        ServerConfig::Sharded => build_sharded_server(empty_client_data)?,
        ServerConfig::Replicated => build_replicated_server(empty_client_data)?,
    };

    let mut simulation = platform::SoftwareSystemSimulation::new(&app);
    for _ in 0..cycles {
        simulation.simulate_system_one_cycle(&app, &mut SystemSimulationCallbacks::default());
    }
    Ok(())
}

pub fn simulate_app(cycles: usize, server_config: ServerConfig) -> anyhow::Result<()> {
    let app = match server_config {
        ServerConfig::Single => build_single_server(empty_client_data)?,
        ServerConfig::Sharded => build_sharded_server(empty_client_data)?,
        ServerConfig::Replicated => build_replicated_server(empty_client_data)?,
    };

    platform::simulate_bittide_app(
        &app,
        None, // InspectFn
        cycles,
        platform::AllocationPolicy::OneToOne(platform::MappingConfiguration1x1::default()),
        &mut SystemSimulationCallbacks::default(),
        FailureProperties::default(),
    )?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn get_client_test_data(client_id: usize) -> Option<ClientData> {
        let mut requests = [None as Option<Request>; CLIENT_DATA_SIZE];
        let mut responses = [None as Option<Response>; CLIENT_DATA_SIZE];

        match client_id {
            0 => {
                // client 0 checks only its own operations.
                requests[0] = Some(Request {
                    op: Operation::Insert,
                    key: 20,
                    data: Some([5; DATA_SIZE]),
                });
                // it takes 2 cycles to get an answer back
                responses[2] = Some(Response {
                    op: Operation::Insert,
                    key: 20,
                    data: Some([5; DATA_SIZE]),
                });
                requests[1] = Some(Request {
                    op: Operation::Insert,
                    key: 21,
                    data: Some([6; DATA_SIZE]),
                });
                responses[3] = Some(Response {
                    op: Operation::Insert,
                    key: 21,
                    data: Some([6; DATA_SIZE]),
                });
                requests[2] = Some(Request {
                    op: Operation::Query,
                    key: 20,
                    data: None,
                });
                responses[4] = Some(Response {
                    op: Operation::Query,
                    key: 20,
                    data: Some([5; DATA_SIZE]),
                });
                requests[3] = Some(Request {
                    op: Operation::Query,
                    key: 21,
                    data: None,
                });
                responses[5] = Some(Response {
                    op: Operation::Query,
                    key: 21,
                    data: Some([6; DATA_SIZE]),
                });
                requests[4] = Some(Request {
                    op: Operation::Modify,
                    key: 20,
                    data: Some([7; DATA_SIZE]),
                });
                responses[6] = Some(Response {
                    op: Operation::Modify,
                    key: 20,
                    data: Some([5; DATA_SIZE]),
                });
                requests[5] = Some(Request {
                    op: Operation::Modify,
                    key: 21,
                    data: Some([8; DATA_SIZE]),
                });
                responses[7] = Some(Response {
                    op: Operation::Modify,
                    key: 21,
                    data: Some([6; DATA_SIZE]),
                });
                requests[6] = Some(Request {
                    op: Operation::Query,
                    key: 20,
                    data: None,
                });
                responses[8] = Some(Response {
                    op: Operation::Query,
                    key: 20,
                    data: Some([7; DATA_SIZE]),
                });
                requests[7] = Some(Request {
                    op: Operation::Query,
                    key: 21,
                    data: None,
                });
                responses[9] = Some(Response {
                    op: Operation::Query,
                    key: 21,
                    data: Some([8; DATA_SIZE]),
                });
            }
            _ => {
                // all other clients compete
                requests[0] = Some(Request {
                    op: Operation::Insert,
                    key: 9,
                    data: Some([client_id as u8; DATA_SIZE]),
                });
                // for a single, sequential server, the first client wins insert.
                responses[2] = Some(Response {
                    op: Operation::Insert,
                    key: 9,
                    data: if client_id == 1 {
                        Some([client_id as u8; DATA_SIZE])
                    } else {
                        None
                    },
                });
                // and all the clients should get the same result
                requests[1] = Some(Request {
                    op: Operation::Query,
                    key: 9,
                    data: None,
                });
                responses[3] = Some(Response {
                    op: Operation::Query,
                    key: 9,
                    data: Some([1; DATA_SIZE]),
                });
                // all other clients compete
                requests[2] = Some(Request {
                    op: Operation::Insert,
                    key: 55,
                    data: Some([client_id as u8; DATA_SIZE]),
                });
                // for a single, sequential server, the first client wins insert.
                responses[4] = Some(Response {
                    op: Operation::Insert,
                    key: 55,
                    data: if client_id == 1 {
                        Some([client_id as u8; DATA_SIZE])
                    } else {
                        None
                    },
                });
                // while for modify, the last client wins, but since they
                // all get the old data, they should see the previous
                // modify.
                requests[3] = Some(Request {
                    op: Operation::Modify,
                    key: 55,
                    data: Some([client_id as u8; DATA_SIZE]),
                });
                responses[5] = Some(Response {
                    op: Operation::Modify,
                    key: 55,
                    data: if client_id == 1 {
                        Some([1 as u8; DATA_SIZE])
                    } else {
                        Some([(client_id - 1) as u8; DATA_SIZE])
                    },
                });
                // and all the clients should get the same result
                requests[4] = Some(Request {
                    op: Operation::Query,
                    key: 55,
                    data: None,
                });
                responses[6] = Some(Response {
                    op: Operation::Query,
                    key: 55,
                    data: Some([(CLIENT_COUNT - 1) as u8; DATA_SIZE]),
                });
            }
        }

        Some(ClientData {
            requests,
            responses,
        })
    }

    #[test]
    fn test_single_server() {
        let _logger = env_logger::builder().try_init();
        let app = build_single_server(get_client_test_data).expect("Failed to build app");
        let mut simulation = platform::SoftwareSystemSimulation::new(&app);
        for _ in 0..10 {
            simulation.simulate_system_one_cycle(&app, &mut SystemSimulationCallbacks::default());
        }
    }

    // TODO(cascaval): create the proper data set for sharded config.
    #[ignore]
    #[test]
    fn test_sharded_server() {
        let _logger = env_logger::builder().try_init();
        let app = build_sharded_server(get_client_test_data).expect("Failed to build app");
        let mut simulation = platform::SoftwareSystemSimulation::new(&app);
        for _ in 0..10 {
            simulation.simulate_system_one_cycle(&app, &mut SystemSimulationCallbacks::default());
        }
    }

    // TODO(cascaval): create the proper data set for sharded config.
    #[ignore]
    #[test]
    fn test_replicated_server() {
        let _logger = env_logger::builder().try_init();
        let app = build_replicated_server(get_client_test_data).expect("Failed to build app");
        let mut simulation = platform::SoftwareSystemSimulation::new(&app);
        for _ in 0..10 {
            simulation.simulate_system_one_cycle(&app, &mut SystemSimulationCallbacks::default());
        }
    }
}
