# Financial Exchange

Trading Platform for Goods or Financial Instruments

Status: Draft

Initial date: Apr 7, 2021

Last updated: Feb 13, 2023


## **Goals**

Demonstrate the value of bittide as a platform for microservices by implementing a financial trading exchange. The advantages of bittide are:



*   level playing field:
    *   all participants submitting orders in a given quanta will have their orders processed together, with matching precedence a matter of policy and not mechanism
        *   policies can include various definitions of fairness, differentiated levels of service, etc
    *   all participants see all of the transactions processed during a given quanta at the same time (some future quanta)
*   guaranteed SLAs: number of matches per metacycle (quanta), number of served requests and transactions.
*   minimize the time quanta for issuing requests and computing transactions
    *   orthogonally, show that having deterministic discrete quanta (which existing systems cannot implement) enables new features, like atomic multi-step matching
*   show the simplicity all the way down to hw


## **Problem description**

Implement a microservices pipeline to define a financial exchange.


## **Evolution**

We aim to build the simplest minimally complete system first, and then incrementally add features.  Here are some proposals (not necessarily a linear sequence) for what such an incremental evolution could look like.

**Minimal Sufficient Functionality**



*   single process for the exchange
    *   matching and accounting (and clearing) happens here purely in-memory
*   one process per participant
    *   participants are wired to the exchange with equal delay

composition -- IO ports specifying the size of the per-quanta data exchange



*   exchange update frame:  <code><em>euf</em></code> bits each
    *   contains room for reporting the maximum provisioned number of per-quanta transactions
*   participant update frame:  <code><em>uf_p </em></code>bits, specific to each participant
    *   contains room for the maximum number of bid-ask updates enabled by the provisioning of each participant
*   exchange process data ports:
    *   <code><em>euf</em></code> output (single port, but wired broadcast to all participants)
    *   <code><em>uf_p</em></code> input, per participant
*   participant process data ports:
    *   <code><em>uf_p</em></code> output (single port), <code><em>euf</em></code> input (single port)

<strong>Sharded Exchange</strong>



*   multiple processes for the exchange
    *   each process responsible for a subset of traded goods/instruments
        *   This is a good first draft. But it still has a linear runtime with the number of traders in the system. In the iso-efficiency sense, scalability hasn’t improved (just the constants).
    *   We could split on both dimensions. Each node inputs N traders, trades between them, aggregates the unfilled orders, and acts like a trader itself. This permits an N-ary tree-reduction. The runtime scales with log base N of the number of traders.
    *   matching and accounting still happen purely in-memory
    *   connectivity
        *   processes are wired fully-connected to each other
        *   participants are wired to a subset (number == desired redundancy)
    *   exchange processes need to forward orders to one another
        *   ie participants not directly connected to relevant exchange
        *   multi-step matches potentially require a tour through multiple processes
        *   this impacts the maximum quanta frequency

composition



*   inter-exchange update frame: <code><em>ieuf</em></code> bits each
*   participant process data ports:
    *   output is wired broadcast to connected exchanges
    *   input is interesting:  for redundancy, we want data from each connected exchange;  but this data should be identical;  so logically, we could say that the participant process retains only a single input port, but add a merging stage that looks for inconsistencies (errors) or tolerated failure
*   exchange process data ports:
    *   participant connections unchanged
    *   additional <code><em>ieuf</em></code> input and output ports for each other exchange process

<strong>Redundant Persistent Datastore</strong>



*   compose the exchanges with a distributed consistent datastore service
    *   records accounting data (transaction log, participant portfolios, etc)
    *   wired only to exchanges, not participants
        *   participants still get all of their data from the exchange

datastore service:  _R_ storage replica processes, and _W_ write controller processes



*   reads can be against any replica, they all contain all of the data
*   writes can be against any controller, they propagate to all replicas
    *   each controller is output-wired to all replicas;  all controller-replica connections are equal-delay
*   replica connectivity:
    *   read ports (number of these depends on desired bandwidth;  each port need not be valid on every metacycle which allows limited bandwidth to be spread across multiple clients):  fixed-size address (input) and data (output) pairs;  the data output reflects the data at the address from a fixed-delay prior metacycle
    *   write ports, wired only to controller processes (one port per controller):  port contains fixed size address-plus-data frame (input)
*   controller connectivity:
    *   input ports:  each port has for write address-data frame; number of ports depends on desired bandwidth, need not be always available, just like replica read ports
    *   output ports:  each port for one write address-data frame;  one port for each replica

composition:



*   each exchange wired for datastore read against some subset of replicas (number == desired redundancy;  parameterized)
*   each exchange wired for datastore write against some subset of controllers (again, parameterized redundancy)

system specification -- it seems like we can specify the topology of a system like this with a few parameters, which in turn would tell us what the virtual provision would need to look like (for simulation, etc):



*   number of participant processes
*   number of exchange processes
*   max exchange transactions per quanta
*   for each participant, max bid-ask updates per quanta
*   number of storage replicas
*   number of storage controllers
*   number of replicas read-connected per exchange
*   number of controllers write-connected per exchange

**Reference Algorithms**

Algorithms for matching



*   [Overview](https://corporatefinanceinstitute.com/resources/knowledge/trading-investing/matching-orders/)
*   [List of algorithms](http://web.archive.org/web/20120626161034/http://www.cmegroup.com/confluence/display/EPICSANDBOX/Match+Algorithms)

- Most commonly used algorithms: Price/Time (FIFO) and Pro-Rata

    - time in the bittide case would be meaningful only if orders can not be fulfilled in a time quanta and are left for later. So it seems that Pro-Rata would be more appropriate.

Algorithms:



*   All code examples below generate an order id when an order comes in the exchange. These are supposed to be unique and are also used for sequencing events. For a sharded exchange we need a concurrent solution:
    *   decoupling sequencing because we can use metacycles for sequencing, we could: a) partition the space of ids between shards and then have each shard run a local counter in that space; b) run an agreement algorithm that gives a unique global value; c) use a service (e.g., order database).

- Code

  - [list of matching engines](https://github.com/topics/matching-engine?l=rust) written in Rust

  - a reasonable baseline: https://github.com/dgtony/orderbook-rs, although it seems to implement the price/time algo rather than pro-rata.

  - a more complicated design: https://github.com/viabtc/viabtc\_exchange\_server implemented in Rust in https://github.com/Fluidex/dingir-exchange.



### Components

**Market data**: a distributed key-value store, or even multiple such key-value stores (e.g. Bloomberg, Google Finance, Yahoo Finance, etc).



*   stores information about the market that is used by various participants to make trading decisions.
*   queries or subscribes to the transaction database. The subscription defines the number of transactions that can be updated in one time step.
*   has subscribers (the participants) that also have a level of service defined based on the subscription -- how much data they get at each step.
*   initial implementation will likely have a single instance
*   _demonstrates replicated key-value stores based on synchronous execution without consensus protocols._
*   _potential for demonstrating load balancing using a front-end that directs participants to the nodes that have the requested data._
*   the time the markets observe the transactions may depend on their distance from the transactions database -- is that fair? Even if we chose to broadcast the transactions, the time the txns are observed are defined by the connectivity in the topology. We can guarantee the time when everybody has observed the transaction ...

**Participants [P]**: the traders



*   query the market data to determine what to trade
*   generate a set of requests to the exchange each cycle
*   both queries and requests may be defined as tiers of service -- the initial implementation, will have a single tier?
*   _demonstrated the simplicity of implementing using synchronous execution based on the guaranteed delivery of market data and outputting the requests._
*   how many requests should a trader generate each cycle?
    *   the exchange must publish its ingestion rate. We can divide this equally, by tiers, by credits, or some other mechanism.
    *   what makes it “fair”?

**The exchange**: the market



*   executes trades, i.e., matches requests against each other and generates transactions.
*   there is a defined “ingestion rate”: the number of trades accepted every cycle. This defines both the amount of computation in the matching process and the number of output transactions.
*   transactions are output to the transaction database
*   requests may also be saved in the transaction database (for accountability purposes). Not in the first implementation.
*   the matching algorithm is driven by policies
*   the output transaction rate should be sufficient to issue all the transactions.
*   the matching algorithm guarantees to execute in a defined number of metacycles (each cycle?)
*   _demonstrates “real-time” execution._
*   _in conjunction with policy changes, demonstrates atomic swapping of functionality_
*   _distribute and shard_

**Transactions database [DB]**: the ledger



*   stores transactions (and eventually requests) and publishes them to subscribers
    *   may broadcast (push) or expose a query interface.
    *   should decide whether transactions are sent directly to the parties involved in the transaction.
*   may be a key-value store, but in the long run we want something that is “verifiable” -- benl@’s verifiable ledgers.
*   initially a single node, will be replicated in a later iteration
*   _demonstrates secure, distributed ledgers._

**Policies**: defines  the biases of the exchange:



*   how are the trades made: matching, breaking ties, partials, etc.
*   how is the ingestion rate distributed
*   policies are “revised” periodically and they have to interact with a running exchange. Due to the synchronous nature of the exchange, we should be able to swap policies between two cycles, atomically. There is some complexity involved if we drive the ingestion rate partitioning with a policy, because the policy for that should be active the cycle before the trading policy -- but still orders of magnitude simpler than consensus based.
*   _demonstrates atomic swapping of functionality_
*   _run multiple policies on the same backend if matching is a policy_