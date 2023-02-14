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

use bencher::Bencher;
use bencher::{benchmark_group, benchmark_main};
use bits::Bits;

use platform::Buffering;
use platform::DataWithValidity;
use platform::IOCalendarVariant;
use platform::IOConfig;
use platform::BUFFERING_DOUBLE;
use platform::BUFFERING_SINGLE;
use platform::{CalendarEntry, GatherEngine, ScatterEngine, SystemSimulationCallbacks};

// number of frames to test on: in principle we want this to be larger than
// RX/TX_MEM_CAPACITY
const FRAMES: usize = 1000000;

type Frame = u32;
const FRAME_SIZE_BYTES: usize = std::mem::size_of::<Frame>();
const FRAME_SIZE_BITS: usize = FRAME_SIZE_BYTES * 8;
const CALENDAR_CAPACITY: usize = 1024;
const RX_MEM_CAPACITY: usize = 256;
const TX_MEM_CAPACITY: usize = 256;

fn scatter<const BUFFERING: Buffering>(bench: &mut Bencher) {
    // TODO(cascaval): iterate through multiple data sizes
    let i0 = Frame::pack(&0xcafebabe).into_boxed_bitslice();

    let mut scatter = ScatterEngine::<BUFFERING>::new(
        FRAME_SIZE_BITS,
        RX_MEM_CAPACITY,
        CALENDAR_CAPACITY,
        IOConfig::ComputeIO,
    );
    // a calendar for which each entry sweeps sweeps the entire memory
    let calendar = vec![CalendarEntry::new(Some(0), RX_MEM_CAPACITY); CALENDAR_CAPACITY];
    scatter.set_calendar(IOCalendarVariant::Input(
        [(); BUFFERING].map(|_| calendar.clone()),
    ));

    bench.iter(|| {
        for _ in 0..FRAMES {
            let _ = scatter.step(Some(&i0), &mut SystemSimulationCallbacks::default());
        }
    });
    bench.bytes = (FRAMES * FRAME_SIZE_BYTES) as u64;
}

fn gather<const BUFFERING: Buffering>(bench: &mut Bencher) {
    // TODO(cascaval): iterate through multiple data sizes
    let mut output = DataWithValidity {
        data: Frame::pack(&0xdeadbeef).into_boxed_bitslice(),
        valid: true,
    };

    let mut gather = GatherEngine::<BUFFERING>::new(
        FRAME_SIZE_BITS,
        TX_MEM_CAPACITY,
        CALENDAR_CAPACITY,
        IOConfig::ComputeIO,
    );
    // a calendar for which each entry sweeps sweeps the entire memory
    let calendar = vec![CalendarEntry::new(Some(0), TX_MEM_CAPACITY); CALENDAR_CAPACITY];
    gather.set_calendar(IOCalendarVariant::Output(
        [(); BUFFERING].map(|_| calendar.clone()),
    ));

    bench.iter(|| {
        for _ in 0..FRAMES {
            let _ = gather.step(&mut output, &mut SystemSimulationCallbacks::default());
        }
    });
    bench.bytes = (FRAMES * FRAME_SIZE_BYTES) as u64;
}

benchmark_group!(
    benches_double,
    scatter<{ BUFFERING_SINGLE }>,
    gather<{ BUFFERING_SINGLE }>
);
benchmark_group!(
    benches_single,
    scatter<{ BUFFERING_DOUBLE }>,
    gather<{ BUFFERING_DOUBLE }>
);
benchmark_main!(benches_double, benches_single);
