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
use specs::ApplicationNode;

use platform::*;

fn forward_action(
    _state: LoopbackRef,
    input: &[InputFrameRef],
    output: &mut [OutputFrameRef],
    _sys: &dyn SystemContext,
) {
    let mut input_val: u64 = 1;

    for inp in input.iter().flatten() {
        input_val = <u64 as Bits>::unpack(&inp.as_bitslice());
        // println!("value read {}", input_val);
    }

    for out in output.iter_mut() {
        (input_val + 1).pack_to(&mut out.data);
        out.valid = true;
        // println!("value written {}", input_val + 1);
    }
}

fn forward(bench: &mut Bencher) {
    const FRAME_SIZE: usize = 64; // bits
    let mut app_spec = Application::new();
    let svc0 = Service::new("svc0", forward_action, None, FrequencyFactor(1));
    let svc1 = Service::new("svc1", forward_action, None, FrequencyFactor(1));
    let n0 = app_spec.add_node(svc0);
    let n1 = app_spec.add_node(svc1);
    let src_port = Port::new(
        0,
        &PortProperties {
            direction: Direction::Outgoing,
            frame_size: FRAME_SIZE.into(),
            framing_lead: FramingLead::Src,
            ..PortProperties::default()
        },
    );
    let dst_port = Port::new(
        0,
        &PortProperties {
            direction: Direction::Incoming,
            frame_size: FRAME_SIZE.into(),
            ..PortProperties::default()
        },
    );
    app_spec.link_simplex_framing(
        n0,
        n1,
        Connection::new(&src_port, &dst_port),
        FramingLead::Src,
    );
    app_spec.link_simplex_framing(
        n1,
        n0,
        Connection::new(&src_port, &dst_port),
        FramingLead::Src,
    );
    // The app-spec needs to specify message sizes on port properties of the Application.
    for node in [n0, n1] {
        app_spec
            .get_node(node)
            .as_ref()
            .borrow_mut()
            .set_ports_properties(&[
                (
                    PortLabel::Number(0),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Incoming,
                        ..Default::default()
                    },
                ),
                (
                    PortLabel::Number(1),
                    PortProperties {
                        frame_size: crate::FrameSize::Number(FRAME_SIZE),
                        direction: Direction::Outgoing,
                        ..Default::default()
                    },
                ),
            ]);
    }

    let cycles: usize = 50000;
    let allocation_policy = AllocationPolicy::OneToOne(MappingConfiguration1x1 {
        frame_size: FRAME_SIZE,
        ..Default::default()
    });
    let system_spec = generate_system_spec(&app_spec, &allocation_policy);
    bench.iter(|| {
        simulate_bittide(
            &system_spec,
            &[&app_spec],
            AllocationPolicy::OneToOne(MappingConfiguration1x1 {
                frame_size: FRAME_SIZE,
                ..Default::default()
            }),
            None,
            cycles,
            &mut SystemSimulationCallbacks::default(),
            FailureProperties::default(),
        )
        .expect("Failed simulation");
    });
    bench.bytes = (FRAME_SIZE / 8 * cycles) as u64;
}

benchmark_group!(benches, forward);
benchmark_main!(benches);
