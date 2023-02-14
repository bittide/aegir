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

#![allow(warnings, unused)]

use bits::*;
use platform::specs::ApplicationNode;
use platform::Application;

waves::action_fn! {
    in_rst
    (state: u32)
    ()
    ->
    (b3_0: bool, b3_1: bool, b3_2: bool, b3_3: bool, b3_4: bool, b3_5: bool, b3_6: bool, b3_7: bool)
    {
        const STIMULUS: [bool; 20] = [
            true,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false,
            false
        ];
        b3_0 = STIMULUS[state as usize];
        b3_1 = STIMULUS[state as usize];
        b3_2 = STIMULUS[state as usize];
        b3_3 = STIMULUS[state as usize];
        b3_4 = STIMULUS[state as usize];
        b3_5 = STIMULUS[state as usize];
        b3_6 = STIMULUS[state as usize];
        b3_7 = STIMULUS[state as usize];
        state = (state + 1) % STIMULUS.len() as u32;
    }
}

waves::action_fn! {
    in_init_count
    (state: u32)
    ()
    ->
    (b4_0: bool, b4_1: bool, b5_0: bool, b5_1: bool, b6_0: bool, b6_1: bool, b7_0: bool, b7_1: bool, b8_0: bool, b8_1: bool, b9_0: bool, b9_1: bool, b10_0: bool, b10_1: bool, b11_0: bool, b11_1: bool)
    {
        const STIMULUS: [u8; 20] = [
            5,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0,
            0
        ];
        b4_0 = ((STIMULUS[state as usize] >> 0) & 1) != 0;
        b4_1 = ((STIMULUS[state as usize] >> 0) & 1) != 0;
        b5_0 = ((STIMULUS[state as usize] >> 1) & 1) != 0;
        b5_1 = ((STIMULUS[state as usize] >> 1) & 1) != 0;
        b6_0 = ((STIMULUS[state as usize] >> 2) & 1) != 0;
        b6_1 = ((STIMULUS[state as usize] >> 2) & 1) != 0;
        b7_0 = ((STIMULUS[state as usize] >> 3) & 1) != 0;
        b7_1 = ((STIMULUS[state as usize] >> 3) & 1) != 0;
        b8_0 = ((STIMULUS[state as usize] >> 4) & 1) != 0;
        b8_1 = ((STIMULUS[state as usize] >> 4) & 1) != 0;
        b9_0 = ((STIMULUS[state as usize] >> 5) & 1) != 0;
        b9_1 = ((STIMULUS[state as usize] >> 5) & 1) != 0;
        b10_0 = ((STIMULUS[state as usize] >> 6) & 1) != 0;
        b10_1 = ((STIMULUS[state as usize] >> 6) & 1) != 0;
        b11_0 = ((STIMULUS[state as usize] >> 7) & 1) != 0;
        b11_1 = ((STIMULUS[state as usize] >> 7) & 1) != 0;
        state = (state + 1) % STIMULUS.len() as u32;
    }
}

waves::action_fn! {
    out_count
    (state: u8)
    (b12: Option<bool>, b13: Option<bool>, b14: Option<bool>, b15: Option<bool>, b16: Option<bool>, b17: Option<bool>, b18: Option<bool>, b19: Option<bool>)
    ->
    ()
    {

        state = 0;
        state |= u8::from(b12.unwrap_or(false)) << 0;
        state |= u8::from(b13.unwrap_or(false)) << 1;
        state |= u8::from(b14.unwrap_or(false)) << 2;
        state |= u8::from(b15.unwrap_or(false)) << 3;
        state |= u8::from(b16.unwrap_or(false)) << 4;
        state |= u8::from(b17.unwrap_or(false)) << 5;
        state |= u8::from(b18.unwrap_or(false)) << 6;
        state |= u8::from(b19.unwrap_or(false)) << 7;
    }
}

waves::action_fn! {
    out_count_inv
    (state: u8)
    (b12: Option<bool>, b13: Option<bool>, b14: Option<bool>, b15: Option<bool>, b16: Option<bool>, b17: Option<bool>, b18: Option<bool>, b19: Option<bool>)
    ->
    ()
    {
        let b20 = !b12.unwrap_or(false);
        let b21 = !b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b23 = !b15.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b25 = !b17.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b27 = !b19.unwrap_or(false);
        state = 0;
        state |= u8::from(b20) << 0;
        state |= u8::from(b21) << 1;
        state |= u8::from(b22) << 2;
        state |= u8::from(b23) << 3;
        state |= u8::from(b24) << 4;
        state |= u8::from(b25) << 5;
        state |= u8::from(b26) << 6;
        state |= u8::from(b27) << 7;
    }
}

waves::action_fn! {
    out_init_count_out
    (state: u8)
    (b4: Option<bool>, b5: Option<bool>, b6: Option<bool>, b7: Option<bool>, b8: Option<bool>, b9: Option<bool>, b10: Option<bool>, b11: Option<bool>)
    ->
    ()
    {

        state = 0;
        state |= u8::from(b4.unwrap_or(false)) << 0;
        state |= u8::from(b5.unwrap_or(false)) << 1;
        state |= u8::from(b6.unwrap_or(false)) << 2;
        state |= u8::from(b7.unwrap_or(false)) << 3;
        state |= u8::from(b8.unwrap_or(false)) << 4;
        state |= u8::from(b9.unwrap_or(false)) << 5;
        state |= u8::from(b10.unwrap_or(false)) << 6;
        state |= u8::from(b11.unwrap_or(false)) << 7;
    }
}

waves::action_fn! {
    reg_b12
    (state: bool)
    (b3: Option<bool>, b4: Option<bool>, b13: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b12_0: bool, b12_1: bool, b12_2: bool, b12_3: bool, b12_4: bool, b12_5: bool, b12_6: bool, b12_7: bool, b12_8: bool)
    {
        let b12 = state;
        let b46 = b3.unwrap_or(false) && b4.unwrap_or(false);
        let b50 = !b46;
        let b20 = !b12;
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12;
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b95 = b31 && b12;
        let b97 = !b95;
        let b20 = !b12;
        let b20 = !b12;
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12;
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b96 = b20 && b30;
        let b98 = !b96;
        let b99 = b97 && b98;
        let b47 = !b99;
        let b48 = !b3.unwrap_or(false);
        let b49 = b47 && b48;
        let b51 = !b49;
        let b52 = b50 && b51;
        let b200 = !b52;
        state = b200;
        b12_0 = state;
        b12_1 = state;
        b12_2 = state;
        b12_3 = state;
        b12_4 = state;
        b12_5 = state;
        b12_6 = state;
        b12_7 = state;
        b12_8 = state;
    }
}

waves::action_fn! {
    reg_b13
    (state: bool)
    (b3: Option<bool>, b5: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b13_0: bool, b13_1: bool, b13_2: bool, b13_3: bool, b13_4: bool, b13_5: bool, b13_6: bool, b13_7: bool, b13_8: bool)
    {
        let b13 = state;
        let b53 = b3.unwrap_or(false) && b5.unwrap_or(false);
        let b56 = !b53;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13;
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b100 = b31 && b13;
        let b103 = !b100;
        let b20 = !b12.unwrap_or(false);
        let b21 = !b13;
        let b162 = b20 && b21;
        let b164 = !b162;
        let b163 = b13 && b12.unwrap_or(false);
        let b165 = !b163;
        let b101 = b164 && b165;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13;
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b102 = b101 && b30;
        let b104 = !b102;
        let b105 = b103 && b104;
        let b54 = !b105;
        let b48 = !b3.unwrap_or(false);
        let b55 = b54 && b48;
        let b57 = !b55;
        let b58 = b56 && b57;
        let b201 = !b58;
        state = b201;
        b13_0 = state;
        b13_1 = state;
        b13_2 = state;
        b13_3 = state;
        b13_4 = state;
        b13_5 = state;
        b13_6 = state;
        b13_7 = state;
        b13_8 = state;
    }
}

waves::action_fn! {
    reg_b14
    (state: bool)
    (b3: Option<bool>, b6: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b14_0: bool, b14_1: bool, b14_2: bool, b14_3: bool, b14_4: bool, b14_5: bool, b14_6: bool, b14_7: bool, b14_8: bool)
    {
        let b14 = state;
        let b59 = b3.unwrap_or(false) && b6.unwrap_or(false);
        let b62 = !b59;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14;
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b106 = b31 && b14;
        let b109 = !b106;
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b165 = !b163;
        let b22 = !b14;
        let b166 = b165 && b22;
        let b168 = !b166;
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b167 = b14 && b163;
        let b169 = !b167;
        let b107 = b168 && b169;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14;
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14;
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b108 = b107 && b30;
        let b110 = !b108;
        let b111 = b109 && b110;
        let b60 = !b111;
        let b48 = !b3.unwrap_or(false);
        let b61 = b60 && b48;
        let b63 = !b61;
        let b64 = b62 && b63;
        let b202 = !b64;
        state = b202;
        b14_0 = state;
        b14_1 = state;
        b14_2 = state;
        b14_3 = state;
        b14_4 = state;
        b14_5 = state;
        b14_6 = state;
        b14_7 = state;
        b14_8 = state;
    }
}

waves::action_fn! {
    reg_b15
    (state: bool)
    (b3: Option<bool>, b7: Option<bool>, b13: Option<bool>, b12: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b15_0: bool, b15_1: bool, b15_2: bool, b15_3: bool, b15_4: bool, b15_5: bool, b15_6: bool, b15_7: bool, b15_8: bool)
    {
        let b15 = state;
        let b65 = b3.unwrap_or(false) && b7.unwrap_or(false);
        let b68 = !b65;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15 && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b23 = !b15;
        let b112 = b31 && b23;
        let b115 = !b112;
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b167 = b14.unwrap_or(false) && b163;
        let b169 = !b167;
        let b23 = !b15;
        let b170 = b169 && b23;
        let b172 = !b170;
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b167 = b14.unwrap_or(false) && b163;
        let b171 = b15 && b167;
        let b173 = !b171;
        let b113 = b172 && b173;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15 && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15 && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b114 = b113 && b30;
        let b116 = !b114;
        let b117 = b115 && b116;
        let b66 = !b117;
        let b48 = !b3.unwrap_or(false);
        let b67 = b66 && b48;
        let b69 = !b67;
        let b70 = b68 && b69;
        let b203 = !b70;
        state = b203;
        b15_0 = state;
        b15_1 = state;
        b15_2 = state;
        b15_3 = state;
        b15_4 = state;
        b15_5 = state;
        b15_6 = state;
        b15_7 = state;
        b15_8 = state;
    }
}

waves::action_fn! {
    reg_b16
    (state: bool)
    (b3: Option<bool>, b8: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>)
    ->
    (b16_0: bool, b16_1: bool, b16_2: bool, b16_3: bool, b16_4: bool, b16_5: bool, b16_6: bool, b16_7: bool, b16_8: bool)
    {
        let b16 = state;
        let b71 = b3.unwrap_or(false) && b8.unwrap_or(false);
        let b74 = !b71;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16;
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b146 = b136 && b16;
        let b149 = !b146;
        let b24 = !b16;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b148 = b24 && b147;
        let b140 = !b148;
        let b118 = b149 && b140;
        let b119 = b31 && b118;
        let b122 = !b119;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b174 = !b215;
        let b24 = !b16;
        let b175 = b174 && b24;
        let b176 = !b175;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b179 = b16 && b215;
        let b177 = !b179;
        let b120 = b176 && b177;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16;
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16;
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b121 = b120 && b30;
        let b123 = !b121;
        let b124 = b122 && b123;
        let b72 = !b124;
        let b48 = !b3.unwrap_or(false);
        let b73 = b72 && b48;
        let b75 = !b73;
        let b76 = b74 && b75;
        let b204 = !b76;
        state = b204;
        b16_0 = state;
        b16_1 = state;
        b16_2 = state;
        b16_3 = state;
        b16_4 = state;
        b16_5 = state;
        b16_6 = state;
        b16_7 = state;
        b16_8 = state;
    }
}

waves::action_fn! {
    reg_b17
    (state: bool)
    (b3: Option<bool>, b9: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b16: Option<bool>)
    ->
    (b17_0: bool, b17_1: bool, b17_2: bool, b17_3: bool, b17_4: bool, b17_5: bool, b17_6: bool, b17_7: bool, b17_8: bool)
    {
        let b17 = state;
        let b77 = b3.unwrap_or(false) && b9.unwrap_or(false);
        let b80 = !b77;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17;
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b24 = !b16.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b148 = b24 && b147;
        let b140 = !b148;
        let b24 = !b16.unwrap_or(false);
        let b141 = b140 && b24;
        let b150 = b141 && b17;
        let b153 = !b150;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b148 = b24 && b147;
        let b140 = !b148;
        let b24 = !b16.unwrap_or(false);
        let b141 = b140 && b24;
        let b151 = !b141;
        let b152 = b25 && b151;
        let b154 = !b152;
        let b125 = b153 && b154;
        let b126 = b31 && b125;
        let b129 = !b126;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b179 = b16.unwrap_or(false) && b215;
        let b177 = !b179;
        let b25 = !b17;
        let b178 = b177 && b25;
        let b181 = !b178;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b179 = b16.unwrap_or(false) && b215;
        let b180 = b17 && b179;
        let b182 = !b180;
        let b127 = b181 && b182;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17;
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17;
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b128 = b127 && b30;
        let b130 = !b128;
        let b131 = b129 && b130;
        let b78 = !b131;
        let b48 = !b3.unwrap_or(false);
        let b79 = b78 && b48;
        let b81 = !b79;
        let b82 = b80 && b81;
        let b205 = !b82;
        state = b205;
        b17_0 = state;
        b17_1 = state;
        b17_2 = state;
        b17_3 = state;
        b17_4 = state;
        b17_5 = state;
        b17_6 = state;
        b17_7 = state;
        b17_8 = state;
    }
}

waves::action_fn! {
    reg_b18
    (state: bool)
    (b3: Option<bool>, b10: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b18_0: bool, b18_1: bool, b18_2: bool, b18_3: bool, b18_4: bool, b18_5: bool, b18_6: bool, b18_7: bool, b18_8: bool)
    {
        let b18 = state;
        let b83 = b3.unwrap_or(false) && b10.unwrap_or(false);
        let b86 = !b83;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18;
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b211 = b225 && b147;
        let b137 = !b211;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b139 = b137 && b138;
        let b155 = b139 && b18;
        let b156 = !b155;
        let b26 = !b18;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b211 = b225 && b147;
        let b137 = !b211;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b139 = b137 && b138;
        let b212 = !b139;
        let b214 = b26 && b212;
        let b142 = !b214;
        let b32 = b156 && b142;
        let b33 = b31 && b32;
        let b36 = !b33;
        let b227 = b17.unwrap_or(false) && b16.unwrap_or(false);
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b185 = b227 && b215;
        let b183 = !b185;
        let b26 = !b18;
        let b184 = b183 && b26;
        let b187 = !b184;
        let b227 = b17.unwrap_or(false) && b16.unwrap_or(false);
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b185 = b227 && b215;
        let b186 = b18 && b185;
        let b188 = !b186;
        let b34 = b187 && b188;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19.unwrap_or(false);
        let b26 = !b18;
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19.unwrap_or(false);
        let b208 = b27 && b18;
        let b132 = !b208;
        let b27 = !b19.unwrap_or(false);
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b35 = b34 && b30;
        let b37 = !b35;
        let b38 = b36 && b37;
        let b84 = !b38;
        let b48 = !b3.unwrap_or(false);
        let b85 = b84 && b48;
        let b87 = !b85;
        let b88 = b86 && b87;
        let b206 = !b88;
        state = b206;
        b18_0 = state;
        b18_1 = state;
        b18_2 = state;
        b18_3 = state;
        b18_4 = state;
        b18_5 = state;
        b18_6 = state;
        b18_7 = state;
        b18_8 = state;
    }
}

waves::action_fn! {
    reg_b19
    (state: bool)
    (b3: Option<bool>, b11: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
    ->
    (b19_0: bool, b19_1: bool, b19_2: bool, b19_3: bool, b19_4: bool, b19_5: bool, b19_6: bool, b19_7: bool, b19_8: bool)
    {
        let b19 = state;
        let b89 = b3.unwrap_or(false) && b11.unwrap_or(false);
        let b92 = !b89;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19;
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19;
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b31 = !b30;
        let b26 = !b18.unwrap_or(false);
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b211 = b225 && b147;
        let b137 = !b211;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b139 = b137 && b138;
        let b212 = !b139;
        let b214 = b26 && b212;
        let b142 = !b214;
        let b26 = !b18.unwrap_or(false);
        let b143 = b142 && b26;
        let b157 = b143 && b19;
        let b160 = !b157;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b134 = !b209;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b136 = b134 && b135;
        let b147 = !b136;
        let b211 = b225 && b147;
        let b137 = !b211;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b139 = b137 && b138;
        let b212 = !b139;
        let b214 = b26 && b212;
        let b142 = !b214;
        let b26 = !b18.unwrap_or(false);
        let b143 = b142 && b26;
        let b158 = !b143;
        let b159 = b27 && b158;
        let b161 = !b159;
        let b39 = b160 && b161;
        let b40 = b31 && b39;
        let b43 = !b40;
        let b227 = b17.unwrap_or(false) && b16.unwrap_or(false);
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b185 = b227 && b215;
        let b186 = b18.unwrap_or(false) && b185;
        let b188 = !b186;
        let b27 = !b19;
        let b189 = b188 && b27;
        let b191 = !b189;
        let b227 = b17.unwrap_or(false) && b16.unwrap_or(false);
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b163 = b13.unwrap_or(false) && b12.unwrap_or(false);
        let b215 = b210 && b163;
        let b185 = b227 && b215;
        let b186 = b18.unwrap_or(false) && b185;
        let b190 = b19 && b186;
        let b192 = !b190;
        let b41 = b191 && b192;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b20 = !b12.unwrap_or(false);
        let b222 = b20 && b13.unwrap_or(false);
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b223 = b222 && b209;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b213 = b223 && b224;
        let b28 = !b213;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b24 = !b16.unwrap_or(false);
        let b225 = b25 && b24;
        let b224 = b226 && b225;
        let b22 = !b14.unwrap_or(false);
        let b209 = b15.unwrap_or(false) && b22;
        let b218 = b209 && b13.unwrap_or(false);
        let b194 = !b218;
        let b210 = b15.unwrap_or(false) && b14.unwrap_or(false);
        let b135 = !b210;
        let b195 = b194 && b135;
        let b219 = !b195;
        let b221 = b224 && b219;
        let b198 = !b221;
        let b27 = !b19;
        let b26 = !b18.unwrap_or(false);
        let b226 = b27 && b26;
        let b25 = !b17.unwrap_or(false);
        let b216 = b25 && b16.unwrap_or(false);
        let b193 = !b216;
        let b25 = !b17.unwrap_or(false);
        let b138 = b193 && b25;
        let b217 = !b138;
        let b220 = b226 && b217;
        let b196 = !b220;
        let b27 = !b19;
        let b208 = b27 && b18.unwrap_or(false);
        let b132 = !b208;
        let b27 = !b19;
        let b133 = b132 && b27;
        let b197 = b196 && b133;
        let b199 = b198 && b197;
        let b144 = !b199;
        let b145 = b28 && b144;
        let b29 = !b145;
        let b30 = b28 && b29;
        let b42 = b41 && b30;
        let b44 = !b42;
        let b45 = b43 && b44;
        let b90 = !b45;
        let b48 = !b3.unwrap_or(false);
        let b91 = b90 && b48;
        let b93 = !b91;
        let b94 = b92 && b93;
        let b207 = !b94;
        state = b207;
        b19_0 = state;
        b19_1 = state;
        b19_2 = state;
        b19_3 = state;
        b19_4 = state;
        b19_5 = state;
        b19_6 = state;
        b19_7 = state;
        b19_8 = state;
    }
}

pub fn build_app() -> Application {
    let mut app_spec = Application::new();
    let in_rst = waves::action!("in_rst" in app_spec
        (state: u32)
        ()
        ->
        (b3_0: bool, b3_1: bool, b3_2: bool, b3_3: bool, b3_4: bool, b3_5: bool, b3_6: bool, b3_7: bool)
        { u32::pack(&0).into_boxed_bitslice() }
        in_rst);
    let in_init_count = waves::action!("in_init_count" in app_spec
        (state: u32)
        ()
        ->
        (b4_0: bool, b4_1: bool, b5_0: bool, b5_1: bool, b6_0: bool, b6_1: bool, b7_0: bool, b7_1: bool, b8_0: bool, b8_1: bool, b9_0: bool, b9_1: bool, b10_0: bool, b10_1: bool, b11_0: bool, b11_1: bool)
        { u32::pack(&0).into_boxed_bitslice() }
        in_init_count);
    let reg_b12 = waves::action!("reg_b12" in app_spec
        (state: bool)
        (b3: Option<bool>, b4: Option<bool>, b13: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b12_0: bool, b12_1: bool, b12_2: bool, b12_3: bool, b12_4: bool, b12_5: bool, b12_6: bool, b12_7: bool, b12_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b12);
    let reg_b13 = waves::action!("reg_b13" in app_spec
        (state: bool)
        (b3: Option<bool>, b5: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b13_0: bool, b13_1: bool, b13_2: bool, b13_3: bool, b13_4: bool, b13_5: bool, b13_6: bool, b13_7: bool, b13_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b13);
    let reg_b14 = waves::action!("reg_b14" in app_spec
        (state: bool)
        (b3: Option<bool>, b6: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b14_0: bool, b14_1: bool, b14_2: bool, b14_3: bool, b14_4: bool, b14_5: bool, b14_6: bool, b14_7: bool, b14_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b14);
    let reg_b15 = waves::action!("reg_b15" in app_spec
        (state: bool)
        (b3: Option<bool>, b7: Option<bool>, b13: Option<bool>, b12: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b15_0: bool, b15_1: bool, b15_2: bool, b15_3: bool, b15_4: bool, b15_5: bool, b15_6: bool, b15_7: bool, b15_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b15);
    let reg_b16 = waves::action!("reg_b16" in app_spec
        (state: bool)
        (b3: Option<bool>, b8: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b17: Option<bool>)
        -> 
        (b16_0: bool, b16_1: bool, b16_2: bool, b16_3: bool, b16_4: bool, b16_5: bool, b16_6: bool, b16_7: bool, b16_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b16);
    let reg_b17 = waves::action!("reg_b17" in app_spec
        (state: bool)
        (b3: Option<bool>, b9: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b18: Option<bool>, b16: Option<bool>)
        -> 
        (b17_0: bool, b17_1: bool, b17_2: bool, b17_3: bool, b17_4: bool, b17_5: bool, b17_6: bool, b17_7: bool, b17_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b17);
    let reg_b18 = waves::action!("reg_b18" in app_spec
        (state: bool)
        (b3: Option<bool>, b10: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b19: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b18_0: bool, b18_1: bool, b18_2: bool, b18_3: bool, b18_4: bool, b18_5: bool, b18_6: bool, b18_7: bool, b18_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b18);
    let reg_b19 = waves::action!("reg_b19" in app_spec
        (state: bool)
        (b3: Option<bool>, b11: Option<bool>, b13: Option<bool>, b12: Option<bool>, b15: Option<bool>, b14: Option<bool>, b18: Option<bool>, b17: Option<bool>, b16: Option<bool>)
        -> 
        (b19_0: bool, b19_1: bool, b19_2: bool, b19_3: bool, b19_4: bool, b19_5: bool, b19_6: bool, b19_7: bool, b19_8: bool)
        { bool::pack(&false).into_boxed_bitslice() }
        reg_b19);
    let out_count = waves::action!("out_count" in app_spec
        (state: u8)
        (b12: Option<bool>, b13: Option<bool>, b14: Option<bool>, b15: Option<bool>, b16: Option<bool>, b17: Option<bool>, b18: Option<bool>, b19: Option<bool>)
        -> 
        ()
        { u8::pack(&0).into_boxed_bitslice() }
        out_count);
    let out_count_inv = waves::action!("out_count_inv" in app_spec
        (state: u8)
        (b12: Option<bool>, b13: Option<bool>, b14: Option<bool>, b15: Option<bool>, b16: Option<bool>, b17: Option<bool>, b18: Option<bool>, b19: Option<bool>)
        -> 
        ()
        { u8::pack(&0).into_boxed_bitslice() }
        out_count_inv);
    let out_init_count_out = waves::action!("out_init_count_out" in app_spec
        (state: u8)
        (b4: Option<bool>, b5: Option<bool>, b6: Option<bool>, b7: Option<bool>, b8: Option<bool>, b9: Option<bool>, b10: Option<bool>, b11: Option<bool>)
        -> 
        ()
        { u8::pack(&0).into_boxed_bitslice() }
        out_init_count_out);
    waves::link!(in_rst b3_0 -> reg_b12 b3 in app_spec);
    waves::link!(in_init_count b4_0 -> reg_b12 b4 in app_spec);
    waves::link!(reg_b13 b13_0 -> reg_b12 b13 in app_spec);
    waves::link!(reg_b15 b15_0 -> reg_b12 b15 in app_spec);
    waves::link!(reg_b14 b14_0 -> reg_b12 b14 in app_spec);
    waves::link!(reg_b19 b19_0 -> reg_b12 b19 in app_spec);
    waves::link!(reg_b18 b18_0 -> reg_b12 b18 in app_spec);
    waves::link!(reg_b17 b17_0 -> reg_b12 b17 in app_spec);
    waves::link!(reg_b16 b16_0 -> reg_b12 b16 in app_spec);
    waves::link!(in_rst b3_1 -> reg_b13 b3 in app_spec);
    waves::link!(in_init_count b5_0 -> reg_b13 b5 in app_spec);
    waves::link!(reg_b12 b12_0 -> reg_b13 b12 in app_spec);
    waves::link!(reg_b15 b15_1 -> reg_b13 b15 in app_spec);
    waves::link!(reg_b14 b14_1 -> reg_b13 b14 in app_spec);
    waves::link!(reg_b19 b19_1 -> reg_b13 b19 in app_spec);
    waves::link!(reg_b18 b18_1 -> reg_b13 b18 in app_spec);
    waves::link!(reg_b17 b17_1 -> reg_b13 b17 in app_spec);
    waves::link!(reg_b16 b16_1 -> reg_b13 b16 in app_spec);
    waves::link!(in_rst b3_2 -> reg_b14 b3 in app_spec);
    waves::link!(in_init_count b6_0 -> reg_b14 b6 in app_spec);
    waves::link!(reg_b13 b13_1 -> reg_b14 b13 in app_spec);
    waves::link!(reg_b12 b12_1 -> reg_b14 b12 in app_spec);
    waves::link!(reg_b15 b15_2 -> reg_b14 b15 in app_spec);
    waves::link!(reg_b19 b19_2 -> reg_b14 b19 in app_spec);
    waves::link!(reg_b18 b18_2 -> reg_b14 b18 in app_spec);
    waves::link!(reg_b17 b17_2 -> reg_b14 b17 in app_spec);
    waves::link!(reg_b16 b16_2 -> reg_b14 b16 in app_spec);
    waves::link!(in_rst b3_3 -> reg_b15 b3 in app_spec);
    waves::link!(in_init_count b7_0 -> reg_b15 b7 in app_spec);
    waves::link!(reg_b13 b13_2 -> reg_b15 b13 in app_spec);
    waves::link!(reg_b12 b12_2 -> reg_b15 b12 in app_spec);
    waves::link!(reg_b14 b14_2 -> reg_b15 b14 in app_spec);
    waves::link!(reg_b19 b19_3 -> reg_b15 b19 in app_spec);
    waves::link!(reg_b18 b18_3 -> reg_b15 b18 in app_spec);
    waves::link!(reg_b17 b17_3 -> reg_b15 b17 in app_spec);
    waves::link!(reg_b16 b16_3 -> reg_b15 b16 in app_spec);
    waves::link!(in_rst b3_4 -> reg_b16 b3 in app_spec);
    waves::link!(in_init_count b8_0 -> reg_b16 b8 in app_spec);
    waves::link!(reg_b13 b13_3 -> reg_b16 b13 in app_spec);
    waves::link!(reg_b12 b12_3 -> reg_b16 b12 in app_spec);
    waves::link!(reg_b15 b15_3 -> reg_b16 b15 in app_spec);
    waves::link!(reg_b14 b14_3 -> reg_b16 b14 in app_spec);
    waves::link!(reg_b19 b19_4 -> reg_b16 b19 in app_spec);
    waves::link!(reg_b18 b18_4 -> reg_b16 b18 in app_spec);
    waves::link!(reg_b17 b17_4 -> reg_b16 b17 in app_spec);
    waves::link!(in_rst b3_5 -> reg_b17 b3 in app_spec);
    waves::link!(in_init_count b9_0 -> reg_b17 b9 in app_spec);
    waves::link!(reg_b13 b13_4 -> reg_b17 b13 in app_spec);
    waves::link!(reg_b12 b12_4 -> reg_b17 b12 in app_spec);
    waves::link!(reg_b15 b15_4 -> reg_b17 b15 in app_spec);
    waves::link!(reg_b14 b14_4 -> reg_b17 b14 in app_spec);
    waves::link!(reg_b19 b19_5 -> reg_b17 b19 in app_spec);
    waves::link!(reg_b18 b18_5 -> reg_b17 b18 in app_spec);
    waves::link!(reg_b16 b16_4 -> reg_b17 b16 in app_spec);
    waves::link!(in_rst b3_6 -> reg_b18 b3 in app_spec);
    waves::link!(in_init_count b10_0 -> reg_b18 b10 in app_spec);
    waves::link!(reg_b13 b13_5 -> reg_b18 b13 in app_spec);
    waves::link!(reg_b12 b12_5 -> reg_b18 b12 in app_spec);
    waves::link!(reg_b15 b15_5 -> reg_b18 b15 in app_spec);
    waves::link!(reg_b14 b14_5 -> reg_b18 b14 in app_spec);
    waves::link!(reg_b19 b19_6 -> reg_b18 b19 in app_spec);
    waves::link!(reg_b17 b17_5 -> reg_b18 b17 in app_spec);
    waves::link!(reg_b16 b16_5 -> reg_b18 b16 in app_spec);
    waves::link!(in_rst b3_7 -> reg_b19 b3 in app_spec);
    waves::link!(in_init_count b11_0 -> reg_b19 b11 in app_spec);
    waves::link!(reg_b13 b13_6 -> reg_b19 b13 in app_spec);
    waves::link!(reg_b12 b12_6 -> reg_b19 b12 in app_spec);
    waves::link!(reg_b15 b15_6 -> reg_b19 b15 in app_spec);
    waves::link!(reg_b14 b14_6 -> reg_b19 b14 in app_spec);
    waves::link!(reg_b18 b18_6 -> reg_b19 b18 in app_spec);
    waves::link!(reg_b17 b17_6 -> reg_b19 b17 in app_spec);
    waves::link!(reg_b16 b16_6 -> reg_b19 b16 in app_spec);
    waves::link!(reg_b12 b12_7 -> out_count b12 in app_spec);
    waves::link!(reg_b13 b13_7 -> out_count b13 in app_spec);
    waves::link!(reg_b14 b14_7 -> out_count b14 in app_spec);
    waves::link!(reg_b15 b15_7 -> out_count b15 in app_spec);
    waves::link!(reg_b16 b16_7 -> out_count b16 in app_spec);
    waves::link!(reg_b17 b17_7 -> out_count b17 in app_spec);
    waves::link!(reg_b18 b18_7 -> out_count b18 in app_spec);
    waves::link!(reg_b19 b19_7 -> out_count b19 in app_spec);
    waves::link!(reg_b12 b12_8 -> out_count_inv b12 in app_spec);
    waves::link!(reg_b13 b13_8 -> out_count_inv b13 in app_spec);
    waves::link!(reg_b14 b14_8 -> out_count_inv b14 in app_spec);
    waves::link!(reg_b15 b15_8 -> out_count_inv b15 in app_spec);
    waves::link!(reg_b16 b16_8 -> out_count_inv b16 in app_spec);
    waves::link!(reg_b17 b17_8 -> out_count_inv b17 in app_spec);
    waves::link!(reg_b18 b18_8 -> out_count_inv b18 in app_spec);
    waves::link!(reg_b19 b19_8 -> out_count_inv b19 in app_spec);
    waves::link!(in_init_count b4_1 -> out_init_count_out b4 in app_spec);
    waves::link!(in_init_count b5_1 -> out_init_count_out b5 in app_spec);
    waves::link!(in_init_count b6_1 -> out_init_count_out b6 in app_spec);
    waves::link!(in_init_count b7_1 -> out_init_count_out b7 in app_spec);
    waves::link!(in_init_count b8_1 -> out_init_count_out b8 in app_spec);
    waves::link!(in_init_count b9_1 -> out_init_count_out b9 in app_spec);
    waves::link!(in_init_count b10_1 -> out_init_count_out b10 in app_spec);
    waves::link!(in_init_count b11_1 -> out_init_count_out b11 in app_spec);
    app_spec
}
