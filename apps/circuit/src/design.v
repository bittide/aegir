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

module counter #(parameter W = 8) (
    input clk, rst,
    input [W - 1:0] init_count,
    output reg [W - 1:0] count,
    output reg [W - 1:0] count_inv,
    output reg [W - 1:0] init_count_out);

    reg [W - 1:0] next_count;
    always @(posedge clk)
        if (rst)
            count <= init_count;
        else
            count <= next_count;

    always @(*) begin
        if (count >= 10)
            next_count = count - 8;
        else
            next_count = count + 1;

        count_inv = ~count;
        init_count_out = init_count;
    end

endmodule // counter
