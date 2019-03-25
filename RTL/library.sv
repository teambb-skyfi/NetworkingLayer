`default_nettype none

//---- Counter
// Register with count-up capability
module Counter
  #(parameter WIDTH = 4, DEFVAL = 0, INCR = 1)
  (input  logic [WIDTH-1:0] D,
   input  logic             load, up, clk, rst_n,
   output logic [WIDTH-1:0] Q);
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) Q <= DEFVAL;
    else if (load)
        Q <= D;
    else if (up)
      Q <= Q + INCR;
  end
endmodule: Counter

//---- Register
// Stores a value in memory
module Register
  #(parameter WIDTH = 4, DEFVAL = 0)
  (input  logic [WIDTH-1:0] D,
   input  logic             en, clk, rst_n,
   output logic [WIDTH-1:0] Q);

  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) Q <= DEFVAL;
    else if (en) Q <= D;
  end

endmodule : Register

//---- Shift Out Register
// Stores a value in memory that can be "shifted out" (MSB first)
// When shift is asserted, the stored value will be shifted by the width of the
// output so that the new bits can be outputted.
module ShiftOutRegister
  #(parameter INWIDTH = 32, OUTWIDTH = 8, DEFVAL = 0)
  (input  logic [INWIDTH-1:0]  D,
   input  logic                reload, shift, clk, rst_n,
   output logic [OUTWIDTH-1:0] Q);

  logic [INWIDTH-1:0] Q_internal;

  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) Q_internal <= DEFVAL;
    else if (reload) Q_internal <= D;
    else if (shift) Q_internal <= (Q_internal << OUTWIDTH);
  end

  assign Q = Q_internal[INWIDTH-1:INWIDTH-OUTWIDTH];

endmodule : ShiftOutRegister

//---- EdgeDetector
// True if a rise edge occurs
module EdgeDetector
  (input  logic data,
   input  logic clk, rst_n,
   output logic is_edge);
  logic data_last;
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) data_last <= 1'b0;
    else data_last <= data;
  end
  assign is_edge = (data == 1'b1) && (data_last == 1'b0);
endmodule : EdgeDetector

module OppmCounter
  #(L, N)
  (input  logic         start,
   input  logic         clk, rst_n,
   output logic [N-1:0] symbol_id,
   output logic         last_symbol_slot,
   output logic         slot_begin);
  logic start_Q;
  logic run;
  Register #(.WIDTH(1)) startReg(.D(run), .en(1'b1), .Q(start_Q), .*);
  assign run = start_Q | start;

  localparam L_SZ = $clog2(L+1);
  logic [L_SZ-1:0] slot_ct;
  logic            slot_clear, slot_up;
  Counter #(.WIDTH(L_SZ)) slotCounter(.D({L_SZ{1'b0}}), .load(slot_clear),
                                      .up(slot_up), .Q(slot_ct), .*);
  assign slot_clear = (slot_ct == L-1) | !run;
  assign slot_up = (slot_ct != L-1) & run;

  localparam SYMBOL_CT = 2**N - 1;
  localparam SYMBOL_SZ = N;
  logic                 symbol_clear, symbol_up;
  Counter #(.WIDTH(SYMBOL_SZ)) symbolCounter(.D({SYMBOL_SZ{1'b0}}),
                                             .load(symbol_clear),
                                             .up(symbol_up), .Q(symbol_id), .*);

  logic final_symbol;
  assign final_symbol = symbol_id == SYMBOL_CT;

  assign symbol_clear = (slot_clear && final_symbol) | !run;
  assign symbol_up = slot_clear && !final_symbol && run;

  assign last_symbol_slot = symbol_clear;
  assign slot_begin = slot_ct == 0;
endmodule : OppmCounter

//---- Shift In Register
// Stores a value in memory that can be shifted.
// When shift is asserted, the stored value will be shifted by the width of the
// input so that the new bits can be stored. There is no "overflow" checking.
module ShiftInRegister
  #(parameter INWIDTH = 8, OUTWIDTH = 32, DEFVAL = 0)
  (input  logic [INWIDTH-1:0]  D,
   input  logic                reload, shift, clk, rst_n,
   output logic [OUTWIDTH-1:0] Q);

  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n) Q <= DEFVAL;
    else if (reload) Q <= {{OUTWIDTH-INWIDTH{1'b0}}, D};
    else if (shift) Q <= (Q << INWIDTH) | D;
  end

endmodule : ShiftInRegister