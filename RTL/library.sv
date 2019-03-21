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

//---- Shift Register
// Stores a value in memory that can be shifted (PISO variant).
// When shift is asserted, the stored value will be shifted by the width of the
// output so that the new bits can be outputted.
module ShiftRegister
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

endmodule : ShiftRegister
