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