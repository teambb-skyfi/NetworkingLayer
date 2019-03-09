//---- Pulser
// Drive a pulse of defined length
module Pulser
 (input  logic clk,    // Clock
  input  logic rst_n,  // Asynchronous reset active low
  input  logic start,  // Start pulse
  output logic avail,  // Pulser available
  output logic pulse   // Output pulse
);

  logic [3:0] count;
  logic       clear, up;
  Counter pulseCounter(.D(4'b0), .load(clear), .Q(count), .*);

  // State register
  enum {IDLE, PULSE} s, ns;
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n)
      s <= IDLE;
    else
      s <= ns;
  end

  // Output logic
  always_comb begin
    unique case (s)
      IDLE: begin
        ns = start ? PULSE : IDLE;
        clear = ~start;
        up = 1'b0;
        avail = 1'b1;
        pulse = 1'b0;
      end
      PULSE: begin
        ns = (count < 10) ? PULSE : IDLE;
        clear = (count >= 10);
        up = (count < 10);
        avail = 1'b0;
        pulse = (count < 10);
      end
    endcase
  end
endmodule: Pulser

// Pulser testbench
module Pulser_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  logic rst_n;
  logic start;
  logic avail;
  logic pulse;
  Pulser dut(.*);

  initial begin
    rst_n  =     1'b0;
    start <=     1'b0;
    rst_n <=  #1 1'b1;
    start <= #19 1'b1;
    start <= #39 1'b0;

    #151 $finish;
  end
endmodule: Pulser_test
