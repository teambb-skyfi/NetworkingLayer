//---- Pulser
// Drive a pulse of defined length
module Pulser
#(parameter COUNT)
 (input  logic clk,    // Clock
  input  logic rst_n,  // Asynchronous reset active low
  input  logic start,  // Start pulse
  output logic avail,  // Pulser available
  output logic pulse   // Output pulse
);
  parameter N_CT = $clog2(COUNT+1);

  logic [N_CT-1:0] count;
  logic            clear, up;
  Counter #(.WIDTH(N_CT)) pulseCounter(.D(4'b0), .load(clear), .Q(count), .*);

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
        ns = (count < COUNT) ? PULSE : IDLE;
        clear = (count >= COUNT);
        up = (count < COUNT);
        avail = 1'b0;
        pulse = (count < COUNT);
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
  Pulser #(.COUNT(10)) dut(.*);

  default clocking cb @(posedge clk);
    default input #1step output #2;
    output negedge rst_n;
    output start;
    input  avail;
    input  pulse;
  endclocking: cb

  initial begin
    rst_n = 1'b0;
    start = 1'b0;

    ##1 cb.rst_n <= 1'b1;
    ##1 cb.start <= 1'b1;
    ##1 cb.start <= 1'b0;
    @(negedge cb.pulse);

    ##1 $finish;
  end
endmodule: Pulser_test
