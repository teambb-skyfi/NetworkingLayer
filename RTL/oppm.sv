`default_nettype none

//---- Pulser
// Drive a pulse of defined length
module Pulser
#(parameter COUNT     // Pulse width in clock ticks
)
 (input  logic clk,   // Clock
  input  logic rst_n, // Asynchronous reset active low
  input  logic start, // Start pulse
  output logic avail, // Pulser available
  output logic pulse  // Output pulse
);
  localparam N_SZ = $clog2(COUNT+1);

  logic [N_SZ-1:0] count;
  logic            clear, up;
  Counter #(.WIDTH(N_SZ)) pulseCounter(.D({N_SZ{1'b0}}), .load(clear),
                                       .Q(count), .*);

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
  Pulser #(.COUNT(50)) dut(.*);

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

    ##1 cb.start <= 1'b1;
    @(negedge cb.pulse);

    @(negedge cb.pulse);

    ##1 $finish;
  end
endmodule: Pulser_test

//---- Modulator
// Modulates 
module Modulator
#(parameter PULSE_CT, // Pulse width in clock ticks
            N,        // Data size in bits
            L         // Time slot size in clock ticks
)
 (input  logic         clk,   // Clock
  input  logic         rst_n, // Asynchronous reset active low
  input  logic [N-1:0] data,  // Data to modulate
  input  logic         valid, // Data is valid
  output logic         avail, // Data can be latched
  output logic         pulse  // Output pulse
);

  localparam L_SZ = $clog2(L+1);
  logic [L_SZ-1:0] slot_ct;
  logic            slot_clear, slot_up;
  Counter #(.WIDTH(L_SZ)) slotCounter(.D({L_SZ{1'b0}}), .load(slot_clear),
                                      .up(slot_up), .Q(slot_ct), .*);
  assign slot_clear = (slot_ct == L-1);
  assign slot_up = (slot_ct != L-1);

  localparam SYMBOL_CT = 2**N - 1;
  localparam SYMBOL_SZ = N;
  logic [SYMBOL_SZ-1:0] symbol_id;
  logic                 symbol_clear, symbol_up;
  Counter #(.WIDTH(SYMBOL_SZ)) symbolCounter(.D({SYMBOL_SZ{1'b0}}),
                                             .load(symbol_clear),
                                             .up(symbol_up), .Q(symbol_id), .*);

  logic final_symbol;
  assign final_symbol = symbol_id == SYMBOL_CT;

  assign symbol_clear = slot_clear && final_symbol;
  assign symbol_up = slot_clear && !final_symbol;

  logic         data_en;
  logic [N-1:0] data_D, data_Q;
  Register #(.WIDTH(N)) dataReg(.D(data_D), .en(data_en), .Q(data_Q), .*);

  assign data_en = symbol_clear;
  assign data_D = valid ? data : {N{1'b0}};

  assign avail = symbol_clear;

  logic pulser_start, pulser_avail;
  Pulser #(.COUNT(PULSE_CT)) pulser(.start(pulser_start), .avail(pulser_avail),
                                    .*);

  assign pulser_start = (slot_ct == 0) && (data_Q == symbol_id);
endmodule: Modulator

// Modulator testbench
module Modulator_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam PULSE_CT = 2;
  localparam N = 2;
  localparam L = 4;
  logic         rst_n;
  logic [N-1:0] data;
  logic         valid;
  logic         avail;
  logic         pulse;
  Modulator #(.PULSE_CT(PULSE_CT), .N(N), .L(L)) dut(.*);

  default clocking cb @(posedge clk);
    default input #1step output #2;
    output negedge rst_n;
    output data;
    output valid;
    input  avail;
    input  pulse;
  endclocking: cb

  initial begin
    rst_n = 1'b0;
    data = 2'b1;
    valid = 1'b1;

    ##1 cb.rst_n <= 1'b1;

    repeat (10) begin
      @(negedge cb.pulse);
      cb.data <= $urandom;
    end

    @(posedge cb.avail);
    ##1 $finish;
  end
endmodule: Modulator_test