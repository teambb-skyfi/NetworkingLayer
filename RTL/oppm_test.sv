`default_nettype none

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

// Modulator testbench
module Modulator_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam PULSE_CT = 1;
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
      @(posedge cb.avail);
      cb.data <= $urandom;
      randcase
        4: cb.valid <= 1;
        1: cb.valid <= 0;
      endcase
    end

    @(posedge cb.avail);
    ##1 $finish;
  end
endmodule: Modulator_test

// Encoder testbench
module Encoder_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam PULSE_CT = 1;
  localparam N_MOD = 2;
  localparam L = 4;
  localparam N_PKT = 8;
  localparam PRE_CT = 3;
  logic             rst_n;
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) dut(.*);

  default clocking cb @(posedge clk);
    default input #1step output #2;
    output negedge rst_n;
    output data;
    output start;
    input  avail;
    input  pulse;
  endclocking: cb

  initial begin
    rst_n = 1'b0;
    data = {N_MOD{1'b0}};
    start = 1'b0;

    ##1 cb.rst_n <= 1'b1;

    repeat (10) begin
      cb.data <= $urandom;
      cb.start <= 1'b1;
      @(negedge cb.avail);
      cb.start <= 1'b0;

      repeat (dut.DATA_PULSE_CT + dut.PRE_CT)
        @(negedge cb.pulse);

      // Random gap between packets
      repeat ($urandom_range(0, 1) * L * (2**N_MOD))
        ##1;
    end

    ##1 $finish;
  end
endmodule: Encoder_test

// Decoder testbench
module Decoder_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam PULSE_CT = 2;
  localparam N_MOD = 2;
  localparam L = 4;
  localparam N_PKT = 8;
  localparam PRE_CT = 3;
  logic             rst_n;
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) dut(.*);

  logic [N_PKT-1:0] data_rcv;
  logic             avail_rcv;
  logic             read;
  Decoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) dut2(.data(data_rcv), .avail(avail_rcv), .*);

  default clocking cb @(posedge clk);
    default input #1step output #2;
    output negedge rst_n;
    output data;
    output start;
    output read;
    input  avail;
    input  pulse;
  endclocking: cb

  initial begin
    rst_n = 1'b0;
    data = {N_MOD{1'b0}};
    start = 1'b0;
    read = 1'b0;

    ##1 cb.rst_n <= 1'b1;

    repeat (2) begin
      cb.data <= $urandom;
      cb.start <= 1'b1;
      @(negedge cb.avail);
      cb.start <= 1'b0;

      repeat (dut.DATA_PULSE_CT + dut.PRE_CT)
        @(negedge cb.pulse);

      // Random gap between packets
      repeat ($urandom_range(0, 1) * L * (2**N_MOD))
        ##1;
    end

    ##1 $finish;
  end
endmodule: Decoder_test