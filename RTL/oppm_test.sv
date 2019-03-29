`default_nettype none

// Pulser testbench
module Pulser_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam COUNT = 50;
  logic rst_n;
  logic start;
  logic avail;
  logic pulse;
  Pulser #(.COUNT(COUNT)) dut(.*);

  default clocking cb @(posedge clk);
    default input #1step output negedge;
    output rst_n;
    inout  start;
    input  avail;
    input  pulse;

    property avail_means_inactive;
      avail |-> ~pulse;
    endproperty

    property correct_pulse;
      avail & start |-> ~pulse ##1 pulse ##COUNT ~pulse;
    endproperty

    property avail_after_pulse;
      pulse ##1 ~pulse |-> ##1 $rose(avail);
    endproperty

    property avail_ends;
      avail & start |-> ##1 ~avail;
    endproperty
  endclocking: cb

  a1: assert property (cb.avail_means_inactive);
  c1: cover property (cb.avail_means_inactive);

  a2: assert property (cb.correct_pulse);
  c2: cover property (cb.correct_pulse);

  a3: assert property (cb.avail_after_pulse);
  c3: cover property (cb.avail_after_pulse);

  a4: assert property (cb.avail_ends);
  c4: cover property (cb.avail_ends);

  covergroup cg @(posedge clk);
    option.at_least = 2;

    pulser_count_p: coverpoint dut.count {
      bins count_bins [] = {[0:COUNT]};
    }
    cross cb.start, cb.avail;
    cross cb.start, cb.pulse;
    cross cb.start, pulser_count_p;
  endgroup: cg

  localparam int SEED = 18500;
  initial $srandom(SEED);

  initial begin
    cg cg_inst = new;

    rst_n = 1'b0;
    start = 1'b0;

    ##1 cb.rst_n <= 1'b1;

    while (cg_inst.get_coverage() < 99.0) begin
      ##1 cb.start <= $urandom;
    end

    // Wait for last pulse to finish
    cb.start <= 1'b0;
    @(cb.avail);
    ##1 $finish;
  end
endmodule: Pulser_test

// OppmCounter testbench
module OppmCounter_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam N = 2;
  localparam L = 8;
  localparam L_SZ = $clog2(L+1);
  localparam DELTA = 1;
  logic            rst_n;
  logic            start;
  logic            clear;
  logic            run;
  logic [L_SZ-1:0] tick_ct;
  logic [N-1:0]    slot_idx;
  logic            final_tick;
  logic            final_slot;
  logic            near_begin;
  logic [N-1:0]    near_slot_idx;
  OppmCounter #(.N(N), .L(L), .DELTA(DELTA)) dut(.*);

  default clocking cb @(posedge clk);
    default input #1step output negedge;
    output rst_n;
    inout  start;
    inout  clear;
    input  run;
    input  tick_ct;
    input  slot_idx;
    input  final_tick;
    input  final_slot;
    input  near_begin;
    input  near_slot_idx;

    property start_initiates_run;
      start & ~clear & ~$past(run) |-> run;
    endproperty

    property clear_clears;
      ~start & clear |-> ##1 (tick_ct == 0) && (slot_idx == 0);
    endproperty

    property ensure_tick_iterates;
      run & ~clear |-> (~final_tick ##1 tick_ct == $past(tick_ct) + 1) or
                       (final_tick ##1 tick_ct == 0);
    endproperty

    property ensure_slot_iterates;
      run & ~clear & final_tick |->
        (~final_slot ##1 slot_idx == $past(slot_idx) + 1) or
        (final_slot ##1 slot_idx == 0);
    endproperty
  endclocking: cb

  a1: assert property (cb.start_initiates_run);
  c1: cover property (cb.start_initiates_run);

  a2: assert property (cb.clear_clears);
  c2: cover property (cb.clear_clears);

  a3: assert property (cb.ensure_tick_iterates);
  c3: cover property (cb.ensure_tick_iterates);

  a4: assert property (cb.ensure_slot_iterates);
  c4: cover property (cb.ensure_slot_iterates);

  initial begin
    rst_n = 1'b0;
    start = 1'b0;
    clear = 1'b0;

    ##1 cb.rst_n <= 1'b1;

    repeat (10) begin
      cb.start <= 1'b1;
      randcase
        1: ;
        1: ##1 cb.start <= 1'b0;
      endcase
      repeat ($urandom_range(1, 5 * 2**N) * L) ##1;
      cb.start <= 1'b0;
      cb.clear <= 1'b1;
      ##1 cb.clear <= 1'b0;
      randcase
        1: ;
        1: ##1;
      endcase
    end

    ##1 $finish;
  end
endmodule: OppmCounter_test

// Modulator testbench
//TODO Write a good testbench???
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
    default input #1step output negedge;
    output rst_n;
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
    // Encoding
    output data;
    output start;
    input  avail;
    input  pulse;
    // Decoding
    input  avail_rcv;
    output read;
  endclocking: cb

  localparam NUM_ITER = 2;

  initial begin
    rst_n = 1'b0;
    data = {N_MOD{1'b0}};
    start = 1'b0;
    read = 1'b0;

    ##1 cb.rst_n <= 1'b1;

    repeat (NUM_ITER) begin
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

  initial begin
    repeat (NUM_ITER) begin
      @(posedge cb.avail_rcv);
      cb.read <= 1'b1;
      ##5;
      cb.read <= 1'b0;
    end
  end
endmodule: Decoder_test
