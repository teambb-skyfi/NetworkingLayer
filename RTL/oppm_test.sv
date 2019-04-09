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
module Modulator_test;
  localparam CLK_T = 10; // Must be even

  logic clk;
  initial begin
    clk = 1'b1;
    forever #(CLK_T >> 1) clk = ~clk;
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

  // Parameters for validation
  localparam SLOTS_PER_SYMBOL = 2**N;
  localparam TICKS_PER_SYMBOL = SLOTS_PER_SYMBOL * L;

  function int elapsed_ticks(int t_s, t_e);
    return (t_e - t_s) / CLK_T;
  endfunction: elapsed_ticks

  default clocking cb @(posedge clk);
    default input #1step output negedge;
    output rst_n;
    inout  data;
    inout  valid;
    input  avail;
    input  pulse;

    property not_valid_means_no_pulse;
      $fell(avail) & ~$past(valid) |->
      ~pulse throughout (~avail)[*0:$] ##1 avail;
    endproperty

    property correct_pulse_width;
      $rose(pulse) |-> ##PULSE_CT ~pulse;
    endproperty

    property pulse_at_correct_time;
      logic [N-1:0] pdata;
      int t_s;
      (avail & valid, pdata = data, t_s = $time) |-> ##1
      ~pulse[*0:$] ##1 pulse ##0 (pdata == elapsed_ticks(t_s, $time) / L);
    endproperty
  endclocking: cb

  a1: assert property (cb.not_valid_means_no_pulse);
  c1: cover property (cb.not_valid_means_no_pulse);

  a2: assert property (cb.correct_pulse_width);
  c2: cover property (cb.correct_pulse_width);

  a3: assert property (cb.pulse_at_correct_time);
  c3: cover property (cb.pulse_at_correct_time);

  class RandomData;
  rand logic [N-1:0] data;
  rand logic         valid;

  constraint valid_dist {
    valid dist {1 := 4, 0 := 1};
  }
  endclass: RandomData

  RandomData rd;
  initial begin
    rst_n = 1'b0;
    data = 2'b1;
    valid = 1'b1;

    ##1 cb.rst_n <= 1'b1;

    rd = new;
    //TODO Should use covergroup...
    repeat (50) begin
      @(posedge cb.avail);
      rd.randomize();
      cb.data <= rd.data;
      cb.valid <= rd.valid;
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
  localparam PRE_CT = 2;
  logic             rst_n;
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) dut(.*);

  localparam DATA_PULSE_CT = (N_PKT+N_MOD-1) / N_MOD; // Ceiling division
  localparam TOTAL_PULSE_CT = PRE_CT + DATA_PULSE_CT;
  localparam NUM_SLOTS = 2**N_MOD;

  default clocking cb @(posedge clk);
    default input #1step output negedge;
    output rst_n;
    inout  data;
    inout  start;
    input  avail;
    input  pulse;

    property correct_pulse_width;
      $rose(pulse) |-> ##PULSE_CT ~pulse;
    endproperty

    property correct_avail;
      avail & start |-> ##1 ~avail;
    endproperty

    property correct_num_pulses;
      avail & start |-> $rose(pulse) [->TOTAL_PULSE_CT] ##1 $fell(pulse);  
    endproperty
  endclocking: cb

  a1: assert property (cb.correct_pulse_width);
  c1: cover property (cb.correct_pulse_width);

  a2: assert property (cb.correct_avail);
  c2: cover property (cb.correct_avail);

  a3: assert property (cb.correct_num_pulses);
  c3: cover property (cb.correct_num_pulses);

  localparam PKT_SENT = 100;
  int sent_correctly;

  class TestDemodulator;
    //TODO: Race conditions?
    logic [N_PKT-1:0] dataEncoded[$];
    logic [N_MOD-1:0] pulsedData[$];
    logic [N_PKT-1:0] datumReceived;
    logic [N_PKT-1:0] dataReceived[$];
    int tick_ct;
    int slot_idx;

    task start_receiving;
      @(posedge cb.pulse);
      pulsedData.push_back(0);
      fork
        // Keep tick ct and slot idx
        forever begin
          ##1 tick_ct += 1;
          tick_ct %= L;
          if (tick_ct == 0) begin
            slot_idx += 1;
            slot_idx %= NUM_SLOTS;
          end
        end

        // Receive pulsed data
        forever begin
          @(posedge cb.pulse);
          pulsedData.push_back(slot_idx);
          if (pulsedData.size == TOTAL_PULSE_CT) begin
            datumReceived = 0;
            foreach (pulsedData[i]) begin
              datumReceived = (datumReceived << N_MOD) + pulsedData[i];
            end
            pulsedData.delete;
            dataReceived.push_back(datumReceived);

            // Check if data received is data encoded
            assert (dataReceived[$] == dataEncoded[dataReceived.size - 1])
              sent_correctly += 1;
            else
              $error("Incorrect packet received! Sent %h but received %h",
                dataEncoded[dataReceived.size - 1], dataReceived[$]);
          end
        end
      join_none
    endtask: start_receiving

    task start_testing;
      sent_correctly = 0;
      fork
        // track_encoding
        forever begin
          @(cb.avail & cb.start);
          @(~cb.avail | ~cb.start);
          dataEncoded.push_back(cb.data);
        end

        start_receiving;
      join_none
    endtask: start_testing

    task finish_testing;
      $display("%d of %d successful", sent_correctly, PKT_SENT);
    endtask: finish_testing
  endclass: TestDemodulator

  TestDemodulator td;

  initial begin
    td = new;
    rst_n = 1'b0;
    data = {N_MOD{1'b0}};
    start = 1'b0;
    td.start_testing;

    ##1 cb.rst_n <= 1'b1;

    repeat (PKT_SENT) begin
      cb.data <= $urandom;
      cb.start <= 1'b1;
      @(negedge cb.avail);
      cb.start <= 1'b0;

      repeat (TOTAL_PULSE_CT)
        @(negedge cb.pulse);

      // Random gap between packets
      repeat ($urandom_range(0, 1) * L * (2**N_MOD))
        ##1;
    end

    ##2
    td.finish_testing;
    $finish;
  end
endmodule: Encoder_test

// Decoder testbench
//TODO Write a good testbench???
module Decoder_test;
  logic clk;
  initial begin
    clk = 1'b1;
    forever #5 clk = ~clk;
  end

  localparam int SEED = 18500;
  initial $srandom(SEED);

  localparam PULSE_CT = 7500;
  localparam N_MOD = 2;
  localparam L = 10000;
  localparam N_PKT = 8;
  localparam PRE_CT = 4;
  localparam DELTA = 1;
  logic             rst_n;
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  //TODO Stop using
  //Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
  //          .PRE_CT(PRE_CT)) dut(.*);

  logic [N_PKT-1:0] data_rcv;
  logic             avail_rcv;
  logic             read;
  Decoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
            .PRE_CT(PRE_CT), .DELTA(DELTA)) dut2(.data(data_rcv),
                                                 .avail(avail_rcv), .*);

  default clocking cb @(posedge clk);
    default input #1step output negedge;
    output rst_n;
    // Encoding
    inout  data;
    inout  start;
    input  avail;
    input  pulse;
    // Decoding
    input  avail_rcv;
    output read;

    property encode_to_decode_basic;
      logic [N_PKT-1:0] e_data;
      (start & avail, e_data = data) |-> ~avail_rcv [*0:$] ##1 avail_rcv & (data_rcv == e_data);
    endproperty
  endclocking: cb

  a1: assert property(cb.encode_to_decode_basic);
  c1: cover property(cb.encode_to_decode_basic);

  localparam NUM_ITER = 10;

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
