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

//---- Modulator
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
  Register #(.WIDTH(N)) dataReg(.D(data), .en(data_en), .Q(data_Q), .*);

  logic valid_en;
  logic valid_Q;
  Register #(.WIDTH(1)) validReg(.D(valid), .en(valid_en), .Q(valid_Q), .*);

  assign data_en = symbol_clear,
         avail = symbol_clear,
         valid_en = symbol_clear;

  logic pulser_start, pulser_avail, pulser_out;
  Pulser #(.COUNT(PULSE_CT)) pulser(.start(pulser_start), .avail(pulser_avail),
                                    .pulse(pulser_out), .*);

  assign pulser_start = (slot_ct == 0) && (data_Q == symbol_id);
  assign pulse = pulser_out && valid_Q;
endmodule: Modulator

//---- Encoder
module Encoder
// Encodes packets of data in sequences of pulses.
// Data is sent MSB-first.
#(parameter PULSE_CT, // Pulse width in clock ticks
            N_MOD,    // Modulation data size in bits
            L,        // Time slot size in clock ticks
            N_PKT,    // Data packet size in bits
            PRE_CT    // Number of preamble symbols to transmit
)
 (input  logic             clk,   // Clock
  input  logic             rst_n, // Asynchronous reset active low
  input  logic [N_PKT-1:0] data,  // Data packet to transmit
  input  logic             start, // Start transmission
  output logic             avail, // Data can be latched
  output logic             pulse  // Output pulse
);
  localparam PRE_CT_SZ = $clog2(PRE_CT+1);
  logic [PRE_CT_SZ-1:0] count_pre;
  logic                 clear_pre, up_pre;
  Counter #(.WIDTH(PRE_CT_SZ)) preambleCounter(.D({PRE_CT_SZ{1'b0}}),
                                               .load(clear_pre), .up(up_pre),
                                               .Q(count_pre), .*);

  logic [N_MOD-1:0] data_mod;
  logic             valid_mod;
  logic             avail_mod;
  Modulator #(.PULSE_CT(PULSE_CT), .N(N_MOD), .L(L)) modder(.data(data_mod),
    .valid(valid_mod), .avail(avail_mod), .*);

  logic             data_reload, data_shift;
  logic [N_MOD-1:0] data_Q;
  ShiftRegister #(.INWIDTH(N_PKT), .OUTWIDTH(N_MOD)) dataReg(.D(data),
    .reload(data_reload), .shift(data_shift), .Q(data_Q), .*);

  localparam DATA_PULSE_CT = (N_PKT+N_MOD-1) / N_MOD; // Ceiling division
  localparam DATA_PULSE_SZ = $clog2(DATA_PULSE_CT+1);
  logic [DATA_PULSE_SZ-1:0] count_dp;
  logic                     clear_dp, up_dp;
  Counter #(.WIDTH(DATA_PULSE_SZ)) dataPulseCounter(.D({DATA_PULSE_SZ{1'b0}}),
                                                    .load(clear_dp),
                                                    .up(up_dp), .Q(count_dp),
                                                    .*);

  // State register
  enum {IDLE, PREAM, DATA} s, ns;
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n)
      s <= IDLE;
    else
      s <= ns;
  end

  // Output logic
  always_comb begin
    ns = s;
    avail = 1'b0;
    // pulse is output of modder

    clear_pre = 1'b0;
    up_pre = 1'b0;

    data_mod = {N_MOD{1'b0}};
    valid_mod = 1'b0;
    
    data_reload = 1'b0;
    data_shift = 1'b0;

    clear_dp = 1'b0;
    up_dp = 1'b0;

    unique case (s)
      IDLE: begin
        ns = start ? PREAM : IDLE;
        avail = 1'b1;
        clear_pre = ~start;
        valid_mod = start;
        data_reload = start;
        clear_dp = ~start;
      end
      PREAM: begin
        ns = (count_pre < PRE_CT) ? PREAM : DATA;
        avail = 1'b0;
        clear_pre = (count_pre >= PRE_CT);
        up_pre = avail_mod & (count_pre < PRE_CT);
        valid_mod = 1'b1;
      end
      DATA: begin
        ns = (count_dp < DATA_PULSE_CT) ? DATA : IDLE;
        avail = 1'b0;
        data_mod = data_Q;
        valid_mod = 1'b1;
        data_shift = avail_mod & (count_dp < DATA_PULSE_CT);
        clear_dp = (count_dp >= DATA_PULSE_CT);
        up_dp = avail_mod & (count_dp < DATA_PULSE_CT);
      end
    endcase
  end
endmodule: Encoder