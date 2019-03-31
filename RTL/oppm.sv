`default_nettype none

/*
Pulser : Specification
----------------------
The Pulser will assert avail when it is ready to pulse. start may be asserted at
any time. One cycle after start is correctly asserted, avail will be deasserted
and pulse will be asserted for COUNT cycles. start will be ignored until avail
is re-asserted. The Pulser is available the cycle after the pulse ends.
*/
module Pulser
#(parameter COUNT     // Pulse width in ticks
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

/*
OppmCounter : Specification
---------------------------
Note that the OppmCounter starts counting ticks in the SAME clock cycle that
start is asserted!

When cleared, the tick counts and slot indices are reset to 0.

start & clear is undefined behavior
*/
module OppmCounter
#(parameter N,                 // Data size in bits
            L,                 // Time slot size in ticks
            DELTA,             // Delta to be considered "in slot" in ticks
            L_SZ = $clog2(L+1) // Tick ct size in bits
)
 (input  logic            clk,             // Clock
  input  logic            rst_n,           // Asynchronous reset active low
  input  logic            start,           // Start counting
  input  logic            clear,           // Synchronous reset
  output logic            run,             // Is running
  output logic [L_SZ-1:0] tick_ct,         // Tick count
  output logic [N-1:0]    slot_idx,        // Value of current slot
  output logic            final_tick,      // Is on final tick
  output logic            final_slot,      // Is on final slot
  output logic            near_begin,      // Are we near slot beginning
  output logic [N-1:0]    near_slot_idx,   // Slot we are near beginning of
  output logic            final_near_tick, // Is on final near tick
  output logic            final_near_slot  // Is on final near slot
);
  // Attempt at precondition
  initial assert (DELTA < L/2) else $fatal("Invalid DELTA in %m");

  localparam LAST_SLOT_IDX = 2**N - 1;
  localparam LAST_TICK_CT = L - 1;

  // Once initiated, keep going (no need to hold start for more than one cycle)
  logic start_Q;
  Register #(.WIDTH(1)) startReg(.D(run), .en(1'b1), .Q(start_Q), .*);
  assign run = start_Q | start;

  // Count how wide every tick is (in clock cycles)
  logic            tick_clear, tick_up;
  Counter #(.WIDTH(L_SZ)) slotTickCtr(.D({L_SZ{1'b0}}), .load(tick_clear),
                                      .up(tick_up), .Q(tick_ct), .*);
  always_comb begin
    final_tick = tick_ct == LAST_TICK_CT;
    tick_clear = final_tick | ~run | clear;
    tick_up = ~final_tick & run & ~clear;
  end

  // Iterate through slot values
  logic idx_clear, idx_up;
  Counter #(.WIDTH(N)) slotIdxCtr(.D({N{1'b0}}), .load(idx_clear), .up(idx_up),
                                  .Q(slot_idx), .*);
  always_comb begin
    final_slot = slot_idx == LAST_SLOT_IDX;
    idx_clear = (final_tick & final_slot) | ~run | clear;
    idx_up = (final_tick & ~final_slot) & run & ~clear;
  end

  // Slot beginning calculations
  logic [N-1:0] next_idx;
  logic         at_beginning, at_end;
  always_comb begin
    at_beginning = tick_ct <= DELTA;
    at_end = tick_ct >= (LAST_TICK_CT - DELTA + 1);
    near_begin = at_beginning | at_end;

    // Yes, this is essentially slotIdxCtr...
    next_idx = final_slot ? {N{1'b0}} : slot_idx + 1;
    near_slot_idx = at_end ? next_idx : slot_idx;

    final_near_slot = near_slot_idx == LAST_SLOT_IDX;
    final_near_tick = tick_ct == (LAST_TICK_CT - DELTA);
  end
endmodule: OppmCounter

/*
Modulator : Specification
-------------------------
*/
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
  logic         data_en;
  logic [N-1:0] data_Q;
  Register #(.WIDTH(N)) dataReg(.D(data), .en(data_en), .clear(1'b0),
                                .Q(data_Q), .*);

  logic valid_en;
  logic valid_Q;
  Register #(.WIDTH(1)) validReg(.D(valid), .en(valid_en), .clear(1'b0),
                                 .Q(valid_Q), .*);

  logic pulser_start, pulser_avail, pulser_out;
  Pulser #(.COUNT(PULSE_CT)) pulser(.start(pulser_start), .avail(pulser_avail),
                                    .pulse(pulser_out), .*);

  localparam DELTA = 0; // near_begin outputs not used..
  localparam L_SZ = $clog2(L+1);
  logic            run;
  logic [L_SZ-1:0] tick_ct;
  logic [N-1:0]    slot_idx;
  logic            final_tick;
  logic            final_slot;
  logic            near_begin;
  logic [N-1:0]    near_slot_idx;
  logic            final_near_tick;
  logic            final_near_slot;
  OppmCounter #(.L(L), .N(N), .DELTA(0)) oc(.start(1'b1), .clear(1'b0), .*);

  always_comb begin
    // Available on the final slot of each symbol
    data_en = final_slot & final_tick;
    avail = final_slot & final_tick;
    valid_en = final_slot & final_tick;

    pulser_start = (tick_ct == 0) && (data_Q == slot_idx);
    pulse = pulser_out && valid_Q;
  end
endmodule: Modulator

/*
Encoder : Specification
-----------------------
Data is sent MSB-first.
*/
module Encoder
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
  ShiftOutRegister #(.INWIDTH(N_PKT), .OUTWIDTH(N_MOD)) dataReg(.D(data),
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

//outputs a 1 on filtered pulse only if PASTCOUNT
// number of previos values were 1.
module digitalFilter #(parameter HISTORY_SIZE=100)(
  input logic clk, 
  input logic rst_n,
  input logic pulse,
  output logic filteredPulse);



  logic [HISTORY_SIZE-1:0] history;
  ShiftInRegister #(.INWIDTH(1), .OUTWIDTH(HISTORY_SIZE),.DEFVAL(0)) 
    sr0(.clk, .rst_n, .shift(1), .reload(0), .D(pulse), .Q(history)); 
  
  assign filteredPulse = ((history == {HISTORY_SIZE{1'b1}}) && pulse) ? 1'b1 : 1'b0;

endmodule: digitalFilter

//---- Decoder
module Decoder
// Decodes packets of data sent as OPPM pulses.
// Data is received MSB-first.
#(parameter PULSE_CT, // Pulse width in clock ticks
            N_MOD,    // Modulation data size in bits
            L,        // Time slot size in clock ticks
            N_PKT,    // Data packet size in bits
            PRE_CT,   // Number of preamble symbols to transmit
            DELTA     // Delta to be considered "in slot" in ticks
)
 (input  logic             clk,   // Clock
  input  logic             rst_n, // Asynchronous reset active low
  input  logic             pulse, // Input pulse
  input  logic             read,  // Data is read
  output logic [N_PKT-1:0] data,  // Data packet to transmit
  output logic             avail, // Data is available to be latched
  output logic             error  // Error has happened
);
  logic filteredPulse;
  digitalFilter #(.HISTORY_SIZE(50))(.clk, .rst_n, .pulse, .filteredPulse);
  
  logic is_edge;
  EdgeDetector ed(.data(filteredPulse), .*);

  localparam L_SZ = $clog2(L+1);
  logic             start_oc;
  logic             clear_oc;
  logic             run;
  logic [L_SZ-1:0]  tick_ct;
  logic [N_MOD-1:0] slot_idx;
  logic             final_tick;
  logic             final_slot;
  logic             near_begin;
  logic [N_MOD-1:0] near_slot_idx;
  logic            final_near_tick;
  logic            final_near_slot;
  OppmCounter #(.L(L), .N(N_MOD), .DELTA(DELTA)) oc(.start(start_oc),
                                                    .clear(clear_oc), .*);

  localparam PRE_CT_SZ = $clog2(PRE_CT+1);
  logic [PRE_CT_SZ-1:0] count_pre;
  logic                 clear_pre, up_pre;
  Counter #(.WIDTH(PRE_CT_SZ)) preambleCounter(.D({PRE_CT_SZ{1'b0}}),
                                               .load(clear_pre), .up(up_pre),
                                               .Q(count_pre), .*);

  localparam DATA_PULSE_CT = (N_PKT+N_MOD-1) / N_MOD; // Ceiling division
  localparam DATA_PULSE_SZ = $clog2(DATA_PULSE_CT+1);
  logic [DATA_PULSE_SZ-1:0] count_dp;
  logic                     clear_dp, up_dp;
  Counter #(.WIDTH(DATA_PULSE_SZ)) dataPulseCounter(.D({DATA_PULSE_SZ{1'b0}}),
                                                    .load(clear_dp),
                                                    .up(up_dp), .Q(count_dp),
                                                    .*);

  logic             data_reload, data_shift;
  logic [N_MOD-1:0] data_D;
  ShiftInRegister #(.INWIDTH(N_MOD), .OUTWIDTH(N_PKT)) dataReg(.D(data_D),
    .reload(data_reload), .shift(data_shift), .Q(data), .*);

  logic avail_D, data_ready, incoming;
  Register #(.WIDTH(1)) availReg(.D(avail_D), .en(1'b1), .clear(1'b0),
                                 .Q(avail), .*);
  always_comb begin
    unique case (avail)
      0: begin
        avail_D = data_ready;
      end
      1: begin
        avail_D = !(read | incoming);
      end
    endcase
  end
  logic error_D, error_happened;
  Register #(.WIDTH(1)) errorReg(.D(error_D), .en(1'b1), .clear(1'b0),
                                 .Q(error), .*);
  always_comb begin
    unique case (error)
      0: begin
        error_D = error_happened;
      end
      1: begin
        error_D = !(read | incoming);
      end
    endcase
  end

  logic cp, cp_D, cp_Q, clear_cp;
  Register #(.WIDTH(1)) consec_pulse_reg(.D(cp_D), .Q(cp_Q), .clear(clear_cp), .en(1'b1), .*);
  assign cp_D = cp | cp_Q;

  logic check_for_missing;

  // State register
  enum {WAIT=0, PREAM=1, DATA=2, ERR0=4, ERR1=5, ERR2=6, ERR3=7} s, ns;
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n)
      s <= WAIT;
    else
      s <= ns;
  end

  // Output logic
  always_comb begin
    ns = s;

    start_oc = 1'b0;
    clear_oc = 1'b0;

    clear_pre = 1'b0;
    up_pre = 1'b0;

    clear_dp = 1'b0;
    up_dp = 1'b0;

    data_reload = 1'b0;
    data_shift = 1'b0;
    data_D = {N_MOD{1'b0}};

    cp = 1'b0;
    clear_cp = 1'b0;
    check_for_missing = final_near_tick & final_near_slot;

    incoming = 1'b0;
    data_ready = 1'b0;
    error_happened = 1'b0;

    //TODO Logic to handle more than one pulse in a symbol (according to cp)
    unique case (s)
      WAIT: begin
        clear_dp = 1'b1;

        if (is_edge) begin
          ns = PREAM;
          start_oc = 1'b1;
          up_pre = 1'b1;
          data_reload = 1'b1;
          cp = 1'b1;
          incoming = 1'b1;
        end else begin
          clear_oc = 1'b1; //TODO Modify for multi-rx?
          clear_pre = 1'b1;
        end
      end
      PREAM: begin
        data_D = near_slot_idx;

        cp = is_edge;

        if (is_edge & near_begin) begin
          if (count_pre >= PRE_CT) begin
            // Data pulse
            ns = DATA;

            clear_pre = 1'b1;

            up_dp = 1'b1;
            data_reload = 1'b1;
          end else if (near_slot_idx == {N_MOD{1'b0}}) begin
            // Correct preamble pulse
            ns = PREAM;

            up_pre = 1'b1;
          end else begin
            // Erroneous pulse
            ns = ERR0;

            // Clear all counters
            clear_oc = 1'b1; //TODO Modify for multi-rx?
            clear_pre = 1'b1;
            clear_dp = 1'b1;
          end
        end else if (is_edge) begin
          // Edge detected outside acceptable bounds
          ns = ERR1;

          // Clear all counters
          clear_oc = 1'b1; //TODO Modify for multi-rx?
          clear_pre = 1'b1;
          clear_dp = 1'b1;
        end else if (check_for_missing) begin
          if (cp_Q)
            clear_cp = 1'b1;
          else
            ns = ERR3;
        end
      end
      DATA: begin
        data_D = near_slot_idx;

        cp = is_edge;

        if (is_edge & near_begin) begin
          data_shift = 1'b1;

          if (count_dp == DATA_PULSE_CT-1) begin
            ns = WAIT;

            data_ready = 1'b1;
            clear_oc = 1'b1; //TODO Modify for multi-rx?
            clear_pre = 1'b1;
            clear_dp = 1'b1;
          end else begin
            up_dp = 1'b1;
          end
        end else if (is_edge) begin
          // Edge detected outside acceptable bounds
          ns = ERR2;

          // Clear all counters
          clear_oc = 1'b1; //TODO Modify for multi-rx?
          clear_pre = 1'b1;
          clear_dp = 1'b1;
        end else if (check_for_missing) begin
          if (cp_Q)
            clear_cp = 1'b1;
          else
            ns = ERR3;
        end
      end

      ERR0, ERR1, ERR2, ERR3: begin
        ns = WAIT;
        error_happened = 1'b1;
        data_reload = 1'b1;
        clear_oc = 1'b1; //TODO Modify for multi-rx?
        clear_pre = 1'b1;
        clear_dp = 1'b1;
      end
    endcase
  end
endmodule: Decoder
