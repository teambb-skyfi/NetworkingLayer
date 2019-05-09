/*
 * @brief Top level module which interfaces with board inputs and outputs
 * 
 */
module ChipInterface(
  input  logic        CLOCK_50,
  input  logic [ 9:0] SW,
  input  logic [ 2:0] KEY,
  output logic [35:0] GPIO_0,
  input  logic [35:0] GPIO_1,
  output logic [ 9:0] LEDR,
  output logic [ 6:0] HEX5, HEX4, HEX1, HEX0);
/*
  logic rst_n;
  assign rst_n = KEY[0];
  
  logic clk;
  assign clk = CLOCK_50;
  
  localparam PULSE_CT = 30;
  localparam N_MOD = 2;
  localparam L = 40;
  localparam N_PKT = 8;
  localparam PRE_CT = 4;
  localparam DELTA = 19; //TODO Could be reduced; likely not issue anyway

  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) enc(.*);

  logic [N_PKT-1:0] data_rcv, data_rcv_Q;
  logic             avail_rcv;
  logic             read;
  logic             pulse_rcv;
  logic             error;
  Decoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT), .DELTA(DELTA)) dut2(.data(data_rcv), .avail(avail_rcv), .pulse(pulse_rcv),
                                         .*);

  HextoSevenSegment upper(data[7:4], HEX1);
  HextoSevenSegment lower(data[3:0], HEX0);

  Register #(.WIDTH(N_PKT)) rcvreg(.D(data_rcv), .Q(data_rcv_Q), .en(avail_rcv), .clear(1'b0), .*);

  HextoSevenSegment upperr(data_rcv_Q[7:4], HEX5);
  HextoSevenSegment lowerr(data_rcv_Q[3:0], HEX4);

  digitalFilter #(.HISTORY_SIZE(50))(.clk, .rst_n, .pulse(GPIO_1[6]), .filteredPulse(pulse_rcv));
  
  always_comb begin
    data = SW[N_PKT-1:0];
    read = 1'b1; // Always read

    // Status
    LEDR[0] = pulse;
    LEDR[1] = avail;

    LEDR[7] = pulse_rcv;
    LEDR[8] = avail_rcv;
    LEDR[9] = error;

    GPIO_0[5] = pulse;
    //pulse_rcv = GPIO_1[6];
  end

  // State register
  enum {WAIT, READY, SENT} s, ns;
  always_ff @(posedge clk, negedge rst_n) begin
    if (~rst_n)
      s <= WAIT;
    else
      s <= ns;
  end

  logic send_n;
  assign send_n = KEY[1];

  // Rate limiter
  localparam LIM_SZ = 32, LIMIT = 500_000;
  logic              load_lim;
  logic [LIM_SZ-1:0] lim_Q;
  Counter #(.WIDTH(LIM_SZ)) limiter(.D(0), .load(load_lim), .up(1'b1), .Q(lim_Q), .*);

  // State logic
  always_comb begin
    ns = s;
    load_lim = 1'b1;

    if (SW[9]) begin
      // Button mode
      start = 1'b0;
       
      unique case (s)
       WAIT: begin
         ns = (avail) ? READY : WAIT;
       end
       READY: begin
         ns = (!send_n) ? SENT : READY;
         start = !send_n;
       end
       SENT: begin
         ns = (!send_n) ? SENT : WAIT;
       end
      endcase
    end else begin
      // Continuous mode
      load_lim = ~avail;
      start = 1'b0;

      if (lim_Q >= LIMIT)
        start = 1'b1;
    end
  end

  logic [31:0] avail_ct, error_ct;
  Counter #(.WIDTH(32)) availCtr(.D(32'd0), .load(1'b0), .up(avail_rcv), .Q(avail_ct), .*);
  Counter #(.WIDTH(32)) errorCtr(.D(32'd0), .load(1'b0), .up(error),     .Q(error_ct), .*);
*/
  logic rst_n;
  assign rst_n = KEY[0];

  logic clk;
  assign clk = CLOCK_50;

  logic filteredPulse;
  digitalFilter #(.HISTORY_SIZE(25))(.clk, .rst_n, .pulse(GPIO_1[6]), .filteredPulse);
  EdgeDetector(.data(filteredPulse), .clk, .rst_n, .is_edge(GPIO_0[5]));
  
  assign LEDR = 10'b0000000011;
endmodule: ChipInterface