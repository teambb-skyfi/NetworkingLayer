/*
 * @brief Top level module which interfaces with board inputs and outputs
 * 
 */
module ChipInterface(
  input  logic        CLOCK_50,
  input  logic [ 9:0] SW,
  input  logic [ 2:0] KEY,
  //output logic [35:0] GPIO_0,
  //input  logic [35:0] GPIO_1,
  output logic [ 9:0] LEDR,
  output logic [ 6:0] HEX5, HEX4, HEX1, HEX0);

  logic rst_n;
  assign rst_n = KEY[0];
  
  logic clk;
  assign clk = CLOCK_50;
  
  localparam PULSE_CT = 7500;
  localparam N_MOD = 2;
  localparam L = 10000;
  localparam N_PKT = 8;
  localparam PRE_CT = 4;
  localparam DELTA = 2000; //TODO Could be reduced; likely not issue anyway

  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) enc(.*);

  logic [N_PKT-1:0] data_rcv, data_rcv_Q;
  logic             avail_rcv;
  logic             read;
  //logic             pulse;
  Decoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT), .DELTA(DELTA)) dut2(.data(data_rcv), .avail(avail_rcv),
                                         .*);

  HextoSevenSegment upper(data[7:4], HEX1);
  HextoSevenSegment lower(data[3:0], HEX0);

  Register #(.WIDTH(N_PKT)) rcvreg(.D(data_rcv), .Q(data_rcv_Q), .en(avail_rcv), .clear(1'b0), .*);

  HextoSevenSegment upperr(data_rcv_Q[7:4], HEX5);
  HextoSevenSegment lowerr(data_rcv_Q[3:0], HEX4);
  
  always_comb begin
    data = SW[N_PKT-1:0];
    read = 1'b0; // No "read"

    // Status
    LEDR[7] = avail_rcv;
    LEDR[8] = avail;
    LEDR[9] = pulse;
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

  // State logic
  always_comb begin
    ns = s;
    start = 1'b1;
   
//   unique case (s)
//    WAIT: begin
//      ns = (avail) ? READY : WAIT;
//    end
//    READY: begin
//      ns = (!send_n) ? SENT : READY;
//      start = !send_n;
//    end
//    SENT: begin
//      ns = (!send_n) ? SENT : WAIT;
//    end
//   endcase
  end
endmodule: ChipInterface