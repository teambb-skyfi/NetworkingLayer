/*
 * @brief Top level module which interfaces with board inputs and outputs
 * 
 */
module ChipInterface(
  input  logic        CLOCK_50,
  input  logic [ 9:0] SW,
  input  logic [ 2:0] KEY,
  output logic [35:0] GPIO_0,
  output logic [ 9:0] LEDR,
  output logic [ 6:0] HEX1, HEX0);

  logic rst_n;
  assign rst_n = KEY[0];
  
  logic clk;
  assign clk = CLOCK_50;
  
  localparam PULSE_CT = 7500;
  localparam N_MOD = 2;
  localparam L = 10000;
  localparam N_PKT = 8;
  localparam PRE_CT = 4;
 
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) enc(.*);

  always_comb begin
    data = SW[N_PKT-1:0];
    GPIO_0[5] = pulse;

    // Status
    LEDR[8] = avail;
    LEDR[9] = pulse;
  end

  HextoSevenSegment upper(data[7:4], HEX1);
  HextoSevenSegment lower(data[3:0], HEX0);

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
  end
endmodule: ChipInterface