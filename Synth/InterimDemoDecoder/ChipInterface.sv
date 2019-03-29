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
  output logic [ 6:0] HEX2, HEX1, HEX0);

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
  logic             avail;
  logic             read;
  logic             pulse;
  Decoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT), .DELTA(DELTA)) dut(.*);

  HextoSevenSegment upper(data[7:4], HEX1);
  HextoSevenSegment lower(data[3:0], HEX0);

  assign LEDR[7:0] = data[7:0];
  
  always_comb begin
    pulse = GPIO_1[6];
    GPIO_0[5] = pulse;

    read = 1'b0; // No "read"

    // Status
    LEDR[8] = avail;
    LEDR[9] = pulse;
  end

endmodule: ChipInterface