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
  output logic [ 3:0] HEX7, HEX6, HEX5, HEX4, HEX3, HEX2, HEX1, HEX0);

  logic rst_n;
  assign rst_n = KEY[0];
  
  always_comb begin
    GPIO_0[6] =GPIO_1[6];
    GPIO_0[10]=1'b1;
    GPIO_0[28]=1'b1;
  end
  
  // logic [31:0] count;
  // always_ff @(posedge CLOCK_50) begin
  //   GPIO_0[5] = (count >= 25000? 0 : 1);
  //   count = (count <= 49999? count + 1 : 0);
  // end

  localparam PULSE_CT = 7500;
  localparam N_MOD = 2;
  localparam L = 10000;
  localparam N_PKT = 8;
  localparam PRE_CT = 4;
  logic             clk;
  logic [N_PKT-1:0] data;
  logic             start;
  logic             avail;
  logic             pulse;
  Encoder #(.PULSE_CT(PULSE_CT), .N_MOD(N_MOD), .L(L), .N_PKT(N_PKT),
    .PRE_CT(PRE_CT)) enc(.*);
  always_comb begin
    clk = CLOCK_50;
    data = SW[N_PKT-1:0];
    start = 1'b1; //TODO On demand?
    //TODO avail
    GPIO_0[5] = pulse;
  end
endmodule: ChipInterface
