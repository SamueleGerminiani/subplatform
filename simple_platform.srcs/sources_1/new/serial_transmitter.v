`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it) 
// 
// Create Date: 11/24/2018 03:08:41 PM
// Design Name: 
// Module Name: serial_transmitter
// Project Name: simple_platform
// Target Devices: Pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added Controller fsm e datapath logic 
//          2.00 - data_to_send is left shifted each clock cycle after
//                 the send command
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module serial_transmitter(
   input  logic       clk,
   input  logic       rst,
   input  logic [7:0] data,
   input  logic       send,
   output logic       done,
   output logic       val
);

logic [7:0] data_to_send;

//----------------------------------------------------------------------
// Controller's states
//----------------------------------------------------------------------
enum logic [3:0]
{ RESET    = 4'd0,
  IDLE     = 4'd1,
  SEND_0   = 4'd2,
  SEND_1   = 4'd3,
  SEND_2   = 4'd4,
  SEND_3   = 4'd5,
  SEND_4   = 4'd6,
  SEND_5   = 4'd7,
  SEND_6   = 4'd8,
  SEND_7   = 4'd9
} state, next_state;
//----------------------------------------------------------------------

// =====================================================================
// the synchronous logic to hold the state
// =====================================================================
always_ff @(posedge clk or posedge rst) begin
    state <= (rst)? RESET : next_state;
end
//----------------------------------------------------------------------

// =====================================================================
// The combinational logic to get the next state
// =====================================================================
always_comb begin
    case (state)
        RESET : next_state  = IDLE;
        IDLE  : next_state  = (send == 1'b1)? SEND_0 : IDLE;
        SEND_0: next_state  = SEND_1;
        SEND_1: next_state  = SEND_2;
        SEND_2: next_state  = SEND_3;
        SEND_3: next_state  = SEND_4;
        SEND_4: next_state  = SEND_5;
        SEND_5: next_state  = SEND_6;
        SEND_6: next_state  = SEND_7;
        SEND_7: next_state  = IDLE;
        default: next_state = IDLE;
    endcase
end
//----------------------------------------------------------------------

// =====================================================================
// Datapath 
// =====================================================================
always_ff @(posedge clk) begin
    case (state) 
        RESET:   data_to_send <= 8'b0;
        IDLE:    data_to_send <= (send == 1'b1)? data : 8'b0;
        default: data_to_send <= (send == 1'b1)? (data_to_send >> 1) : data_to_send;
    endcase
end

always_comb begin
    // in any state...
    done = (state == SEND_7);
    val  = data_to_send[0];
end
//----------------------------------------------------------------------
       

endmodule
