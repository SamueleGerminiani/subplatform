`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:04:46 PM
// Design Name: 
// Module Name: buslayer_master
// Project Name: simple_platform 
// Target Devices: pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added FSM for wishbone protcol (B4)
//          2.00 - Splitted datapath in combinational and sequential datapath
//                 (outputs are stable during the read/write transaction)
//          3.00 - Renamed wishbone_master in buslayer_master
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module buslayer_master (
    //============ Wishbone ============
    //  control signals in Controller
    input  logic        wb_clk,
    input  logic        wb_rst,
    input  logic        wb_ack,
    input  logic        wb_err,
    input  logic        wb_stall,
    output logic        wb_cyc,
    output logic        wb_stb,
    input  logic [31:0] wb_dat_i,
    output logic        wb_we,
    output logic [3:0]  wb_sel,
    output logic [31:0] wb_adr,
    output logic [31:0] wb_dat_o,
    //===================================
    
    //==== Interface to upper module ==== 
    input  logic        request,
    input  logic        write,
    input  logic [31:0] address,
    input  logic [31:0] data_to_bus,
    input  logic [3:0]  byte_sel,
    output logic        reset,
    output logic        busy,
    output logic [31:0] data_from_bus,
    output logic        ready_from_bus,
    output logic        error_from_bus
    //=====================================
);


//----------------------------------------------------------------------
// Controller's states
//----------------------------------------------------------------------
enum logic [1:0]
{ RESET    = 2'd0,
  IDLE     = 2'd1,
  REQUEST  = 2'd2,
  WAIT_ACK = 2'd3
} state, next_state;
//----------------------------------------------------------------------

// =====================================================================
// the synchronous logic to hold the state
// =====================================================================
always_ff @(posedge wb_clk or posedge wb_rst) begin
    state <= (wb_rst)? RESET : next_state;
end
//----------------------------------------------------------------------

// =====================================================================
// The combinational logic to get the next state
// =====================================================================
always_comb begin
    case (state)
        RESET: next_state = IDLE;
        IDLE: begin
            next_state = ((request && !wb_ack && !wb_err && !wb_stall))? 
                         REQUEST : IDLE;
        end
        REQUEST: begin
            next_state = ((wb_ack || wb_err))? IDLE
                       : (wb_stall == 1'b1)? WAIT_ACK 
                       : REQUEST;
        end
        WAIT_ACK: begin
            next_state = ((wb_ack || wb_err))? IDLE 
                       : WAIT_ACK;   
        end
    endcase
end
//----------------------------------------------------------------------

// =====================================================================
// Datapath 
// =====================================================================
always_comb begin
    // in any state...
    reset          = wb_rst;   
    busy           = (state != IDLE && 'b0);
    ready_from_bus = (state == REQUEST || state == WAIT_ACK)? wb_ack : 1'b0;
    error_from_bus = (state == REQUEST || state == WAIT_ACK)? wb_err : 1'b0;
    data_from_bus  = (wb_rst == 1'b0)? wb_dat_i : 32'b0;
    wb_cyc         = (state == REQUEST || state == WAIT_ACK);
    wb_stb         = (state == REQUEST);
end

always_ff @(posedge wb_clk) begin
    if ((state == RESET) || 
        (state == WAIT_ACK && (wb_ack || wb_err))) begin
        wb_dat_o <= 32'b0;
        wb_adr   <= 32'b0;
        wb_sel   <= 4'b0;
        wb_we    <= 1'b0;
    end else
    if (state == IDLE) begin
        wb_dat_o <=  data_to_bus;
        wb_adr   <=  address;
        wb_sel   <=  byte_sel;
        wb_we    <=  write;
   end 
end
//----------------------------------------------------------------------

endmodule
