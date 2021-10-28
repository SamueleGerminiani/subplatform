`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:05:05 PM
// Design Name: 
// Module Name: wishbone_slave
// Project Name: simple_platform
// Target Devices: pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added FSM for Wishbone protocol (B4)
//          2.00 - Renamed wishbone_slave in buslayer_slave
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module buslayer_slave(
    //============ Wishbone ============
    input  logic        wb_clk,
    input  logic        wb_rst,
    input  logic        wb_cyc,
    input  logic        wb_stb,
    input  logic        wb_we,
    input  logic [3:0]  wb_sel,
    input  logic [31:0] wb_dat_i,
    input  logic [31:0] wb_adr,
    output logic        wb_ack,
    output logic        wb_err,
    output logic        wb_stall,
    output logic [31:0] wb_dat_o,
    //===================================  
    
    //==== Interface to upper module ==== 
    output logic        request,
    output logic        write,
    output logic        reset,
    output logic [31:0] address,
    output logic [31:0] data_from_bus,
    output logic [3:0]  byte_sel,
    input  logic [31:0] data_to_bus,
    input  logic        done,
    input  logic        err
    //=====================================
);

//----------------------------------------------------------------------
// Controller's states
//----------------------------------------------------------------------
enum logic [1:0]
{ RESET        = 2'd0,
  IDLE         = 2'd1,
  REQUEST      = 2'd2,
  WAIT_CYC_LOW = 2'd3
} state, next_state;
//----------------------------------------------------------------------

// registers to stabilize signals to bus until wb_cyc is unset
logic          done_ff, err_ff;
logic [31 : 0] data_to_bus_ff;
 
// =====================================================================
// the synchronous logic to update the state
// =====================================================================
always_ff @(posedge wb_clk or posedge wb_rst) begin
    state <= (wb_rst)? RESET : next_state;
end
//----------------------------------------------------------------------

// =====================================================================
// The combinational logic to describe the next state
// =====================================================================
always_comb begin
    case (state)
        RESET: next_state = IDLE;
        IDLE:  next_state = ((wb_cyc && wb_stb) == 1'b1)? REQUEST : IDLE;
        REQUEST: begin
            next_state = (((err || done) && !wb_cyc) == 1'b1)? IDLE
                       : (((err || done) &&  wb_cyc) == 1'b1)? WAIT_CYC_LOW
                       : REQUEST;
        end
        WAIT_CYC_LOW: next_state = (wb_cyc == 1'b0)? IDLE : WAIT_CYC_LOW;
    endcase
end
//----------------------------------------------------------------------
 
// =====================================================================
// Datapath 
// =====================================================================
always_ff @(posedge wb_clk) begin : sequential_logic_for_outputs
    case (state)
        RESET: begin
            write           <= 1'b0;
            byte_sel        <= 4'b0;
            address         <= 32'b0;
            data_from_bus   <= 32'b0;
            data_to_bus_ff  <= 32'b0;
            done_ff         <= 1'b0;
            err_ff          <= 1'b0;  
        end
        IDLE: begin
            // data and control values coming from the 
            // bus are formwared to the upper module
            write           <= wb_we;
            byte_sel        <= wb_sel;
            address         <= wb_adr;
            data_from_bus   <= wb_dat_i;
            // outputs to bus is reset
            data_to_bus_ff  <= 32'b0;
            done_ff         <=  1'b0;
            err_ff          <=  1'b0;
        end
        REQUEST: begin
            // outputs to uppermodule is stable
            // data and control values coming from the
            // uppermodule are formwared to the bus
            data_to_bus_ff  <= data_to_bus;
            done_ff         <= done;
            err_ff          <= err;
        end
        WAIT_CYC_LOW: begin
             // outputs to bus is stable
             // outputs to uppermodel is reset
             write           <= 1'b0;
             byte_sel        <= 4'b0;
             address         <= 32'b0;
             data_from_bus   <= 32'b0;
        end
    endcase
end

always_comb begin : combinational_logic_for_outputs
   
`ifdef BLS_ERR_1
    wb_ack   = done_ff;
    wb_err   = err_ff;
    wb_dat_o = data_to_bus_ff;
`else
    if (state == RESET || state == IDLE || wb_cyc == 1'b0) begin
        wb_ack   = 1'b0;
        wb_err   = 1'b0;
        wb_dat_o = 32'b0;
    end
    else begin
        wb_ack   = (state == REQUEST)? done : done_ff;
        wb_err   = (state == REQUEST)? err : err_ff;
        wb_dat_o = (state == REQUEST)? data_to_bus : data_to_bus_ff;
    end
`endif
       
   reset    = wb_rst;    
   request  = (state == REQUEST);
   wb_stall = (state == RESET || state == IDLE)? 1'b0 
            : (wb_cyc && !(wb_ack || wb_err));
end
//----------------------------------------------------------------------
     


endmodule


