`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/26/2018 02:02:07 PM
// Design Name: 
// Module Name: wishbone_bus
// Project Name: simple_platform
// Target Devices: pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: wishbone_bus_selector
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added wishbone_bus_selector
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module wishbone_bus 
#( parameter SLAVES=1)
 (  //------- Wishbone Syscon ----------
    input logic         sysClk,
    input logic         sysRst, 
    //----------------------------------
    
    //------- Wishbone (MASTER) --------
    output logic        wb_clk_m,
    output logic        wb_rst_m,
    output logic        wb_ack_m,
    output logic        wb_err_m,
    output logic        wb_stall_m,
    input  logic        wb_cyc_m,
    input  logic        wb_stb_m,
    output logic [31:0] wb_dat_i_m,
    input  logic        wb_we_m,
    input  logic [3:0]  wb_sel_m,
    input  logic [31:0] wb_adr_m,
    input  logic [31:0] wb_dat_o_m,
    //----------------------------------
    
    //------- Wishbone (SLAVE-n) ----------
    output logic        wb_clk_s   [SLAVES-1:0],
    output logic        wb_rst_s   [SLAVES-1:0],
    output logic        wb_cyc_s   [SLAVES-1:0],
    output logic        wb_stb_s   [SLAVES-1:0],
    output logic        wb_we_s    [SLAVES-1:0],
    output logic [3:0]  wb_sel_s   [SLAVES-1:0],
    output logic [31:0] wb_dat_i_s [SLAVES-1:0],
    output logic [31:0] wb_adr_s   [SLAVES-1:0],
    input  logic        wb_ack_s   [SLAVES-1:0],
    input  logic        wb_err_s   [SLAVES-1:0],
    input  logic        wb_stall_s [SLAVES-1:0],
    input  logic [31:0] wb_dat_o_s [SLAVES-1:0]
    //-------------------------------------
);

logic [31:0] current_slave;

wishbone_bus_selector selector(
    .address(wb_adr_m),
    .slave(current_slave)
);

genvar i; 

// =====================================================================
// Forwarding clock and reset signals to master and slaves
// =====================================================================
assign wb_clk_m = sysClk;
assign wb_rst_m = sysRst;

generate        
for (i = 0; i < SLAVES; i=i+1) begin      
  assign wb_clk_s[i] = sysClk;
  assign wb_rst_s[i] = sysRst;
end;
endgenerate
//----------------------------------------------------------------------

// =====================================================================
// Forwarding data, and address from master to slaves
// =====================================================================
generate        
for (i = 0; i < SLAVES; i=i+1) begin      
  assign wb_adr_s[i]   = wb_adr_m;
  assign wb_dat_i_s[i] = wb_dat_o_m;
end;
endgenerate 
//----------------------------------------------------------------------

// =====================================================================
// Forwarding cyc, stb, we, and sel from master to slaves
// =====================================================================
generate
for (i = 0; i < SLAVES; i=i+1) begin
    assign wb_cyc_s[i] = (current_slave == i) ? wb_cyc_m : 1'b0;
    assign wb_stb_s[i] = (current_slave == i) ? wb_stb_m : 1'b0;
    assign wb_we_s[i]  = (current_slave == i) ? wb_we_m  : 1'b0;
    assign wb_sel_s[i] = (current_slave == i) ? wb_sel_m : 3'b0;
end;
endgenerate
//----------------------------------------------------------------------

// =====================================================================
// Forwarding data, ack, error, stall values from a slave to master
// =====================================================================
assign wb_dat_i_m = (current_slave == SLAVES && wb_we_m == 1'b1)? 32'b0 :
                                                wb_dat_o_s[current_slave];              
assign wb_ack_m   = (current_slave == SLAVES) ? 1'b0 :
                                                wb_ack_s[current_slave];
assign wb_err_m   = (current_slave == SLAVES) ? 1'b0 :
                                                wb_err_s[current_slave];
assign wb_stall_m = (current_slave == SLAVES) ? 1'b0 : 
                                                wb_stall_s[current_slave];
//----------------------------------------------------------------------

endmodule

