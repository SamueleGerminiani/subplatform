`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/28/2018 04:24:16 PM
// Design Name: 
// Module Name: wishbone_interface
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


interface wishbone_interface (input logic wb_clk, wb_rst);
  //logic        wb_clk;
  //logic        wb_rst;
  logic        wb_ack;
  logic        wb_err;
  logic        wb_stall;
  logic        wb_cyc;
  logic        wb_stb;
  logic [31:0] wb_dat_i;
  logic        wb_we;
  logic [3:0]  wb_sel;
  logic [31:0] wb_adr;
  logic [31:0] wb_dat_o;

modport master (input wb_ack, wb_err, wb_stall, wb_dat_i,
                output wb_cyc, wb_stb, wb_we, wb_sel, wb_adr, wb_dat_o);
                
modport slave  (input wb_cyc, wb_stb, wb_dat_i, wb_we, wb_sel, wb_adr,
                output wb_ack, wb_err, wb_stall, wb_dat_o);
             
endinterface
