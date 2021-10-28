`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 12/05/2018 04:49:49 PM
// Design Name: 
// Module Name: simple_platform
// Project Name: simple_platform
// Target Devices: Pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: syscon, camellia_wrapper, serial_transmitter_wrapper, 
//               core_wrapper, wishbone_bus
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added bus, core, syscon and two slave modules
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module simple_platform();

localparam NUM_SLAVE = 2'd2;

// wires connecting master and slave
logic         clk           [NUM_SLAVE:0];
logic         rst           [NUM_SLAVE:0];
logic         ack           [NUM_SLAVE:0];
logic         err           [NUM_SLAVE:0];
logic         stall         [NUM_SLAVE:0];
logic         cyc           [NUM_SLAVE:0];
logic         stb           [NUM_SLAVE:0];
logic [31:0]  data_from_bus [NUM_SLAVE:0];
logic         we            [NUM_SLAVE:0];
logic  [3:0]  sel           [NUM_SLAVE:0];
logic [31:0]  adr           [NUM_SLAVE:0];  
logic [31:0]  data_to_bus   [NUM_SLAVE:0];

// clock and reset signals for the platform
logic sysClk, sysRst;

// reset and clock generator for wishbone protocol
syscon sys (
    .clk_o(sysClk),
    .rst_o(sysRst)
);

// SLAVE (0)
camellia_wrapper slave_0(
    .wb_clk   (clk[0]),
    .wb_rst   (rst[0]),
    .wb_cyc   (cyc[0]),
    .wb_stb   (stb[0]),
    .wb_we    (we[0]),
    .wb_sel   (sel[0]),
    .wb_dat_i (data_from_bus[0]), 
    .wb_adr   (adr[0]),
    .wb_ack   (ack[0]),
    .wb_err   (err[0]),
    .wb_stall (stall[0]),
    .wb_dat_o (data_to_bus[0])
);

// SLAVE (1)
serial_transmitter_wrapper slave_1(
    .wb_clk   (clk[1]),
    .wb_rst   (rst[1]),
    .wb_cyc   (cyc[1]),
    .wb_stb   (stb[1]),
    .wb_we    (we[1]),
    .wb_sel   (sel[1]),
    .wb_dat_i (data_from_bus[1]),
    .wb_adr   (adr[1]),
    .wb_ack   (ack[1]),
    .wb_err   (err[1]),
    .wb_stall (stall[1]),
    .wb_dat_o (data_to_bus[1])
);

// (MASTER)
core_wrapper core(
    .wb_clk   (clk[NUM_SLAVE]),
    .wb_rst   (rst[NUM_SLAVE]),
    .wb_ack   (ack[NUM_SLAVE]),
    .wb_err   (err[NUM_SLAVE]),
    .wb_stall (stall[NUM_SLAVE]),
    .wb_cyc   (cyc[NUM_SLAVE]),
    .wb_stb   (stb[NUM_SLAVE]),
    .wb_dat_i (data_from_bus[NUM_SLAVE]),
    .wb_we    (we[NUM_SLAVE]),
    .wb_sel   (sel[NUM_SLAVE]),
    .wb_adr   (adr[NUM_SLAVE]),
    .wb_dat_o (data_to_bus[NUM_SLAVE])
);

wishbone_bus #(.SLAVES(NUM_SLAVE)) bus(
    //---------------- Syscon--------------
    .sysClk(sysClk),
    .sysRst(sysRst),
    //-------------------------------------
    
    //----------------- Master-------------
    .wb_clk_m   (clk[NUM_SLAVE]),
    .wb_rst_m   (rst[NUM_SLAVE]),
    .wb_ack_m   (ack[NUM_SLAVE]),
    .wb_err_m   (err[NUM_SLAVE]),
    .wb_stall_m (stall[NUM_SLAVE]),
    .wb_cyc_m   (cyc[NUM_SLAVE]),
    .wb_stb_m   (stb[NUM_SLAVE]),
    .wb_dat_i_m (data_from_bus[NUM_SLAVE]),
    .wb_we_m    (we[NUM_SLAVE]),
    .wb_sel_m   (sel[NUM_SLAVE]),
    .wb_adr_m   (adr[NUM_SLAVE]),
    .wb_dat_o_m (data_to_bus[NUM_SLAVE]),
    //-------------------------------------
    
    //---------------- Slaves -------------
    .wb_clk_s   (clk[NUM_SLAVE-1:0]),
    .wb_rst_s   (rst[NUM_SLAVE-1:0]),
    .wb_ack_s   (ack[NUM_SLAVE-1:0]),
    .wb_err_s   (err[NUM_SLAVE-1:0]),
    .wb_stall_s (stall[NUM_SLAVE-1:0]),
    .wb_cyc_s   (cyc[NUM_SLAVE-1:0]),
    .wb_stb_s   (stb[NUM_SLAVE-1:0]),
    .wb_dat_i_s (data_from_bus[NUM_SLAVE-1:0]),
    .wb_we_s    (we[NUM_SLAVE-1:0]),
    .wb_sel_s   (sel[NUM_SLAVE-1:0]),
    .wb_adr_s   (adr[NUM_SLAVE-1:0]),
    .wb_dat_o_s (data_to_bus[NUM_SLAVE-1:0])
    //---------------------------------------
);

endmodule
