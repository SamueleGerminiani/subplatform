`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:04:07 PM
// Design Name: 
// Module Name: serial_transmitter_wrapper
// Project Name: simple_platform
// Target Devices: pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Binded serial transmitter and wishbone_slave
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module serial_transmitter_wrapper(
    //============ Wishbone ============
    input  logic        wb_clk,
    input  logic        wb_rst,
    input  logic        wb_cyc,
    input  logic        wb_stb,
    input  logic        wb_we,
    input  logic  [3:0] wb_sel,
    input  logic [31:0] wb_dat_i,
    input  logic [31:0] wb_adr,
    output logic        wb_ack,
    output logic        wb_err,
    output logic        wb_stall,
    output logic [31:0] wb_dat_o
    //===================================  
);

// clock and reset signals
logic clk, rst;
// the selected byte of data
logic  [3:0] byte_sel;
// data read from the bus
logic [31:0] data_from_bus;
// control signals
logic request, write, done, err;
// the data formwared to the transmitter
logic [7:0] data;

buslayer_slave slave_interface (
    //============ Wishbone ============
    .wb_clk(wb_clk),
    .wb_rst(wb_rst),
    .wb_cyc(wb_cyc),
    .wb_stb(wb_stb),
    .wb_we(wb_we),
    .wb_sel(wb_sel),
    .wb_dat_i(wb_dat_i),
    .wb_adr(wb_adr),
    .wb_ack(wb_ack),
    .wb_err(wb_err),
    .wb_stall(wb_stall),
    .wb_dat_o(wb_dat_o),
    //=================================
    
    //======== Module (wrapper) =======
    .request(request),
    .write(write),
    .reset(rst),
    .address(),
    .data_from_bus(data_from_bus),
    .byte_sel(byte_sel),
    .data_to_bus(32'b0),
    .done(done),
    .err(err)
    //=================================
);

serial_transmitter transmitter (
    .clk(wb_clk),
    .rst(rst),
    .data(data),
    .send(request && !err),
    .done(done),
    .val()
);


always_comb begin
   err = (request == 1'b1) && 
             (write == 1'b0 || 
                (byte_sel[3:0] != 4'b0001 && 
                 byte_sel[3:0] != 4'b0010 &&
                 byte_sel[3:0] != 4'b0100 &&
                 byte_sel[3:0] != 4'b1000)); 
                 
   case (byte_sel)
    4'b0001: data = data_from_bus[7:0];
    4'b0010: data = data_from_bus[15:8];
    4'b0100: data = data_from_bus[23:16];
    4'b1000: data = data_from_bus[31:24];
    default data = 8'b0;
   endcase
end
 
endmodule

