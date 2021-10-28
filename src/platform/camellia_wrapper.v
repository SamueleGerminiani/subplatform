`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/29/2018 04:36:28 PM
// Design Name: 
// Module Name: camellia_wrapper
// Project Name: simple_platform
// Target Devices: Pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: camellia, wishbone_slave
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added memory mapped registers and bind register-camellia
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

// This module is memory-mapped according the follwing 
// table address -> data.
// N.B. the address has granularity a word!!!!
//     R/W                                                   offset from 
//   policy                         Key                     CAMELLIA_BASE
//             ---------------------------------------------   dec  hex   data2cam
//     R/W     | key[3]   | key[2]   | key[1]   | key[0]   |   + 0   (0)      0
//     R/W     | key[7]   | key[6]   | key[5]   | key[4]   |   + 4   (4)      1
//     R/W     | key[11]  | key[10]  | key[9]   | key[8]   |   + 8   (8)      2
//     R/W     | key[15]  | key[14]  | key[13]  | key[12]  |   + 12  (c)      3
//             ---------------------------------------------
//                               Data (int)
//             ---------------------------------------------
//     R/W     | data[3]  | data[2]  | data[1]  | data[0]  |   + 16 (10)      4
//     R/W     | data[7]  | data[6]  | data[5]  | data[4]  |   + 20 (14)      5
//     R/W     | data[11] | data[10] | data[9]  | data[8]  |   + 24 (18)      6 
//     R/W     | data[15] | data[14] | data[13] | data[12] |   + 28 (1c)      7
//             ---------------------------------------------
//                               Control (in)
//             ---------------------------------------------
//     R/W     |   krdy   |   Drdy   |  EncDec  |   EN     |   + 32 (20)      8
//             ---------------------------------------------
//                               Data (out)                                 
//              ---------------------------------------------               data4cam
//      R       | data[3]  | data[2]  | data[1]  | data[0]  |   + 36 (24)     9
//      R       | data[7]  | data[6]  | data[5]  | data[4]  |   + 40 (28)    10
//      R       | data[11] | data[10] | data[9]  | data[8]  |   + 44 (2c)    11
//      R       | data[15] | data[14] | data[13] | data[12] |   + 48 (30)    12
//              ---------------------------------------------
//                              Control (out)
//              ---------------------------------------------
//      R       |          |          |          |   BSY     |  + 52 (34)    13
//              ---------------------------------------------

`define CAMELLIA_BASE 32'h0

module camellia_wrapper(
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

// binding signals between camellia_wrapper and wishbone_slave
logic request, write, reset, err, done;
// the address of data
logic [31:0] address;
// selected byte of data
logic  [3:0] byte_sel;
// data read from the bus
logic [3:0][7:0] data_from_bus;
// data written in the bus
logic [31:0] data_to_bus;

//
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
    .reset(reset),
    .address(address),
    .data_from_bus(data_from_bus),
    .byte_sel(byte_sel),
    .data_to_bus(data_to_bus),
    .done(done),
    .err(err)
    //=================================
);

// control (out) signals from camellia
logic bsy;
// the address of the module minus its base address
logic [31:0] mudule_addres;
// the word (in) selected
logic [31:0] wordIn_sel;
// the word (out) selected
logic [1:0] wordOut_sel;
// array of 36 8-bit vectors
logic [3:0][7:0] data2cam [8:0];
// data (out) signal from camellia
logic [3:0][7:0] data4cam [3:0];

//
camellia camallia_u (
    .CLK    (wb_clk),
    .RSTn   (!reset), // active low!    
    // control (in)
    .EN     (data2cam[8][0][0]), 
    .EncDec (data2cam[8][1][0]),
    .Drdy   (data2cam[8][2][0]), 
    .Krdy   (data2cam[8][3][0]),
    // data (in)
    .Din    ({{data2cam[7]}, {data2cam[6]}, 
             {data2cam[5]}, {data2cam[4]}}),              
    // key (in)
    .Kin    ({{data2cam[3]}, {data2cam[2]}, 
             {data2cam[1]},  {data2cam[0]}}),     
    // data (out)
    .Dout   ({{data4cam[0]}, {data4cam[3]}, 
              {data4cam[2]},  {data4cam[1]}}),
    // control (out)
    .BSY    (bsy), 
    .Kvld   (), 
    .Dvld   ()
);

//
always_comb begin
    mudule_addres = (address - `CAMELLIA_BASE);
    // ...
    wordIn_sel = {{28'b0}, {mudule_addres[5:2]}};
    // ...
    wordOut_sel = {{28'b0}, {wordIn_sel[1:0]}};
    // the camellia wrapper replies immediately (always!)
    done = request;
    // there is an errror if:
    // 1) the address has not granulary a word
    // 2) the value of the address signal is out the range of the memory-mapped registers;
    // 3) there is a write request for a control (out) signal of camellia.
    err = request && 
          ( mudule_addres[1:0] != 2'b0 || 
            mudule_addres > 32'h34     || (write && mudule_addres >= 32'h24));
end

// the sequential logic updating the memory mapped registers' value
always_ff @(posedge wb_clk or posedge reset) begin
    if (reset) begin
        for (integer i = 0; i < 9; i++) 
            data2cam[i] <= 8'b0;
    end
    else begin
        if ((request && write && !err) == 1'b1) begin                                        
            for (integer k = 0;k < 4; k++) begin
                if (byte_sel[k]) 
                    data2cam[wordIn_sel][k] <= (wordIn_sel == 8)? data_from_bus[0]
                                                                : data_from_bus[k];
            end
        end
       
        // if bsy signal is set, then the command is acquired by camellia.
        // We can unset the key/data-ready control input
        if (bsy) begin
            data2cam[8][1] <= 8'b0;
            data2cam[8][2] <= 8'b0;
            data2cam[8][3] <= 8'b0;
        end
   end
end

//
always_comb begin
    if ((request && !write && !err) == 1'b1) begin
       data_to_bus[7:0] = (!byte_sel[0])? 8'b0
                        : (wordIn_sel < 9)?   data2cam[wordIn_sel][0] 
                        : (wordIn_sel < 13)? data4cam[wordOut_sel][0] 
                        : {{7'b0}, {bsy}};
                        
       data_to_bus[15:8] = (!byte_sel[1])? 8'b0
                        : (wordIn_sel < 9)? data2cam[wordIn_sel][1] 
                        : data4cam[wordOut_sel][1]; 
                         
       data_to_bus[23:16] = (!byte_sel[2])? 8'b0
                        : (wordIn_sel < 9)? data2cam[wordIn_sel][2] 
                        : data4cam[wordOut_sel][2];   
                                    
      data_to_bus[31:24] = (!byte_sel[3])? 8'b0
                        : (wordIn_sel < 9)? data2cam[wordIn_sel][3] 
                        : data4cam[wordOut_sel][3]; 
    end   
    else begin
        data_to_bus = 32'hffffffff;
    end
end



endmodule
