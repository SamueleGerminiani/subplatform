`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:09:45 PM
// Design Name: 
// Module Name: syscon
// Project Name: simple_platform
// Target Devices: Pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Added clock generator
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module syscon(
   output logic clk_o,
   output logic rst_o
);

logic clk, rst;

initial begin
   clk         <= 1'b0;
   rst         <= 1'b1;
   #20 rst     <= 1'b0;
end

//------------------------------------------------------------------------------
// main clock generation
//------------------------------------------------------------------------------
always #5 clk = ~clk;
//------------------------------------------------------------------------------

assign clk_o = clk;
assign rst_o = rst;

endmodule