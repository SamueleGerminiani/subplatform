`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 11/28/2018 03:22:48 PM
// Design Name: 
// Module Name: wishbone_bus_selector
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

//`include "address_ranges.vh"

module wishbone_bus_selector
#( parameter SLAVES=1)
(  input  logic [31:0] address,
   output logic [31:0] slave
);

// =====================================================================
// Support function to enable the addressed slave device
// =====================================================================
function in_range;
    input [31:0] address;
    input [31:0] base_address;
    input [31:0] last_address;
begin
    in_range = (address >= base_address && address <= last_address)? 1 : 0;
end
endfunction
//----------------------------------------------------------------------

assign slave = in_range ( address, 32'h0,  32'h37 )? 32'b0 :
               in_range ( address, 32'h60, 32'h60 )? 32'b1 :
               SLAVES;
endmodule
