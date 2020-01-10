`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:10:33 PM
// Design Name: 
// Module Name: sim1
// Project Name: simple_platform
// Target Devices: Pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: simple_platform
// 
// Revision:
// Revision 0.01 - File Created
//          1.00 - Defined the read/write transactors and
//                 simple_platform instance
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////



module sim1();

simple_platform p();

//================================================================================
// VCD traces
//================================================================================
initial begin
`ifdef TRACE_DEBUG
    $dumpfile("sim.vcd");
    $dumpvars(0, p);
`elsif TRACE_WB_MASTER
    $dumpfile("bl_master.vcd");
    $dumpvars(1, p.core.master_interface.wb_clk,
                 p.core.master_interface.wb_rst,
                 p.core.master_interface.wb_cyc,
                 p.core.master_interface.wb_stb,
                 p.core.master_interface.wb_we,
                 p.core.master_interface.wb_dat_i,
                 p.core.master_interface.wb_adr,
                 p.core.master_interface.wb_ack,
                 p.core.master_interface.wb_err,
                 p.core.master_interface.wb_stall,
                 p.core.master_interface.wb_dat_o,
                 p.core.master_interface.wb_sel,
                 p.core.master_interface.request,
                 p.core.master_interface.write,
                 p.core.master_interface.address,
                 p.core.master_interface.byte_sel,
                 p.core.master_interface.reset,
                 p.core.master_interface.busy,
                 p.core.master_interface.ready_from_bus,
                 p.core.master_interface.error_from_bus,
                 p.core.master_interface.data_to_bus,
                 p.core.master_interface.data_from_bus); 
`elsif TRACE_WB_SLAVE_0
    $dumpfile("bl_slave.vcd");
    $dumpvars(1, p.slave_0.slave_interface.wb_clk,
                 p.slave_0.slave_interface.wb_rst,
                 p.slave_0.slave_interface.wb_cyc,
                 p.slave_0.slave_interface.wb_stb,
                 p.slave_0.slave_interface.wb_we,
                 p.slave_0.slave_interface.wb_sel,
                 p.slave_0.slave_interface.wb_dat_i,
                 p.slave_0.slave_interface.wb_adr,
                 p.slave_0.slave_interface.wb_ack,
                 p.slave_0.slave_interface.wb_err,
                 p.slave_0.slave_interface.wb_stall,
                 p.slave_0.slave_interface.wb_dat_o,
                 p.slave_0.slave_interface.request,
                 p.slave_0.slave_interface.write,
                 p.slave_0.slave_interface.reset,
                 p.slave_0.slave_interface.address,
                 p.slave_0.slave_interface.data_from_bus,
                 p.slave_0.slave_interface.byte_sel,
                 p.slave_0.slave_interface.data_to_bus,
                 p.slave_0.slave_interface.done,
                 p.slave_0.slave_interface.err);
`elsif TRACE_WB_SLAVE_1
     $dumpfile("bl_slave.vcd");
    $dumpvars(1, p.slave_1.slave_interface.wb_clk,
                 p.slave_1.slave_interface.wb_rst,
                 p.slave_1.slave_interface.wb_cyc,
                 p.slave_1.slave_interface.wb_stb,
                 p.slave_1.slave_interface.wb_we,
                 p.slave_1.slave_interface.wb_sel,
                 p.slave_1.slave_interface.wb_dat_i,
                 p.slave_1.slave_interface.wb_adr,
                 p.slave_1.slave_interface.wb_ack,
                 p.slave_1.slave_interface.wb_err,
                 p.slave_1.slave_interface.wb_stall,
                 p.slave_1.slave_interface.wb_dat_o,
                 p.slave_1.slave_interface.request,
                 p.slave_1.slave_interface.write,
                 p.slave_1.slave_interface.reset,
                 p.slave_1.slave_interface.address,
                 p.slave_1.slave_interface.data_from_bus,
                 p.slave_1.slave_interface.byte_sel,
                 p.slave_1.slave_interface.data_to_bus,
                 p.slave_1.slave_interface.done,
                 p.slave_1.slave_interface.err);
`elsif CAMELLIA
    $dumpfile("camellia.vcd");
    $dumpvars(1, p.slave_0.slave_interface.wb_clk,
                 p.slave_0.camallia_u.RSTn,
                 p.slave_0.camallia_u.EN,
                 p.slave_0.camallia_u.EncDec,
                 p.slave_0.camallia_u.Drdy,
                 p.slave_0.camallia_u.Krdy,
                 p.slave_0.camallia_u.BSY,
                 p.slave_0.camallia_u.Kvld,
                 p.slave_0.camallia_u.Dvld);
 `elsif SERIAL_TRANSMITTER
    $dumpfile("serial_transmitter.vcd");
    $dumpvars(1, p.slave_1.slave_interface.wb_clk,
                 p.slave_1.transmitter.rst,
                 p.slave_1.transmitter.data_to_send,
                 p.slave_1.transmitter.send,
                 p.slave_1.transmitter.done,
                 p.slave_1.transmitter.val);
 `endif
end
//--------------------------------------------------------------------------------

endmodule