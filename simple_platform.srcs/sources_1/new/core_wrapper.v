`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: University of Verona, Verona, Italy
// Engineer: Alessandro Danese (alessandro.danese@univr.it)
// 
// Create Date: 11/24/2018 03:03:37 PM
// Design Name: 
// Module Name: core_wrapper
// Project Name: simple_platform 
// Target Devices: pynq
// Tool Versions: Vivado 2017.4.1
// Description: 
// 
// Dependencies: wishbone_master
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////

module core_wrapper( 
   //============ Wishbone ============
   input             wb_clk,
   input             wb_rst,
   input             wb_ack,
   input             wb_err,
   input             wb_stall,
   output            wb_cyc,
   output            wb_stb,
   input   [31:0]    wb_dat_i,
   output            wb_we,
   output   [3:0]    wb_sel,
   output  [31:0]    wb_adr,
   output  [31:0]    wb_dat_o
   //===================================
);

reg [31:0] write_transaction_count=0;
reg [31:0] read_transaction_count=0;

final begin
$display(transactor_log, "\nwrite_transaction_count: %d\n", write_transaction_count++);
$display(transactor_log, "\nread_transaction_count: %d\n", read_transaction_count++);
end
// the function implemented in the testbench file
import "DPI-C" context task run_testbench();

reg        request;        // request is set to start a new bus transaction
reg        write;          // operation: write=1 (write) write=0 (read)
reg [31:0] address;        // the address written in the bus
reg [31:0] data_to_bus;    // the data written in the bus
reg [3:0]  sel;            // byte (data) selected in the bus
reg        reset;          // 
reg        busy;           //
reg [31:0] data_from_bus;  // the data read from the bus
reg        ready_from_bus; // it is set when the current bus transaction ended
reg        error_from_bus; // it is set if there is an error during the current bus transaction

initial begin 
   request      <= 1'b0;
   write        <= 1'b0;
   address      <= 32'b0;
   sel          <= 4'b0;
   data_to_bus  <= 32'b0;
end

buslayer_master master_interface(
   // binding core_wrapper's bus interface with
   // buslayer_master's bus interface 
   .wb_clk(wb_clk),
   .wb_rst(wb_rst),
   .wb_ack(wb_ack),
   .wb_err(wb_err),
   .wb_stall(wb_stall),
   .wb_cyc(wb_cyc),
   .wb_stb(wb_stb),
   .wb_dat_i(wb_dat_i),
   .wb_we(wb_we),
   .wb_sel(wb_sel),
   .wb_adr(wb_adr),
   .wb_dat_o(wb_dat_o),
   
   // binding core_wrapper's registers with 
   // buslayer_master's module interface
   .request(request),
   .write(write),
   .address(address),
   .data_to_bus(data_to_bus),
   .byte_sel(sel),
   .reset(reset),
   .busy(busy),
   .data_from_bus(data_from_bus),
   .ready_from_bus(ready_from_bus),
   .error_from_bus(error_from_bus)
);

//================================================================================
// Read/Write transactor definition
//================================================================================
// the log file for transactor's operations
integer transactor_log;

initial begin
    transactor_log = $fopen("transactor_log.txt");
    @(posedge p.core.wb_clk);
    run_testbench();
    
    $fclose(p.core.transactor_log);
    //$finish();
end


export "DPI-C" task write_transaction;
task write_transaction(input int addressIn, input int dataIn, 
                      input byte byteSelIn, output byte errorOut);
begin
    // waiting the posedge of the platform's clock
    @(posedge wb_clk); 
    
    $fdisplay(transactor_log, 
              "wishbone-WRITE (START): time:%0t\taddr:%x\tdata:%x\tbyteSel:%x", 
              $time, addressIn, dataIn, byteSelIn);
              
    if (reset == 1'b0 && busy == 1'b0) begin 
        // loading the new values coming from the testbench's variables
        // into the module core's registers
        address     <= addressIn;
        data_to_bus <= dataIn;
        sel         <= byteSelIn[3:0];
        write       <= 1'b1;
        request     <= 1'b1;
        @(posedge wb_clk);
        
        // waiting the reply from the addressed slave module
        wait((ready_from_bus || error_from_bus) == 1'b1);
        
        // loading the values coming from the module core's registers into 
        // the testbench's variables
        request     <= 1'b0;
        write       <= 1'b0;
        sel         <= 4'b0;
        errorOut           <= {{7'b0}, {error_from_bus}};

        //keep track of the number of write transactions
        write_transaction_count++;

        $fdisplay(transactor_log, 
                  "wishbone-WRITE  (STOP): time:%0t\terror:%d", 
                  $time, error_from_bus);
    end
    else begin // the interface is either busy or the reset signal is asserted 
        errorOut    <= 8'b1;
        $fdisplay(transactor_log, "wishbone-WRITE  (STOP): time:%0t\terror:1", $time);
    end 
    // wating the posedge of the platform's clock
    @(posedge wb_clk); 
end
endtask;

export "DPI-C" task read_transaction;
task read_transaction(input int addressIn, input int byteSelIn, 
                     output int dataOut, output byte errorOut);
begin
    // waiting the posedge of the platform's clock
    @(posedge wb_clk); 
    
    $fdisplay(transactor_log, 
              "wishbone-READ  (START): time:%0t\taddr:%x\tbyteSel:%x", 
              $time, addressIn, byteSelIn);
              
    if (reset == 1'b0 && busy == 1'b0) begin 
        // loading the new values coming from the testbench's variables
        // into the module core's registers
        address     <= addressIn;
        sel         <= byteSelIn[3:0];
        write       <= 1'b0;
        request     <= 1'b1;
        @(posedge wb_clk);
        
        // waiting the reply from the addressed slave module
        wait((ready_from_bus || error_from_bus) == 1'b1);
        @(posedge wb_clk);
        
        // loading the values coming from the module core's registers into 
        // the testbench's variables        
        request     <= 1'b0;
        write       <= 1'b0;
        sel         <= 4'b0;
        errorOut           <= {{7'b0}, {error_from_bus}};
        dataOut            <= data_from_bus;
         
        //keep track of the number of write transactions
        read_transaction_count++;

        $fdisplay(transactor_log, 
                  "wishbone-READ   (STOP): time:%0t\tdata:%x\terror:%x", 
                  $time, data_from_bus, error_from_bus);
    end
    else begin // the interface is either busy or the reset signal is asserted 
        errorOut    <= 8'b1;
        $fdisplay(transactor_log, "wishbone-READ  (STOP): time:%0t\terror:1", $time);
    end 
    // waiting the posedge of the platform's clock
    @(posedge wb_clk); 
end
endtask;
//--------------------------------------------------------------------------------

endmodule
