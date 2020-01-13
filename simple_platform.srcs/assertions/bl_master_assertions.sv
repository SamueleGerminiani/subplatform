`define BUSLAYER_MASTER sim1.p.core.master_interface
checker checker0(clk, wb_rst, wb_cyc, wb_stb,busy,request,write,ready_from_bus,error_from_bus);
    clocking mock @(posedge clk);

        property master_read_write_transaction;

        endproperty

    endclocking


   assert property (mock.master_read_write_transaction)begin

   end


    endchecker: checker0

bind `BUSLAYER_MASTER checker0 buslayer_master_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.wb_cyc, `BUSLAYER_MASTER.wb_stb, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.write,`BUSLAYER_MASTER.ready_from_bus,`BUSLAYER_MASTER.error_from_bus, sim1.p.core.transaction_count);
