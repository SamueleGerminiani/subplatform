`define BUSLAYER_MASTER sim1.p.core.master_interface
checker checker0(clk, wb_rst, wb_cyc, wb_stb,busy,request,write,ready_from_bus,error_from_bus);
    clocking mock @(posedge clk);

        property master_read_write_transaction;
            ((request && !busy) ##1 busy) |-> (
                (busy [*0:$] ##1 ready_from_bus ##1 !request [->1] ##1 (!busy && !ready_from_bus))
                /*
                or
                ((busy [->1] ##1 (error_from_bus)) |-> (!request ##1 (!busy && !error_from_bus)))
                */
            );
        endproperty


    endclocking

   int pass_count=0;
   int fail_count=0;


   assert property (mock.master_read_write_transaction)begin
       pass_count++;
   end
   else begin
       fail_count++;
   end

   final begin 
       $display("Pass %d",pass_count);
       $display("Fail %d",fail_count);
   end

    endchecker: checker0

bind `BUSLAYER_MASTER checker0 buslayer_master_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.wb_cyc, `BUSLAYER_MASTER.wb_stb, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.write,`BUSLAYER_MASTER.ready_from_bus,`BUSLAYER_MASTER.error_from_bus);
