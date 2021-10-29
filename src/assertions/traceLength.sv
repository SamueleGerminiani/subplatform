`define BUSLAYER_MASTER sim1.p.core.master_interface
checker TLChecker(clk,reset,busy,request,wb_we,write,wb_adr,address, wb_dat_o,data_to_bus, wb_sel,byte_sel);

    clocking TLChecker_clocking @(posedge clk);


        property ptl;
            always(1);
        endproperty

    endclocking

    int tl=0;
    cover property (TLChecker_clocking.ptl)begin
        tl++;
    end


    final begin
        $display("trace length: %d", tl);
    end

    endchecker: TLChecker

bind `BUSLAYER_MASTER TLChecker tl_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.wb_we, `BUSLAYER_MASTER.write, `BUSLAYER_MASTER.wb_adr, `BUSLAYER_MASTER.address, `BUSLAYER_MASTER.wb_dat_o, `BUSLAYER_MASTER.data_to_bus, `BUSLAYER_MASTER.wb_sel, `BUSLAYER_MASTER.byte_sel);
