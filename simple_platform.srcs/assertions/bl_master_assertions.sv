`define BUSLAYER_MASTER sim1.p.core.master_interface
checker MasterBusCheck(clk,reset,busy,request,wb_we,write,wb_adr,address, wb_dat_o,data_to_bus, wb_sel, byte_sel);

    clocking MasterBusCheck_clocking @(posedge clk);

        property es1;
            !busy && request |=> busy;
        endproperty

        property es2_a;
            'b1;
        endproperty

        property es2_b;
            'b1;
        endproperty

        property es2_c;
            'b1;
        endproperty

        property es2_d;
            'b1;
        endproperty

    endclocking

    assert property (MasterBusCheck_clocking.es1);
    assert property (MasterBusCheck_clocking.es2_a);
    assert property (MasterBusCheck_clocking.es2_b);
    assert property (MasterBusCheck_clocking.es2_c);
    assert property (MasterBusCheck_clocking.es2_d);

    endchecker: MasterBusCheck

bind `BUSLAYER_MASTER MasterBusCheck masterBus_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.wb_we, `BUSLAYER_MASTER.write, `BUSLAYER_MASTER.wb_adr, `BUSLAYER_MASTER.address, `BUSLAYER_MASTER.wb_dat_o, `BUSLAYER_MASTER.data_to_bus, `BUSLAYER_MASTER.wb_sel, `BUSLAYER_MASTER.byte_sel);
