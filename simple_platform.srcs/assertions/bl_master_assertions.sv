`define BUSLAYER_MASTER sim1.p.core.master_interface
checker MasterBusCheck(clk,reset,busy,request,wb_we,write,wb_adr,address, wb_dat_o,data_to_bus, wb_sel,byte_sel);

    clocking MasterBusCheck_clocking @(posedge clk);


        //Common behavior for read/write cycles
        property p0;
            (!busy && request) |=> busy;
        endproperty

        /*Assertions for data flow: check that the out ports (wb_we,wb_adr,wb_data_o) have the same values of the
        registers one clock tick before.*/
        property p1;
            //When a new write cycle begins
            (!busy && request && write)
            //then
            |->
            //check the data flow from register 'write' to port 'wb_we'
            nexttime[1]( busy && wb_we == $past(write, 1));
        endproperty

        property p2;
            !(request && write) ##1 (request && write) |-> nexttime[1](wb_adr == $past(address, 1));
        endproperty

        property p3;
            !(request && write) ##1 (request && write) |-> nexttime[1](wb_dat_o == $past(data_to_bus, 1));
        endproperty

        property p4;
            !(request && write) ##1 (request && write) |-> nexttime[1](wb_sel == $past(byte_sel, 1));
        endproperty
    endclocking


    assert property (MasterBusCheck_clocking.p1);
    assert property (MasterBusCheck_clocking.p2);
    assert property (MasterBusCheck_clocking.p3);
    assert property (MasterBusCheck_clocking.p4);

    endchecker: MasterBusCheck

bind `BUSLAYER_MASTER MasterBusCheck masterBus_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.wb_we, `BUSLAYER_MASTER.write, `BUSLAYER_MASTER.wb_adr, `BUSLAYER_MASTER.address, `BUSLAYER_MASTER.wb_dat_o, `BUSLAYER_MASTER.data_to_bus, `BUSLAYER_MASTER.wb_sel, `BUSLAYER_MASTER.byte_sel);
