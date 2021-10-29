`define BUSLAYER_MASTER sim1.p.core.master_interface
checker MasterBusCheck(clk,reset,busy,request,wb_we,write,wb_adr,address, wb_dat_o,data_to_bus, wb_sel,byte_sel);

    clocking MasterBusCheck_clocking @(posedge clk);


        //Common behavior for read/write cycles
        property p0;
            (1) |-> (1);
        endproperty

        /*Assertions for data flow: check that the out ports (wb_we,wb_adr,wb_data_o) have the same values of the registers one clock tick before (in a write cycle), use the "$past" operator (see the manual).*/
        property p1;
            //When a new write cycle begins
            (1)
            //then
            |->
            //check the data flow from register 'write' to port 'wb_we'
            (1);
        endproperty

        //The rest is similar to the the previous assertion
        
        property p2;
            (1) |-> (1);
        endproperty

        property p3;
            (1) |-> (1);
        endproperty

        property p4;
            (1) |-> (1);
        endproperty


    endclocking

    assert property (MasterBusCheck_clocking.p0);
    int p0ATCT=0;
    cover property (MasterBusCheck_clocking.p0) begin
        p0ATCT++;
    end

    assert property (MasterBusCheck_clocking.p1);
    int p1ATCT=0;
    cover property (MasterBusCheck_clocking.p1) begin
        p1ATCT++;
    end

    assert property (MasterBusCheck_clocking.p2);
    int p2ATCT=0;
    cover property (MasterBusCheck_clocking.p2) begin
        p2ATCT++;
    end

    assert property (MasterBusCheck_clocking.p3);
    int p3ATCT=0;
    cover property (MasterBusCheck_clocking.p3) begin
        p3ATCT++;
    end

    assert property (MasterBusCheck_clocking.p4);
    int p4ATCT=0;
    cover property (MasterBusCheck_clocking.p4) begin
        p4ATCT++;
    end

    final begin
        $display("bl_master.p0ATCT: %d", p0ATCT);
        $display("bl_master.p1ATCT: %d", p1ATCT);
        $display("bl_master.p2ATCT: %d", p2ATCT);
        $display("bl_master.p3ATCT: %d", p3ATCT);
        $display("bl_master.p4ATCT: %d", p4ATCT);
    end

    endchecker: MasterBusCheck

bind `BUSLAYER_MASTER MasterBusCheck masterBus_checker_instance(`BUSLAYER_MASTER.wb_clk,`BUSLAYER_MASTER.wb_rst, `BUSLAYER_MASTER.busy, `BUSLAYER_MASTER.request, `BUSLAYER_MASTER.wb_we, `BUSLAYER_MASTER.write, `BUSLAYER_MASTER.wb_adr, `BUSLAYER_MASTER.address, `BUSLAYER_MASTER.wb_dat_o, `BUSLAYER_MASTER.data_to_bus, `BUSLAYER_MASTER.wb_sel, `BUSLAYER_MASTER.byte_sel);
