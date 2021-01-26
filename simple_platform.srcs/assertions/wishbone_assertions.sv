//`define WISHBONE sim1.p.bus
//
///*
//clk : clock signal
//reset: reset signal
//wb_we_m: (master signal) if true then it is a write cycle, otherwise it is a read cycle
//wb_cyc_m:(master signal) when true it means that a valid bus cycle is in progress
//wb_stb: when true, it indicates that the SLAVE is selected, a slave can respond only when wb_stb is true
//wb_ack_s: (slave signal, of array type, element ith of the array is refering to the ith slave), when true it indicates the termination of a normal bus cycle
//wb_stall_s: (slave signal, of array type, element ith of the array is refering to the ith slave), when true it indicates that the slave cannot accept additional transactions in its queue
//*/
//
//checker BusCheck(clk, reset,wb_we_m, wb_cyc_m, wb_stb, wb_ack_s,wb_stall_s);
//
//    clocking Buscheck_clocking @(posedge clk);
//
//        //Write cycle: master -> slave
//        property es3;
//		'b1
//		//Complete here
//        endproperty
//
//    endclocking
//
//    assert property (Buscheck_clocking.es3);
//
//
//endchecker: BusCheck
//
//bind `WISHBONE BusCheck bus_checker_instance(`WISHBONE.sysClk,`WISHBONE.sysRst, `WISHBONE.wb_we_m,`WISHBONE.wb_cyc_m,`WISHBONE.wb_stb_m, `WISHBONE.wb_ack_s, `WISHBONE.wb_stall_s);
//
