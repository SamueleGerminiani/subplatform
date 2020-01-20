`define WISHBONE sim1.p.bus
checker BusCheck(clk, reset,wb_we_m, wb_cyc_m, wb_stb, wb_ack_s,wb_stall_s);
        static int fail_count=0;
        static int pass_count=0;

    clocking Buscheck_clocking @(posedge clk);
        property es3;
            'b1;
        endproperty
    endclocking


    assert property (Buscheck_clocking.es3)
        pass_count++;
    else
        fail_count++;

    final begin
        $display("WishboneCheck_Pass %d",pass_count);
        $display("WishboneCheck_Fail %d",fail_count);
    end

endchecker: BusCheck

bind `WISHBONE BusCheck bus_checker_instance(`WISHBONE.sysClk,`WISHBONE.sysRst, `WISHBONE.wb_we_m,`WISHBONE.wb_cyc_m,`WISHBONE.wb_stb_m, `WISHBONE.wb_ack_s, `WISHBONE.wb_stall_s);

