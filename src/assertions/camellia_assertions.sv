//`define CAMELLIA sim1.p.slave_0.camallia_u
//
//checker camellia_checker(wb_clk, Krdy, Kvld, EncDec, Drdy, Dvld);
//	clocking clk_cone1 @(posedge wb_clk);
//
//        //Load a Key
//		property p0;
//		'b1
//		//Complete here
//		endproperty
//
//        //Common behavior encode/decode
//		property p1;
//		'b1
//		//Complete here
//		endproperty
//
//        //Encode a word
//		property p2;
//		'b1
//		//Complete here
//		endproperty
//
//        //Decode a word
//		property p3;
//		'b1
//		//Complete here
//		endproperty
//
//
//
//	endclocking
//
//	p0: assert property (clk_cone1.p0);
//	p1: assert property (clk_cone1.p1);
//	p2: assert property (clk_cone1.p2);
//	p3: assert property (clk_cone1.p3);
//endchecker: camellia_checker
//
//bind `CAMELLIA camellia_checker camellia_checker_instance(sim1.p.slave_0.slave_interface.wb_clk, `CAMELLIA.Krdy, `CAMELLIA.Kvld, `CAMELLIA.EncDec, `CAMELLIA.Drdy, `CAMELLIA.Dvld );
