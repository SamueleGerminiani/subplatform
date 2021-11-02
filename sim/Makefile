# RTL source code
SRC=../src
TESTBENCH=$(SRC)/firmware/sp_fw.c

DUT=$(SRC)/platform/*.v \
	$(SRC)/platform/*.sv


SVA=$(SRC)/assertions/*.sv
	
DEFINE_TRACE=
FAULTS_LIST=

help:
	@clear
	@echo =========================================================================================
	@echo  " 								                                                       "
	@echo  " USAGE: make RECIPE|TARGET                                                            "
	@echo  " --- RECIPES ---------------------------------------------------------------------------"
	@echo  " simulation             => Performs: clean, compile_s, and run_s        			   "
	@echo  " ABV                    => Performs: clean, and Assertion-based Verification           "
	@echo  " faultC_bl_master       => Performs: clean, and fault coverage for buslayer (master)   "
	@echo  " faultC_camellia        => Performs: clean, and fault coverage for camellia            "
	@echo  " faultC_wishbone        => Performs: clean, and fault coverage for transmitter         "
	@echo  " --- TARGETS ---------------------------------------------------------------------------"
	@echo  " check_faults           => Performs: fault-coverage with faults.txt file               "
	@echo  " compile_s              => Compilings DUT                                              "
	@echo  " run_s                  => Runs simulation.                                            "
	@echo  "                                                                                       "
	@echo  " --- ADMINISTRATIVE TARGETS ------------------------------------------------------------"
	@echo  " help                   => Displays this message.                                      "
	@echo  " clean                  => Removes all intermediate and log files.                     "
	@echo  "				     			                                                       "
	@echo =========================================================================================

clean:
	@echo ===========================================================================
	@echo " Cleaning up                                                             "
	@echo ===========================================================================
	@find . -maxdepth 1 ! -name 'Makefile' -type f -exec rm -f {} +
	@find . -maxdepth 1 ! -name 'tools' ! -name '.' -type d -exec rm -rf {} +
	@mkdir vcd

compile_s:
	@echo ===========================================================================
	@echo " Compiling for simulation - START                                        "
	@echo ===========================================================================
	@vlib work
	@vlog +acc=rnbp -dpiheader ./work/vc_hdrs.h                                     \
		  $(ERROR) $(DEFINE_TRACE)                                                  \
		  -ccflags "-I ./work"  \
		  -sv $(DUT) $(SIM) $(TESTBENCH)
	@echo ===========================================================================
	@echo " Compiling for simulation - END                                          "
	@echo ===========================================================================

run_s:
	@echo ===========================================================================
	@echo " Simulation - START                                                      "
	@echo ===========================================================================
	@vsim -quiet -suppress vopt-13314,vsim-4075                                     \
		  -c sim1 -do "run 10000ns; exit"
	@echo ===========================================================================
	@echo " Simulation - END                                                        "
	@echo ===========================================================================

compile_ABV:
	@echo ===========================================================================
	@echo " Compiling for Assertion Based Verifcation - START                       "
	@echo ===========================================================================
	@vlib work
	@vlog +acc=rnbp -dpiheader ./work/vc_hdrs.h                                     \
		  $(ERROR) $(DEFINE_TRACE)                                                  \
		  -ccflags " -I ./work"                                                      \
		  -sv $(DUT) $(SIM) $(TESTBENCH) -cuname assertions -mfcu $(SVA)
	@echo ===========================================================================
	@echo " Compiling for Assertion Based Verifcation - END                         "
	@echo ===========================================================================

run_ABV:
	@echo ===========================================================================
	@echo " Simulation - START                                                      "
	@echo ===========================================================================
	@vsim -quiet -suppress vopt-13314,vsim-4075                                   \
	      -c sim1 -do "assertion fail -r / sim1; run 10000ns;                \
	                   assertion report -failed -r sim1 -file fault_report.txt;   \
					   exit"
	@cat fault_report.txt
	@echo ===========================================================================
	@echo " Simulation - END                                                        "
	@echo ===========================================================================

copy_fl:
	@cp $(FAULTS_LIST) ./faults.txt

check_faults:
	@echo ===========================================================================
	@echo " Fault coverage - START                                                  "
	@echo ===========================================================================
	@bash ./tools/check_faults.sh
	@echo ===========================================================================
	@echo " Fault coverage - END                                                    "
	@echo ===========================================================================

simulation: DEFINE_TRACE=+define+TRACE_DEBUG
simulation: clean compile_s run_s


faultC_bl_master: FAULTS_LIST=../faults/bl_master_faults.txt
faultC_bl_master: SVA=$(SRC)/assertions/bl_master_assertions.sv
faultC_bl_master: clean compile_ABV copy_fl check_faults

faultC_wishbone: FAULTS_LIST=../faults/wishbone_faults.txt
faultC_wishbone: SVA=$(SRC)/assertions/wishbone_assertions.sv
faultC_wishbone: clean compile_ABV copy_fl check_faults

faultC_camellia: FAULTS_LIST=../faults/camellia_faults.txt
faultC_camellia: SVA=$(SRC)/assertions/camellia_assertions.sv
faultC_camellia: clean compile_ABV copy_fl check_faults



ABV: clean compile_ABV run_ABV

.PHONY: help clean copy_fl
