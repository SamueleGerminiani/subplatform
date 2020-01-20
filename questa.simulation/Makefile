# RTL source code
PROJECT=../simple_platform
TESTBENCH=../firmware/sp_fw.c
ASSERTIONS=../psl/*.psl
#ERROR=+define+BLS_ERR_1

# ---------------------- DO NOT TOUCH BELOW THIS LINE --------------------------
DUT=$(PROJECT).srcs/sources_1/new/*.v \
	$(PROJECT).srcs/sources_1/new/*.sv \
    $(PROJECT).srcs/sources_1/imports/platform/*.v

SIM=$(PROJECT).srcs/sim_1/new/sim1.v

SVA=$(PROJECT).srcs/assertions/*.sv
	
DEFINE_TRACE=
FAULTS_LIST=

help:
	@clear
	@echo =========================================================================================
	@echo  " 								                                                       "
	@echo  " USAGE: make RECEPIE|TARGET                                                            "
	@echo  " Authors: Alessandro Danese (alessandro.danese@univr.it)                                "
	@echo  "          Samuele Germiniani (samuele.germiniani@univr.it)                                "
	@echo  " 								                                                       "
	@echo  " --- RECIPES ---------------------------------------------------------------------------"
	@echo  " simulation             => Performs: clean, compile_s, and run_s        			   "
	@echo  " mining_bl_master       => Performs: clean, and assertion mining for buslayer (master) "
#	@echo  " mining_bl_slave_0      => Performs: clean, and assertion mining for buslayer (slave_0)"
#	@echo  " mining_bl_slave_1      => Performs: clean, and assertion mining for buslayer (slave_1)"
	@echo  " mining_camellia        => Performs: clean, and assertion mining for camellia          "
	@echo  " mining_serial_transmitter     => Performs: clean, and assertion mining for transamitter      "
	@echo  " ABV                    => Performs: clean, and Assertion-based Verification           "
	@echo  " faultC_bl_master       => Performs: clean, and fault coverage for buslayer (master)   "
#	@echo  " faultC_bl_slave        => Performs: clean, and fault coverage for buslayer (slave)    "
	@echo  " faultC_camellia        => Performs: clean, and fault coverage for camellia            "
	@echo  " faultC_transmitter     => Performs: clean, and fault coverage for transmitter         "
	@echo  "                                                                                       "
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

compile_s:
	@echo ===========================================================================
	@echo " Compiling for simulation - START                                        "
	@echo ===========================================================================
	@vlib work
	@vlog -modelsimini ../modelsim.ini +acc=rnbp -dpiheader ./work/vc_hdrs.h                                     \
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
	@vsim -modelsimini ../modelsim.ini -quiet -suppress vopt-13314,vsim-4075                                     \
		  -c sim1 -do "run 1ms; exit"
	@echo ===========================================================================
	@echo " Simulation - END                                                        "
	@echo ===========================================================================

compile_ABV:
	@echo ===========================================================================
	@echo " Compiling for Assertion Based Verifcation - START                       "
	@echo ===========================================================================
	@vlib work
	@vlog -modelsimini ../modelsim.ini +acc=rnbp -dpiheader ./work/vc_hdrs.h                                     \
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
	@vsim -modelsimini ../modelsim.ini -quiet -suppress vopt-13314,vsim-4075                                   \
	      -c sim1 -do "assertion fail -r / sim1; run 1ms;                \
	                   assertion report -failed -r sim1 -file fault_report.txt;   \
					   exit"
	@cat fault_report.txt
	@echo ===========================================================================
	@echo " Simulation - END                                                        "
	@echo ===========================================================================

assertion_mining:
	@echo ===========================================================================
	@echo " Assertion mining - START                                                "
	@echo ===========================================================================
	@./tools/mine_assertions.sh $(NAME)
	@echo ===========================================================================
	@echo " Assertion mining - END                                                  "
	@echo ===========================================================================

copy_fl:
	@cp $(FAULTS_LIST) ./faults.txt

check_faults:
	@echo ===========================================================================
	@echo " Fault coverage - START                                                  "
	@echo ===========================================================================
	@./tools/check_faults.sh
	@echo ===========================================================================
	@echo " Fault coverage - END                                                    "
	@echo ===========================================================================

simulation: DEFINE_TRACE=+define+TRACE_DEBUG
simulation: clean compile_s run_s

mining_bl_master: DEFINE_TRACE=+define+TRACE_WB_MASTER
mining_bl_master: NAME=bl_master
mining_bl_master: clean compile_s run_s assertion_mining

mining_serial_transmitter: DEFINE_TRACE=+define+SERIAL_TRANSMITTER
mining_serial_transmitter: NAME=serial_transmitter
mining_serial_transmitter: clean compile_s run_s assertion_mining

#mining_bl_slave_0: DEFINE_TRACE=+define+TRACE_WB_SLAVE_0
#mining_bl_slave_0: NAME=bl_slave_0
#mining_bl_slave_0: clean compile_s run_s assertion_mining
#
#mining_bl_slave_1: DEFINE_TRACE=+define+TRACE_WB_SLAVE_1
#mining_bl_slave_1: NAME=bl_slave_1
#mining_bl_slave_1: clean compile_s run_s assertion_mining

mining_camellia: DEFINE_TRACE=+define+CAMELLIA
mining_camellia: NAME=camellia
mining_camellia: clean compile_s run_s assertion_mining


ABV: clean compile_ABV run_ABV

faultC_bl_master: FAULTS_LIST=../faults/bl_master_faults.txt
faultC_bl_master: clean compile_ABV copy_fl check_faults

faultC_bl_slave: FAULTS_LIST=../faults/bl_slave_faults.txt
faultC_bl_slave: clean compile_ABV copy_fl check_faults

faultC_camellia: FAULTS_LIST=../faults/camellia_faults.txt
faultC_camellia: clean compile_ABV copy_fl check_faults

faultC_transmitter: FAULTS_LIST=../faults/transmitter_faults.txt
faultC_transmitter: clean compile_ABV copy_fl check_faults

.PHONY: help clean copy_fl
