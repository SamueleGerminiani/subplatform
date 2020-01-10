#!/bin/bash

NAME=`ls *.vcd | cut -d. -f1`
CLOCK=wb_clk
WORKDIR=./work

TRACE_VCD=$NAME".vcd"
CONF_MINER=../mining/"mining_"$NAME".xml"

if [ ! -e $TRACE_VCD ]; then
    echo "File: "$TRACE_VCD" not found!"
    exit 1
fi

if [ ! -e $CONF_MINER ]; then
    echo "File: "$CONF_MINER" not found!"
    exit 1
fi

rm -rf $WORKDIR

mkdir $WORKDIR
if [ ! -e $WORKDIR ]; then
    echo "Directory: "$WORKDIR" not created!"
    exit 1
fi

command -v vcd2mangrove.py >/dev/null 2>&1 || { echo >&2 "vcd2mangrove.py is required but it's not installed. Aborting."; exit 1;}
echo "Turning the VCD trace file into a mangrove trace file."

vcd2mangrove.py $TRACE_VCD $CLOCK True

mv trace.mangrove $WORKDIR
mv trace.variables $WORKDIR

assertionMiner $CONF_MINER
