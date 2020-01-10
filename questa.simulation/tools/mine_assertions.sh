#!/bin/bash

WORKDIR=./work

NAME=$1
CONF_MINER=../mining/a-team/tests/$NAME/"mining_"$NAME".xml"
mv $NAME".vcd" ../mining/a-team/tests/$NAME/$NAME".vcd"
TRACE_VCD=../mining/a-team/tests/$NAME/$NAME".vcd"


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

./../mining/a-team/bin/a-team $CONF_MINER $TRACE_VCD
