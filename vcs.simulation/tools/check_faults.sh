#!/bin/bash

FAULTS_LIST=faults.txt
SIM_REPORT=fault_report.txt
MAX_FAULT=1
COVERAGE_REPORT=coverage.txt
RUN="1ms"

# ---------------------- DO NOT TOUCH BELOW THIS LINE --------------------------

UCLI=file.cmds
echo "" > $COVERAGE_REPORT
while IFS= read -r fault
do
    echo -e "force "$fault"\nrun" > $UCLI
    ./simv  +vcs+finish+$RUN                  \
            -assert maxfail=$MAX_FAULT        \
            -assert report=$SIM_REPORT        \
            -assert quiet 1                   \
            -ucli -ucli2Proc -do $UCLI

    if [ ! -e $SIM_REPORT ]; then
            echo "Fault report not generated!"
            exit 1
    fi

    ASSERTS_FAILED=`grep -oP ':\s\K[a-zA-Z0-9].*(?=:)' $SIM_REPORT | sort | uniq`

    echo ===========================================================================  >> $COVERAGE_REPORT
    echo "Fault: "$fault >> $COVERAGE_REPORT
    echo "Assertions: " >> $COVERAGE_REPORT
    for item in ${ASSERTS_FAILED[*]}; do
        echo "--> "$item >> $COVERAGE_REPORT
    done
done < $FAULTS_LIST

rm -f $UCLI
rm -f $SIM_REPORT
rm -f $SIM_REPORT.disablelog

cat $COVERAGE_REPORT
exit 0
