#!/bin/bash

FAULTS_LIST=faults.txt
SIM_REPORT=fault_report.txt
COVERAGE_REPORT=coverage.txt
RUN="1ms"
# ---------------------- DO NOT TOUCH BELOW THIS LINE --------------------------

UCLI=file.cmds
echo "" > $COVERAGE_REPORT
while IFS= read -r fault
do
    fault=$(echo "$fault" | tr -d '\r')
    echo "assertion fail -r / -limit 1 sim1; force $fault; run $RUN; \
          assertion report -failed -r sim1 -file $SIM_REPORT; exit" > $UCLI
    vsim -quiet -suppress vopt-13314,vsim-4075 -c sim1 -do $UCLI

    echo ===========================================================================  >> $COVERAGE_REPORT
    echo "Fault: "$fault >> $COVERAGE_REPORT
    if [ ! -s $SIM_REPORT ]; then
        echo "---------------------------------------------------------------------------"
        echo "NO ASSERTION FAILED!"  >> $COVERAGE_REPORT
    else
        cat $SIM_REPORT              >> $COVERAGE_REPORT
    fi

done < $FAULTS_LIST

rm -f $UCLI
rm -f $SIM_REPORT

cat $COVERAGE_REPORT
exit 0
