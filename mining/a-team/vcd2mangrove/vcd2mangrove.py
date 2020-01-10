#! /usr/bin/env python

import os
import sys

from Verilog_VCD import *


###############################################################################
def getSignalCode(signalName, trace):
    for key, value in trace.iteritems():
        nets = value['nets']
        info = nets[0]
        name = info['name']

        if name == signalName:
            return key

    return ''


###############################################################################

###############################################################################
def getSignalNames(trace):
    names = []
    for key, value in trace.iteritems():
        nets = value['nets']
        info = nets[0]
        name = info['name']
        #name = name.lower()
        size = info['size']
        names.append((name, key, size))

    return names


###############################################################################

###############################################################################
def getValues(signalCode, trace):
    signal = trace[signalCode]
    values = signal['tv']
    return values


###############################################################################

###############################################################################
def filterValues(clockValues, signalValues):
    values = []

    lastIndexSV = 0
    for index in range(len(clockValues)):
        timeClock, valueClock = clockValues[index]
        if valueClock == '1':
            continue

        timeSignal, valueSignal = signalValues[lastIndexSV]
        while timeSignal < timeClock:
            tmp = lastIndexSV + 1
            if tmp >= len(signalValues):
                break

            tmpTimeSignal, tmpValueSignal = signalValues[tmp]
            if tmpTimeSignal > timeClock:
                break

            lastIndexSV = tmp

        timeSignal, valueSignal = signalValues[lastIndexSV]
        values.append((timeSignal, valueSignal))

    return values


###############################################################################

###############################################################################
def replaceValues(signalValues):
    for index in range(len(signalValues)):
        timeSignal, valueSignal = signalValues[index]
        valueSignal = valueSignal.replace('x', '0')
        signalValues[index] = (timeSignal, valueSignal)


###############################################################################

###############################################################################
def addMissingBits(signalValues, signalSize):
    if signalSize == '1':
        return

    for index in range(len(signalValues)):
        timeSignal, valueSignal = signalValues[index]
        valueSignal = valueSignal.zfill(int(signalSize))
        signalValues[index] = (timeSignal, valueSignal)
    pass


###############################################################################

###############################################################################
def printMangroveTrace(path, trace, splitVector,convertLogicToBool):
    var_file = open(path + "trace.variables", "w")
    for index in range(len(trace)):
        nameSignal, valueSignal = trace[index]
        time, value = valueSignal[0]
 

        if len(value) == 1 and convertLogicToBool == "Yes" :
            var_file.write(nameSignal + " bool\n")
        else:
            if not splitVector:
                var_file.write(nameSignal + " logic " + str(len(value)) + "\n")
            else:
                try:
                    chPos = nameSignal.index('[')
                    baseName = nameSignal[0:chPos]
                    for bitPos in range(len(value)):
                        var_file.write(baseName + "[" + str(len(value) - bitPos - 1) + "] bool\n")
                # var_file.write(baseName + "_" + str(len(value) - bitPos - 1) + " bool\n")
                except ValueError:
                    print "warning! The variable " + nameSignal + " is supposed to be a 32 integer!"
                    for i in range(32):
                        var_file.write(nameSignal + "[" + str(31 - i) + "] bool\n")

    var_file.write("\n")
    var_file.close()

    trace_file = open(path + "trace.mangrove", "w")
    instants = len(trace[0][1])

    if splitVector:
        signals = 0
        for indexVar in range(len(trace)):
            nameSignal, valuesSignal = trace[indexVar]
            time, value = valuesSignal[0]
            signals += len(value)

        trace_file.write(str(signals) + " " + str(instants) + "\n")
    else:
        trace_file.write(str(len(trace)) + " " + str(instants) + "\n")

    for indexVar in range(len(trace)):
        nameSignal, valuesSignal = trace[indexVar]
        time, value = valuesSignal[0]

        if len(value) == 1 or not splitVector:
            for indexValue in range(len(valuesSignal)):
                timeSignal, valueSignal = valuesSignal[indexValue]
                trace_file.write(str(valueSignal) + " ")
            trace_file.write("\n")
        else:
            for indexBit in range(len(value)):
                for indexValue in range(len(valuesSignal)):
                    timeSignal, valueSignal = valuesSignal[indexValue]
                    trace_file.write(str(valueSignal[indexBit]) + " ")
                trace_file.write("\n")
    trace_file.close()


###############################################################################

###############################################################################
def main(argv):
    if len(sys.argv) < 7:
        print "Usage:"
        print "python " + os.path.basename(sys.argv[0]) + " <vcd> <clock> <split?Yes:No> <addModulePathToVariables?Yes:No> <convertLogicToBool?Yes:No> <pathToOut>"
        return 1

    fileName = sys.argv[1]
    clockName = sys.argv[2]
    splitVector = (sys.argv[3] == "Yes")
    addModulePathToVariables=sys.argv[4]
    convertLogicToBool=sys.argv[5]
    pathToOut= "./" + sys.argv[6]

    data = parse_vcd(fileName,addModulePathToVariables,clockName)
    clockCode = getSignalCode(clockName, data)

    if clockCode == '':
        print "clock signal not found!"
        return 1

    clockValues = getValues(clockCode, data)

    signals = getSignalNames(data)
    signals.sort(key=lambda tup: tup[0])

    mangroveTrace = []
    for index in range(len(signals)):
        signalName, signalCode, signalSize = signals[index]
        if signalName == clockName:
            continue

        signalValues = getValues(signalCode, data)
        signalValues = filterValues(clockValues, signalValues)

        assert len(signalValues) == ((len(clockValues) + 1) / 2)

        replaceValues(signalValues)
        addMissingBits(signalValues, signalSize)
        mangroveTrace.append((signalName, signalValues))

    printMangroveTrace(pathToOut, mangroveTrace, splitVector, convertLogicToBool)


###############################################################################

if __name__ == '__main__':
    main(sys.argv)
