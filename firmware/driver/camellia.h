/*------------------------------------------------------------------------------
Copyright © 2018 by Alessandro Danese

This file is provided under the terms of MIT License (MIT):

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
the Software, and to permit persons to whom the Software is furnished to do so,
subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
------------------------------------------------------------------------------*/
/**
 * @author Alessandro Danese
 * Univerity of Verona, Dept. of Computer Science, Verona, Italy
 * alessandro.danese@univr.it
 */


#ifndef __WB_CAMELLIA_DRIVER__
#define __WB_CAMELLIA_DRIVER__

#include "buslayer_master.h"

// the base address of Camellia mudule
#define CAMELLIA_BASE_ADDRESS     0x0

// Control/data memory mapped registers.
// Each register is OFFSET bytes far from the base address
#define CAMELLIA_KEY        M_PTR_I(CAMELLIA_BASE_ADDRESS + 0x0)
#define CAMELLIA_DATA_I     M_PTR_I(CAMELLIA_BASE_ADDRESS + 0x10)
#define CAMELLIA_CONTROL_I  M_PTR_I(CAMELLIA_BASE_ADDRESS + 0x20)
#define CAMELLIA_DATA_O     M_PTR_I(CAMELLIA_BASE_ADDRESS + 0x24)
#define CAMELLIA_CONTROL_O  M_PTR_C(CAMELLIA_BASE_ADDRESS + 0x34)

// Control bits for Camellia
#define ENABLE   BYTE_1
#define ENCDEC   BYTE_2
#define DRDY     BYTE_3
#define KRDY     BYTE_4

#define ENC 1
#define DEC 0


char enableCamellia() {
    return wb_write(CAMELLIA_CONTROL_I, 1, ENABLE);
}

char disableCamellia() {
    return wb_write(CAMELLIA_CONTROL_I, 0, ENABLE);
}

char loadKey(uint *key) {
    unsigned char err = 0;
    uint *key_address = CAMELLIA_KEY;
    for (int i = 0; (i < 4 && err == 0); i++)
        err = wb_writeInt(key_address + i, key[i]);

    if (err == 0)
        err = wb_write(CAMELLIA_CONTROL_I, 1, KRDY);

    unsigned char bsy = 1;
    while (err == 0 && bsy == 1)
        err = wb_readByte(CAMELLIA_CONTROL_O, &bsy);

    return err;
}

char encDec(uint *dataIn, uint *dataOut, char encDec) {
    unsigned char err = 0;
    uint *data_i_address = CAMELLIA_DATA_I;
    for (int i = 0; (i < 4 && err == 0); i++)
        err = wb_writeInt(data_i_address + i, dataIn[i]);

    if (err == 0)
        err = wb_write(CAMELLIA_CONTROL_I, 1,
                       DRDY | ((encDec == 0)? ENCDEC : 0));

    unsigned char bsy = 1;
    while (err == 0 && bsy == 1)
        err = wb_readByte(CAMELLIA_CONTROL_O, &bsy);

    uint *data_o_address = CAMELLIA_DATA_O;
    for (int i = 0; (i < 4 && err == 0); i++)
        err = wb_readInt(data_o_address + i, dataOut + i);

    return err;
}

 #endif
