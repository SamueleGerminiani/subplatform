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

#ifndef __WB_OPERATIONS__
#define __WB_OPERATIONS__

#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wpointer-to-int-cast"

#include <stdlib.h>
#include "vc_hdrs.h"

// MAX_ERRORS defines how many times either a read or write transaction can fail
// before aborting the current operation.
#define MAX_ERRORS 2

#define BYTE_1 0x1
#define BYTE_2 0x2
#define BYTE_3 0x4
#define BYTE_4 0x8

#define M_PTR_I(address) ((int *)(address))
#define M_PTR_S(address) ((short *)(address))
#define M_PTR_C(address) ((char *)(address))

//##############################################################################
// Generic read and write methods for Wishbone transactions
//##############################################################################

// Description: wb_write performs a wishbone write transaction
// Inputs:
//  address: a 4 bytes address
//  data:    a 4 bytes data value
//  byteSel: a 4 bits value selecting which byte of the data is valid
//           (1 -> valid, 0 -> not valid)
//           byteSel[0] -> data[7:0]; ...; byteSel[3] -> data[31:24]
// Output: 1 on error, 0 otherwise
char wb_write(int *address, uint data, uint byteSel) {
    char err = 0;
    int error_counter = 0;
    do {
        write_transaction((int)address, data, byteSel, &err);
        error_counter++;
    } while (err == 1 && error_counter < MAX_ERRORS);
    return err;
}

// Description: wb_read performs a wishbone read transaction
// Inputs:
//  address: a 4 bytes address
//  data:    a 4 bytes data value pointer
//  byteSel: a 4 bits value selecting which byte of the memory location defined
//           by address is copied in data (1 -> to be copied, 0 -> to be discard)
//           byteSel[0] -> data[7:0]; ...; byteSel[3] -> data[31:24]
// Output: 1 on error, 0 otherwise
char wb_read(int *address, uint *data, uint byteSel) {
        int error_counter = 0;
        char err = 0;
        do {
            read_transaction((int)address, byteSel, data, &err);
            error_counter++;
        } while (err == 1 && error_counter < MAX_ERRORS);
        return err;
}
//------------------------------------------------------------------------------


//##############################################################################
// Read and write methods for standard C data types
//##############################################################################

// Description: wb_writeByte writes a char in a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a char (1 byte) data value
// Output: 1 on error, 0 otherwise
char wb_writeByte(char *address, unsigned char data) {
    return wb_write((int *)address, data, 0x1);
}

// Description: wb_writeShort writes a unsigned short in a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a unsigned short (2 bytes) data value
// Output: 1 on error, 0 otherwise
char wb_writeShort(short *address, unsigned short data) {
    return wb_write((int *)address, data, 0x3);
}

// Description: wb_writeInt writes unsigned integer in a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a unsigned integer (4 bytes) data value
// Output: 1 on error, 0 otherwise
char wb_writeInt(int *address, unsigned int data) {
    return wb_write(address, data, 0xF);
}

// Description: wb_readByte reads a char from a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a char (1 byte) pointer in which the read data will be stored
// Output: 1 on error, 0 otherwise
char wb_readByte(char *address, unsigned char *data) {
    unsigned int tmp; // wb_read always reads a integer!
    char err = wb_read((int *)address, &tmp, 0x1);
    *data = (unsigned char)tmp;
    return err;
}

// Description: wb_readShort reads a unsigned short from a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a unsigned short (2 bytes) pointer in which the read data will be stored
// Output: 1 on error, 0 otherwise
char wb_readShort(short *address, unsigned short *data) {
    unsigned int tmp; // wb_read always reads a integer!
    char err = wb_read((int *)address, &tmp, 0x3);
    *data = (unsigned short)tmp;
    return err;
}

// Description: wb_readInt reads a unsigned integer from a memory location
// Inputs:
//  address: a 4 bytes address
//  data:    a unsigned integer (4 bytes) pointer in which the read data will be stored
// Output: 1 on error, 0 otherwise
char wb_readInt(int *address, unsigned int *data) {
    return wb_read(address, data, 0xF);
}
//------------------------------------------------------------------------------

#pragma GCC diagnostic pop
#endif // __WB_OPERATIONS__
