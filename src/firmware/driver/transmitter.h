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


#ifndef __WB_TRANSMITTER_DRIVER__
#define __WB_TRANSMITTER_DRIVER__

#include "buslayer_master.h"

// the base address of Transmitter mudule
#define TRANSMITTER_BASE_ADDRESS M_PTR_C(0x60)

void transmit(char data) {
    wb_writeByte(TRANSMITTER_BASE_ADDRESS, data);
}

void transmitInt(unsigned int data) {
    transmit((char)data);
    transmit((char)(data >> 8));
    transmit((char)(data >> 16));
    transmit((char)(data >> 24));
}

#endif
