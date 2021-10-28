#include <stdlib.h>
#include <stdio.h>

#include "driver/camellia.h"
#include "driver/transmitter.h"

#define LOOPS 1000000

uint key []    = {0x11234567, 0x89ABCDEF, 0xEDCBA987, 0x76543210};
uint data []   = {0x40404040, 0x30303030, 0x20202020, 0x10101010};
uint result [] = {         1,          2,          3,          4};

int run_testbench() {

	//printf("Enabling Camellia...\n");
	enableCamellia();

	uint fail = 0;
	for (int i = 0; i < LOOPS && fail == 0; i++) {

		// Printing the key for Camelia
		//printf("Loading key:\t%x%x%x%x\n", key[0], key[1], key[2], key[3]);
		// Loading the key for Camellia
		loadKey(key);
		// Printing the data for Cammllia
		//printf("Coding data:\t%x%x%x%x\n", data[0], data[1], data[2], data[3]);
		// Coding data
		encDec(data, result, ENC);
		// Printing the result
		//printf("Result:\t\t%x%x%x%x\n", result[0], result[1], result[2], result[3]);
		// Sending each byte to the transmitter
		for (int j = 0; j < 4; j++)
			transmitInt(result[j]);
		// Checking the result:
		// text_1 -> (enc -> dec) -> text_2. text_1 must be equal to text_2
		//printf("Checking:....   ");
		encDec(result, result, DEC);

		for (int j = 0; j < 4; j++) fail = fail || (result[j] != data[j]);
		//printf("%s\n\n", ((fail)? "Fail!" : "Ok"));

		if (!fail) {

			uint tk = key[0];
			uint td = data[3];

			for (int j = 0; j < 3; j++) {
				key[j] = key[j+1];
				data[4 - j - 1] = data[4 -j - 2];
			}

			key  [3] = tk;
			data [0] = td;
		}
	}

	return 0;
}
