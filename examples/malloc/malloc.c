#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>


int* build_array(uint8_t n) {
	int* a = (int *) malloc (n * sizeof(int));
	if (a == NULL) {
		return 0;
	}
	else {
		uint8_t i;
		for (i = 0; i < n; i++)
			a[i] = 0;
		return a;
	}
}

int main(int argc, char* argv[]) {
	int* a = build_array(argc);
	return 0;
}


