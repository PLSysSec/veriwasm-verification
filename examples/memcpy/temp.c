#include <stdio.h>
#include <string.h>

void swap (void* a0, void* a1) {
	const char temp[9];
	memcpy((void*) temp, a0, 9);
	memcpy(a0, a1, 9);
	memcpy(a1, temp, 9);
}

int main () {
   return(0);
}
