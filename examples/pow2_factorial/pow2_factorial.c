#include <stdint.h>

unsigned long pow2(unsigned exponent) {
	unsigned long a = 1;

	for (unsigned i = 0; i < exponent; ++i) {
		a += a;
	}

	return a;
}

uint64_t factorial(uint8_t n) {
	if (n) {
		return n * factorial(n - 1);
	} else {
		return 1;
	}
}

int main(int argc, char* argv[]) {
	int x = factorial(argc);
	int y = pow2(x);
	return x * y;
}
