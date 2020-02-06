
/*
 * ====================================================
 * Developed at SSRG Virginia Tech by Ian Roessle iroessle@vt.edu
 * ====================================================
 */

/* int main(void)
 * Return : zero                  
 * Tests double remainder function for verification purposes.
 * This serves as test case study 1.
 */



#include "fdlibm.h"
#include <stdio.h>

int main(void)
{
    double numerator=500.0;
    double denominator=0.0;

    double remainder = __ieee754_remainder(numerator,denominator);

    printf("The remainder of %lf / %lf is: %lf\n", numerator, denominator, remainder);

    return 0;
}



