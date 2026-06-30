/*
 * C consumer test for SFFI round-trip verification.
 * Compiles against the generated calculator.h header and links
 * with the shared library produced from calculator.spl.
 */
#include <stdio.h>
#include <assert.h>
#include "calculator.h"

int main(void) {
    spl_library_init();

    /* Test standalone exported functions */
    assert(calculator_square(5) == 25);
    assert(calculator_square(0) == 0);
    assert(calculator_square(-3) == 9);
    assert(calculator_add(3, 4) == 7);
    assert(calculator_add(-1, 1) == 0);

    /* Test class lifecycle: create */
    spl_Calculator_t* calc = spl_Calculator_create();
    assert(calc != NULL);

    /* Test method calls */
    spl_Calculator_add(calc, 10);
    assert(spl_Calculator_get_accumulator(calc) == 10);

    spl_Calculator_multiply(calc, 3);
    assert(spl_Calculator_get_accumulator(calc) == 30);

    spl_Calculator_add(calc, -30);
    assert(spl_Calculator_get_accumulator(calc) == 0);

    /* Test class lifecycle: destroy */
    spl_Calculator_destroy(calc);

    spl_library_shutdown();
    printf("PASS: all C round-trip tests passed\n");
    return 0;
}
