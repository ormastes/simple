// Mailbox test for RV32I GHDL simulation
// Uses MMIO mailbox registers instead of semihosting traps

#include "mailbox.h"

int main(void) {
    mb_puts("Hello mailbox\n");
    mb_result(1, 42);  /* pass=1, value=42 */
    mb_exit(0);
    return 0; /* unreachable */
}
