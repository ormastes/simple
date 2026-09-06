#include <stdio.h>

#include "cosmos_hal.h"

static unsigned int bridge_read_count;

int cosmos_fsbl_bridge_is_qemu(void) {
    return 1;
}

unsigned int cosmos_fsbl_bridge_read32(unsigned int address) {
    (void)address;
    bridge_read_count++;
    return 0U;
}

int main(void) {
    if (cosmos_fsbl_validate_handoff() != COSMOS_UNAVAILABLE) {
        fputs("QEMU FSBL handoff did not report unavailable\n", stderr);
        return 1;
    }
    if (bridge_read_count != 0U) {
        fputs("QEMU FSBL handoff performed an MMIO bridge read\n", stderr);
        return 1;
    }
    if (cosmos_fsbl_selftest() != COSMOS_OK) {
        fputs("pure-Simple FSBL self-test failed in QEMU composition\n", stderr);
        return 1;
    }
    puts("cosmos pure-Simple FSBL QEMU no-MMIO contract: PASS");
    return 0;
}
