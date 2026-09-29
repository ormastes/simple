#include <stdint.h>
#include <stdio.h>
#include "rv32_token_siphash.h"

int main(void) {
    uint8_t key[16];
    unsigned i;
    for (i = 0; i < 16; ++i) key[i] = (uint8_t)i;
    if (simpleos_token_siphash24_bytes(key, key, 0) !=
            UINT64_C(0x726fdb47dd0e0e31)) {
        return 1;
    }
    puts("PASS rv32 token SipHash-2-4 KAT");
    return 0;
}
