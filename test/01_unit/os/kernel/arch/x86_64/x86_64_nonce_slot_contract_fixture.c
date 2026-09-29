#include <assert.h>
#include <stdint.h>
#include <string.h>
#include "../../../../../../examples/09_embedded/simple_os/arch/x86_64/boot/x86_64_nonce_slot_contract.h"

int main(void)
{
    uint8_t slot[118] = {0};
    const char *line = "SIMPLEOS_QEMU_NONCE=x86_64-fixture-1\n";
    memcpy(slot, line, strlen(line));
    assert(x86_64_nonce_slot_line_length(slot, sizeof(slot)) == strlen(line));
    slot[strlen(line) + 3U] = 'X';
    assert(x86_64_nonce_slot_line_length(slot, sizeof(slot)) == 0);
    slot[strlen(line) + 3U] = 0;
    slot[strlen(line) - 1U] = 0;
    assert(x86_64_nonce_slot_line_length(slot, sizeof(slot)) == 0);
    memcpy(slot, "SIMPLEOS_QEMU_NONCE=\n", 22U);
    memset(slot + 22U, 0, sizeof(slot) - 22U);
    assert(x86_64_nonce_slot_line_length(slot, sizeof(slot)) == 0);
    memset(slot, 0, sizeof(slot));
    memcpy(slot, "SIMPLEOS_QEMU_NONCE=bad!\n", 26U);
    assert(x86_64_nonce_slot_line_length(slot, sizeof(slot)) == 0);
    return 0;
}
