#include "access_policy.h"

#include <stdint.h>
#include <stdio.h>

static int require_u32(const char *name, uint32_t actual, uint32_t expected) {
    if (actual == expected) return 1;
    fprintf(stderr, "FAIL %s actual=%u expected=%u\n", name, actual, expected);
    return 0;
}

int main(void) {
    const uint32_t flash_base = UINT32_C(0x10000000);
    const uint32_t flash_size = UINT32_C(0x00400000);
    const uint32_t ram_base = UINT32_C(0x20000000);
    const uint32_t ram_size = UINT32_C(0x00008000);
    int ok = 1;

    ok &= require_u32("read-unaligned",
                      cortex_m_policy_read_receipt(flash_base + 1u,
                                                   flash_base, flash_size,
                                                   ram_base, ram_size),
                      UINT32_C(257));
    ok &= require_u32("read-flash",
                      cortex_m_policy_read_receipt(flash_base,
                                                   flash_base, flash_size,
                                                   ram_base, ram_size),
                      UINT32_C(512));
    ok &= require_u32("read-rejected",
                      cortex_m_policy_read_receipt(UINT32_C(0x60000000),
                                                   flash_base, flash_size,
                                                   ram_base, ram_size),
                      UINT32_C(8194));
    ok &= require_u32("write-ram",
                      cortex_m_policy_write_receipt(ram_base,
                                                    ram_base, ram_size),
                      UINT32_C(32768));
    ok &= require_u32("write-peripheral",
                      cortex_m_policy_write_receipt(UINT32_C(0x40000000),
                                                    ram_base, ram_size),
                      UINT32_C(65536));
    ok &= require_u32("write-rejected",
                      cortex_m_policy_write_receipt(flash_base,
                                                    ram_base, ram_size),
                      UINT32_C(131075));
    if (!ok) return 1;
    puts("status=PASS c_abi_exports=2 scalar_u32=true cases=6");
    return 0;
}
