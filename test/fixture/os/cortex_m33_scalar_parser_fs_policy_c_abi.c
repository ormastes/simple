#include <stdint.h>
#include <stdio.h>

extern uint32_t cm33_policy_streq(uint32_t, uint32_t);
extern uint32_t cm33_policy_starts_with(uint32_t, uint32_t);
extern uint32_t cm33_policy_parse_hex_prefix(uint32_t, uint32_t);
extern uint32_t cm33_policy_parse_hex_digit(uint32_t);
extern uint32_t cm33_policy_strlen_simple(uint32_t);
extern uint32_t cm33_policy_memcpy_simple(uint32_t);
extern uint32_t cm33_policy_fs_add_file(uint32_t, uint32_t, uint32_t,
                                       uint32_t, uint32_t);
extern uint32_t cm33_policy_fs_add_name(uint32_t, uint32_t, uint32_t);
extern uint32_t cm33_policy_fs_init(uint32_t);
extern uint32_t cm33_policy_fs_find(uint32_t, uint32_t, uint32_t);

static int require_u32(const char *name, uint32_t actual, uint32_t expected) {
    if (actual == expected) return 1;
    fprintf(stderr, "%s expected=%u actual=%u\n", name, expected, actual);
    return 0;
}

int main(void) {
    int ok = 1;
    ok &= require_u32("streq", cm33_policy_streq('a', 'a'), 1);
    ok &= require_u32("starts", cm33_policy_starts_with('a', 0), 2);
    ok &= require_u32("prefix", cm33_policy_parse_hex_prefix('0', 'x'), 2);
    ok &= require_u32("digit", cm33_policy_parse_hex_digit('F'), 15);
    ok &= require_u32("strlen", cm33_policy_strlen_simple('a'), 1);
    ok &= require_u32("memcpy", cm33_policy_memcpy_simple(0), 0);
    ok &= require_u32("fs-add", cm33_policy_fs_add_file(0, 0, 5, 16, 4096), 2048);
    ok &= require_u32("fs-name", cm33_policy_fs_add_name('a', 30, 32), 1);
    ok &= require_u32("fs-init", cm33_policy_fs_init(6), UINT32_MAX);
    ok &= require_u32("fs-find", cm33_policy_fs_find(1, 2, 1), 1);
    if (!ok) return 1;
    puts("cm33_scalar_parser_fs_c_abi status=PASS exports=10/10 scalar_u32=true");
    return 0;
}
