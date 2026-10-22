/* Split secure_temp_dir handle-ABI contract (runtime_native.c).
 * rt_secure_temp_dir_set_parent / _set_prefix take ONE boxed text
 * RuntimeValue, not (ptr, len): that is the crossing every seed vintage emits
 * (doc/08_tracking/bug/tracked_seed_cranelift_split_secure_temp_dir_refuses_20261019.md).
 * Build: clang -Isrc/runtime -c src/runtime/runtime_native.c -o rn.o &&
 *        clang this.c rn.o -o probe (Windows: -lbcrypt -ladvapi32 -lws2_32
 *        -Wl,/FORCE:UNRESOLVED); run: probe <existing-parent-dir>.
 * Prints PASS and exits 0, or names each failed contract and exits 1. */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
int64_t rt_string_new(const uint8_t*, uint64_t);
int64_t rt_string_len(int64_t);
const uint8_t* rt_string_data(int64_t);
int64_t rt_secure_temp_dir_set_parent(int64_t);
int64_t rt_secure_temp_dir_set_prefix(int64_t);
int64_t rt_secure_temp_dir_make(void);
int main(int argc, char** argv) {
    const char* parent = argc > 1 ? argv[1] : ".";
    int64_t p = rt_string_new((const uint8_t*)parent, strlen(parent));
    int64_t x = rt_string_new((const uint8_t*)"probe-", 6);
    int64_t bad = rt_string_new((const uint8_t*)"a/b", 3);
    int fails = 0;
    if (rt_secure_temp_dir_set_prefix(bad) != 0) { puts("FAIL bad prefix admitted"); fails++; }
    if (rt_secure_temp_dir_set_parent(0) != 0) { puts("FAIL nil parent admitted"); fails++; }
    if (rt_secure_temp_dir_set_parent(p) != 1) { puts("FAIL parent refused"); fails++; }
    if (rt_secure_temp_dir_set_prefix(x) != 1) { puts("FAIL prefix refused"); fails++; }
    int64_t made = rt_secure_temp_dir_make();
    int64_t n = rt_string_len(made);
    if (n <= 0) { puts("FAIL make refused"); fails++; } else printf("made %.*s\n", (int)n, (const char*)rt_string_data(made));
    if (rt_string_len(rt_secure_temp_dir_make()) > 0) { puts("FAIL make did not consume slots"); fails++; }
    puts(fails ? "FAIL" : "PASS");
    return fails;
}
