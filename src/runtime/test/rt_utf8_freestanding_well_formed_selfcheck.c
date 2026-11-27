/* Freestanding UTF-8 well-formedness selfcheck.
 *
 * The kernel runtimes (riscv64 boot/freestanding_runtime.c, x86_64
 * up_squared/freestanding_runtime.c) gate rt_bytes_to_text on
 * spl_utf8_well_formed from runtime_utf8_well_formed.h, the same
 * freestanding-safe check the hosted runtime uses (Unicode Table 3-7).
 * This pins the reject cases: overlong, surrogate, truncated, stray
 * continuation, > U+10FFFF.
 *
 * Build: clang -std=c11 -ffreestanding -I src/runtime \
 *   src/runtime/test/rt_utf8_freestanding_well_formed_selfcheck.c -o t && ./t */
#include "runtime_utf8_well_formed.h"
#include <stdio.h>

static int failures = 0;

static void check(const char *name, const uint8_t *b, size_t n, int want) {
    int got = spl_utf8_well_formed(b, n);
    if (got != want) {
        printf("FAIL %s: got %d want %d\n", name, got, want);
        failures++;
    }
}

#define CASE(name, want, ...) do { \
    static const uint8_t buf_[] = {__VA_ARGS__}; \
    check(name, buf_, sizeof(buf_), want); } while (0)

int main(void) {
    check("empty", (const uint8_t *)"", 0, 1);
    CASE("ascii", 1, 'h', 'i');
    CASE("two-byte", 1, 0xC3, 0xA9);
    CASE("three-byte", 1, 0xE2, 0x82, 0xAC);
    CASE("four-byte", 1, 0xF0, 0x9F, 0x98, 0x80);
    CASE("max-scalar", 1, 0xF4, 0x8F, 0xBF, 0xBF);
    CASE("overlong-2", 0, 0xC0, 0xAF);
    CASE("overlong-2b", 0, 0xC1, 0xBF);
    CASE("overlong-3", 0, 0xE0, 0x80, 0xAF);
    CASE("overlong-4", 0, 0xF0, 0x80, 0x80, 0xAF);
    CASE("surrogate-hi", 0, 0xED, 0xA0, 0x80);
    CASE("surrogate-lo", 0, 0xED, 0xBF, 0xBF);
    CASE("truncated-2", 0, 'a', 0xC3);
    CASE("truncated-3", 0, 0xE2, 0x82);
    CASE("truncated-4", 0, 0xF0, 0x9F, 0x98);
    CASE("stray-cont", 0, 0x80);
    CASE("stray-cont-mid", 0, 'a', 0xBF, 'b');
    CASE("above-10ffff", 0, 0xF4, 0x90, 0x80, 0x80);
    CASE("f5-lead", 0, 0xF5, 0x80, 0x80, 0x80);
    CASE("ff", 0, 0xFF);
    if (failures) return 1;
    printf("PASS rt_utf8_freestanding_well_formed_selfcheck\n");
    return 0;
}
