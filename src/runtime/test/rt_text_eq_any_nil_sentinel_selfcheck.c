/* Probe: does rt_text_eq_any recognize the flat-Option nil sentinel (RT_NIL == 3)?
 *
 * rt_text_eq_any backs native `==`/`!=` whenever either operand is
 * string-shaped (MIR lowering's bin_is_str_eq intercept in
 * 50.mir/_MirLoweringExpr/expr_dispatch.spl). A `Dict<_, text>.get(k)` MISS
 * yields the flat-Option nil sentinel 3 (preserved around the decode by
 * dict_get_preserve_flat_nil since 2026-08-05), and `x == nil` on that
 * str-typed result lowers to rt_text_eq_any(x, 3).
 *
 * The unfixed body ran rt_interp_cstr on both operands first; the sentinel 3
 * is not a registered string and is < 0x10000, so it decodes to NULL and the
 * `if (!a || !b) return 0;` guard answered NOT-EQUAL unconditionally --
 * `text_miss == nil` was false and `text_miss != nil` was true, making a
 * dict miss indistinguishable from a hit for text-valued dicts (bug
 * native_dict_get_miss_returns_zero_not_nil_2026-07-28, residual text row).
 *
 * P0 positive control: two equal-content tagged strings compare equal.
 * P1 positive control: unequal-content strings compare unequal.
 * P2 THE RED: nil sentinel vs nil sentinel must be EQUAL (x == nil on a miss).
 * P3 nil sentinel vs a real string must be UNEQUAL (x == nil on a hit).
 * P4 real string vs nil sentinel (operand order flipped) must be UNEQUAL.
 *
 * Build + run (same line the sibling selfchecks document; the runtime dir holds
 * mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/text_eq_any_nil_probe \
 *     src/runtime/test/rt_text_eq_any_nil_sentinel_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

extern int64_t rt_text_eq_any(int64_t left, int64_t right);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

#define RT_NIL_SENTINEL 3

static int fails = 0;
static void check(const char* name, int64_t got, int64_t want) {
    if (got == want) {
        printf("PASS %s (got %lld)\n", name, (long long)got);
    } else {
        printf("FAIL %s (got %lld, want %lld)\n", name, (long long)got, (long long)want);
        fails++;
    }
}

int main(void) {
    int64_t hello_a = rt_string_new((const uint8_t*)"hello", 5);
    int64_t hello_b = rt_string_new((const uint8_t*)"hello", 5);
    int64_t world = rt_string_new((const uint8_t*)"world", 5);

    check("P0 equal-content strings", rt_text_eq_any(hello_a, hello_b), 1);
    check("P1 unequal-content strings", rt_text_eq_any(hello_a, world), 0);
    check("P2 nil == nil (dict-miss text vs NilLit)", rt_text_eq_any(RT_NIL_SENTINEL, RT_NIL_SENTINEL), 1);
    check("P3 nil vs real string", rt_text_eq_any(RT_NIL_SENTINEL, hello_a), 0);
    check("P4 real string vs nil", rt_text_eq_any(hello_a, RT_NIL_SENTINEL), 0);

    if (fails == 0) {
        printf("VERDICT: ALL %d PROBES PASS\n", 5);
        return 0;
    }
    printf("VERDICT: %d PROBE(S) FAIL\n", fails);
    return 1;
}
