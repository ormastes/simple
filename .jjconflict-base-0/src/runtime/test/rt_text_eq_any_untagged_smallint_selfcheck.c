/* REPRODUCER for bug native_text_eq_any_untagged_smallint_deref_2026-07-23.
 *
 * Symptom: a native binary SIGSEGV'd at fault address exactly `value << 3`
 * when text equality received a boxed small int where text was expected.
 *
 *   val v = json_array_get([41], 0)   # raw array, NOT a ("array", ...) tuple
 *
 * `json_get_type` did `value.0` on what is really a raw array, yielding the
 * boxed integer 41 = 0x148, then compared it `== "array"`. MIR lowered that to
 * rt_text_eq_any(0x148, "array"). 0x148 has clear low tag bits, so the old
 * body handed it to strcmp as a raw `char*` and dereferenced address 0x148.
 *
 * The interpreter returns false gracefully for the same input, so this was a
 * silent interp/native divergence that turned into a hard crash only in the
 * native lane -- and std.common.json takes `any` everywhere, so every one of
 * its comparisons is a candidate.
 *
 * Fix under test: rt_interp_cstr (runtime_native.c:2656) rejects any signed
 * value below 0x10000 as a non-pointer and returns NULL; rt_text_eq_any
 * (runtime_native.c:3503) then answers NOT-EQUAL via its `!a || !b` guard
 * instead of dereferencing.
 *
 * A FAIL here is a wrong answer; a SIGSEGV here is the original defect. Both
 * are non-zero exits, and the harness prints which probe was in flight.
 *
 * Build + run (same line the sibling selfchecks document; the runtime dir
 * holds mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/text_eq_any_smallint \
 *     src/runtime/test/rt_text_eq_any_untagged_smallint_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time|counterpart') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdint.h>

extern int64_t rt_text_eq_any(int64_t left, int64_t right);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

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
    int64_t array_lit = rt_string_new((const uint8_t*)"array", 5);
    int64_t array_lit2 = rt_string_new((const uint8_t*)"array", 5);

    /* P0/P1 positive controls: the fix must not break real text equality. */
    check("P0 equal-content strings still compare equal",
          rt_text_eq_any(array_lit, array_lit2), 1);
    check("P1 unequal-content strings still compare unequal",
          rt_text_eq_any(array_lit, rt_string_new((const uint8_t*)"object", 6)), 0);

    /* P2 THE RED: the exact value from the bug report, 41 << 3 == 0x148.
     * Pre-fix this dereferenced address 0x148 and SIGSEGV'd. */
    printf("probe P2: rt_text_eq_any(0x148, \"array\")\n");
    fflush(stdout);
    check("P2 boxed 41 (0x148) vs \"array\" is not-equal, no deref",
          rt_text_eq_any((int64_t)0x148, array_lit), 0);

    /* P3 operand order flipped -- the guard must cover BOTH sides, not just
     * the left one. */
    printf("probe P3: rt_text_eq_any(\"array\", 0x148)\n");
    fflush(stdout);
    check("P3 \"array\" vs boxed 41 (operands flipped)",
          rt_text_eq_any(array_lit, (int64_t)0x148), 0);

    /* P4 both operands garbage small ints: must answer, not crash. */
    printf("probe P4: rt_text_eq_any(0x148, 0x148)\n");
    fflush(stdout);
    check("P4 two identical boxed small ints are not text-equal",
          rt_text_eq_any((int64_t)0x148, (int64_t)0x148), 0);

    if (fails == 0) {
        printf("RT_TEXT_EQ_ANY_UNTAGGED_SMALLINT_SELFCHECK: PASS\n");
        printf("VERDICT: ALL 5 PROBES PASS\n");
        return 0;
    }
    printf("RT_TEXT_EQ_ANY_UNTAGGED_SMALLINT_SELFCHECK: FAIL\n");
    printf("VERDICT: %d PROBE(S) FAIL\n", fails);
    return 1;
}
