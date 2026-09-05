/* Probe: does rt_value_as_int DECODE a text value, or shift its pointer?
 *
 * rt_value_as_int backs the `ANY -> int` cast arm on the compiled lanes. It was
 * an unconditional
 *
 *     return value >> 3;
 *
 * which is correct for a tagged int (TAG_INT == 0x0, so a boxed int is v << 3)
 * and PURE GARBAGE for a TAG_HEAP value: a heap string's pointer >> 3 is a raw
 * allocation address, different on every run. Every `s.char_at(i) as i64` site
 * on a compiled lane took this path, because `char_at` has no static return
 * type and its result falls through to ANY.
 *
 * The Rust seed twin was fixed in 22c983762d0 (decode single-codepoint text to
 * that codepoint, fall back to the lenient parse otherwise). This is the same
 * fix for the C runtime that the SELF-HOSTED binary actually links.
 *
 * P0 is the live positive control: a tagged int must still round-trip. If P0
 *    fails, this oracle is dead and every other verdict here is meaningless.
 * P1 is the RED: single-ASCII-codepoint text must decode to its code point.
 * P2 is the RED that names the bug: "Cafe\u00e9".char_at(3)-shaped text (the
 *    2-byte codepoint U+00E9) must yield 233, not a pointer.
 * P3 is the numeric-text control: multi-char digit text uses the same lenient
 *    parse the STRING-typed cast arm already uses.
 * P4 is the ANTI-REGRESSION control for the two pure-Simple call sites that
 *    pass a RAW, UNTAGGED i64 into this function and depend on the bare shift
 *    (70.backend/backend/_MirToLlvm/core_codegen.spl:700 and :1011). The guard
 *    must be the REGISTRY-VALIDATED rt_core_as_string(), not a bare
 *    `(v & TAG_MASK) == TAG_HEAP` test -- with TAG_HEAP == 0x1, every ODD raw
 *    value would test as "heap" and be silently rerouted.
 * P5 guards nil/special values (must not be treated as text).
 *
 * Build + run (same line the sibling selfchecks document; the runtime dir holds
 * mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/value_as_int_probe \
 *     src/runtime/test/rt_value_as_int_text_decode_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern int64_t rt_value_int(int64_t value);
extern int64_t rt_value_as_int(int64_t value);
extern int64_t rt_value_nil(void);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

static int failures = 0;

static void check(const char* name, int64_t got, int64_t want) {
    if (got == want) {
        printf("  PASS %-52s got=%lld\n", name, (long long)got);
    } else {
        printf("  FAIL %-52s got=%lld want=%lld\n", name, (long long)got, (long long)want);
        failures++;
    }
}

int main(void) {
    printf("rt_value_as_int text-decode selfcheck\n");

    /* P0: positive control -- tagged ints must be unaffected. */
    printf("P0 tagged int round-trip (positive control)\n");
    check("rt_value_as_int(rt_value_int(0))", rt_value_as_int(rt_value_int(0)), 0);
    check("rt_value_as_int(rt_value_int(42))", rt_value_as_int(rt_value_int(42)), 42);
    check("rt_value_as_int(rt_value_int(-1))", rt_value_as_int(rt_value_int(-1)), -1);
    check("rt_value_as_int(rt_value_int(123456789))",
          rt_value_as_int(rt_value_int(123456789)), 123456789);

    /* P1: single ASCII codepoint decodes to its code point. */
    printf("P1 single-ASCII-codepoint text decodes to its code point (RED)\n");
    check("rt_value_as_int(\"h\")",
          rt_value_as_int(rt_string_new((const uint8_t*)"h", 1)), 104);
    check("rt_value_as_int(\"A\")",
          rt_value_as_int(rt_string_new((const uint8_t*)"A", 1)), 65);

    /* P2: the bug's own oracle. U+00E9 is 2 bytes (0xC3 0xA9); this is what
     *     `"Cafe\u00e9".char_at(3)` hands to the cast. */
    printf("P2 single MULTI-BYTE codepoint decodes to 233, not a pointer (RED)\n");
    check("rt_value_as_int(\"\\u00e9\")",
          rt_value_as_int(rt_string_new((const uint8_t*)"\xc3\xa9", 2)), 233);

    /* P3: multi-character text keeps the existing lenient-parse shape, so
     *     `int(text)` is unchanged. */
    printf("P3 multi-char numeric text uses the lenient parse (unchanged shape)\n");
    check("rt_value_as_int(\"42\")",
          rt_value_as_int(rt_string_new((const uint8_t*)"42", 2)), 42);
    check("rt_value_as_int(\"-7\")",
          rt_value_as_int(rt_string_new((const uint8_t*)"-7", 2)), -7);

    /* P4: RAW untagged i64 must still take the bare shift. These are the two
     *     pure-Simple call sites' operand shapes. An odd raw value is the
     *     dangerous one: TAG_HEAP == 0x1. */
    printf("P4 raw untagged i64 still takes the bare shift (anti-regression)\n");
    check("rt_value_as_int(4097) [odd, would test as TAG_HEAP]",
          rt_value_as_int(4097), 4097 >> 3);
    check("rt_value_as_int(0x7FFFFFFF) [odd]",
          rt_value_as_int(0x7FFFFFFF), 0x7FFFFFFF >> 3);
    check("rt_value_as_int(1) [odd, below the 4096 floor]",
          rt_value_as_int(1), 0);
    check("rt_value_as_int(0x12345678) [even]",
          rt_value_as_int(0x12345678), 0x12345678 >> 3);

    /* P5: nil / special must not be mistaken for text. */
    printf("P5 nil is not text (control)\n");
    check("rt_value_as_int(rt_value_nil())",
          rt_value_as_int(rt_value_nil()), rt_value_nil() >> 3);

    if (failures == 0) {
        printf("VERDICT: PASS - all probes green\n");
        return 0;
    }
    printf("VERDICT: FAIL - %d probe(s) red\n", failures);
    return 1;
}
