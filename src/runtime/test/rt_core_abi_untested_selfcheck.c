/* Selfcheck for five CORE-REQUIRED ABI symbols that had ZERO tests anywhere.
 *
 * Provenance: doc/08_tracking/test/rt_test_coverage_audit_2026-08-31.md.
 * All five appear in the core-required contract array in
 * src/compiler_rust/common/src/runtime_symbols.rs (the 88 symbols every
 * bootstrap stage must resolve), and none was reached by any C selfcheck, any
 * Rust #[cfg(test)] body, any interpreter_extern test, or any Simple spec:
 *
 *   rt_str_hash  rt_len  rt_string_trim  rt_string_to_int  rt_string_to_int_lenient
 *
 * THE REDS this file pins (both found BY writing it, not known beforehand):
 *
 *  R1 rt_str_hash's FNV-1a-64 offset basis differs between the two duplicate
 *     definitions of the symbol, so its value depends on WHICH TU the link
 *     picked -- a hash written by one lane cannot be read back by the other:
 *       src/runtime/runtime.c:541              14695981039346656037  (correct
 *                                              FNV-1a-64 basis, 0xcbf29ce484222325)
 *       src/runtime/runtime_legacy_core.c:243   1469598103934665603  (the same
 *                                              digits with the trailing '7'
 *                                              DROPPED -- 19 digits, not 20)
 *     Both files are listed together in
 *     scripts/check/runtime_bundle_duplicate_symbols_baseline.txt (row
 *     rt_str_hash <TAB> runtime.c,runtime_legacy_core.c), and the core-C
 *     bootstrap capsule (scripts/check/build-core-c-bootstrap-runtime-capsule.shs)
 *     compiles runtime_legacy_core.c and NOT runtime.c -- so the BOOTSTRAP lane
 *     is the one running the truncated constant.
 *
 *  R2 rt_string_to_int truncates its input at 63 bytes (char buf[64], n clamped
 *     to sizeof(buf)-1, runtime_native.c:5391), so a 64-byte numeric string
 *     silently parses only its first 63 bytes. No diagnostic, no saturation --
 *     just a wrong number.
 *
 * I4 additionally RECORDS (does not fix) the intentional C-vs-Rust split on
 * rt_string_to_int("42abc"): C is lenient (strtoll -> 42), the Rust crate is
 * strict (str::parse -> 0). See collections.rs:4227's own comment.
 *
 * Build + run: see section 6 of
 * doc/08_tracking/test/rt_test_coverage_audit_2026-08-31.md.
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t value);
extern const char* rt_string_data(int64_t value);
extern int64_t rt_str_hash(const char* s);
extern int64_t rt_len(int64_t value);
extern int64_t rt_string_trim(int64_t value);
extern int64_t rt_string_to_int(int64_t value);
extern int64_t rt_string_to_int_lenient(int64_t value);
extern int64_t rt_value_int(int64_t v);

static int fails = 0;
static int checks = 0;

static void eq_i(const char* name, int64_t got, int64_t want) {
    checks++;
    if (got == want) {
        printf("PASS %s (got %lld)\n", name, (long long)got);
    } else {
        printf("FAIL %s (got %lld, want %lld)\n", name, (long long)got, (long long)want);
        fails++;
    }
}

static void ne_i(const char* name, int64_t a, int64_t b) {
    checks++;
    if (a != b) {
        printf("PASS %s (%lld != %lld)\n", name, (long long)a, (long long)b);
    } else {
        printf("FAIL %s (both %lld, expected different)\n", name, (long long)a);
        fails++;
    }
}

static void eq_s(const char* name, int64_t got, const char* want) {
    checks++;
    int64_t n = rt_string_len(got);
    const char* d = rt_string_data(got);
    size_t wn = strlen(want);
    if (d && n >= 0 && (size_t)n == wn && memcmp(d, want, wn) == 0) {
        printf("PASS %s (got len=%lld)\n", name, (long long)n);
    } else {
        printf("FAIL %s (got len=%lld [%.*s], want len=%zu [%s])\n",
               name, (long long)n, (int)(n < 0 ? 0 : n), d ? d : "", wn, want);
        fails++;
    }
}

/* Independent oracle: a second FNV-1a-64 implementation written here, so the
 * hash assertions do not merely re-run the implementation under test. */
static uint64_t fnv1a64_ref(const char* s) {
    uint64_t h = 14695981039346656037ULL;   /* 0xcbf29ce484222325 */
    while (*s) {
        h ^= (uint64_t)(unsigned char)*s++;
        h *= 1099511628211ULL;
    }
    return h;
}

static int64_t str(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

int main(void) {
    /* ---- rt_str_hash ------------------------------------------------- */

    /* H0 THE RED (R1): empty string must hash to the FNV-1a-64 offset basis.
     * Discriminating: fails for a 0/constant/length stub AND for the
     * digit-dropped legacy basis, which is the whole point. */
    eq_i("H0 rt_str_hash(empty) == FNV-1a-64 offset basis",
         rt_str_hash(""), (int64_t)14695981039346656037ULL);

    /* H1 full-string agreement with the independent oracle above.
     * Discriminating: only a genuine FNV-1a-64 over the whole input passes. */
    eq_i("H1 rt_str_hash(simple) == reference FNV-1a-64",
         rt_str_hash("simple"), (int64_t)fnv1a64_ref("simple"));

    /* H2 order sensitivity. Discriminating against any commutative
     * (sum/xor-of-bytes) stub. */
    ne_i("H2 rt_str_hash order-sensitive (ab vs ba)",
         rt_str_hash("ab"), rt_str_hash("ba"));

    /* H3 length is not the hash. Discriminating against a strlen stub. */
    ne_i("H3 rt_str_hash(abc) is not strlen", rt_str_hash("abc"), 3);

    /* ---- rt_len ------------------------------------------------------ */

    /* L0..L2 three different lengths: discriminating against any constant
     * stub and against a stub returning 0 or -1. */
    eq_i("L0 rt_len(hello) == 5", rt_len(str("hello")), 5);
    eq_i("L1 rt_len(empty) == 0", rt_len(str("")), 0);
    eq_i("L2 rt_len(abcdefghij) == 10", rt_len(str("abcdefghij")), 10);

    /* L3 byte length, not codepoint count: \xc3\xa9 is one U+00E9, two bytes.
     * Discriminating between a byte-length and a UTF-8-aware implementation. */
    eq_i("L3 rt_len(2-byte UTF-8 codepoint) == 2 (bytes, not codepoints)",
         rt_len(str("\xc3\xa9")), 2);

    /* L4 a non-string, non-array value answers 0 rather than trapping.
     * NOT strongly discriminating -- a stub returning 0 also passes. Recorded
     * as a contract pin, not as a defect detector. */
    eq_i("L4 rt_len(non-container) == 0 [weak: a 0-stub also passes]",
         rt_len(rt_value_int(7)), 0);

    /* ---- rt_string_trim ---------------------------------------------- */

    eq_s("T0 trim(  hi  )", rt_string_trim(str("  hi  ")), "hi");

    /* T1 interior whitespace preserved. Discriminating against a
     * strip-all-whitespace stub, which T0 alone would not catch. */
    eq_s("T1 trim( a b ) keeps the interior space",
         rt_string_trim(str(" a b ")), "a b");

    eq_s("T2 trim(hi) is a no-op", rt_string_trim(str("hi")), "hi");
    eq_s("T3 trim(spaces) == empty", rt_string_trim(str("   ")), "");
    eq_s("T4 trim strips tab/CR/LF too", rt_string_trim(str("\t\r\n x \n")), "x");
    eq_s("T5 trim does not collapse an interior tab",
         rt_string_trim(str("\n a\tb \r")), "a\tb");

    /* ---- rt_string_to_int / rt_string_to_int_lenient ------------------ */

    eq_i("I0 to_int(42) == 42", rt_string_to_int(str("42")), 42);

    /* I1 negative: discriminating against an unsigned/abs stub. */
    eq_i("I1 to_int(-17) == -17", rt_string_to_int(str("-17")), -17);

    eq_i("I2 to_int( 42 ) == 42", rt_string_to_int(str(" 42 ")), 42);
    eq_i("I3 to_int(abc) == 0", rt_string_to_int(str("abc")), 0);

    /* I4 RECORDS the intentional C-vs-Rust split: C is lenient here.
     * Discriminating for the C lane; it deliberately encodes the divergence
     * rather than asserting one cross-lane answer. */
    eq_i("I4 to_int(42abc) == 42 [C lenient; Rust crate is strict -> 0]",
         rt_string_to_int(str("42abc")), 42);

    /* I5 THE RED (R2): 64 bytes = 62 '0' then "42". The value is 42 and fits
     * i64; the C body copies only 63 bytes, so it parses 62 zeros + '4' -> 4.
     * Maximally discriminating: no plausible stub returns 4 here. */
    {
        char big[65];
        memset(big, '0', 62);
        big[62] = '4';
        big[63] = '2';
        big[64] = '\0';
        eq_i("I5 to_int(64-byte 0...042) == 42 [63-byte truncation RED]",
             rt_string_to_int(str(big)), 42);
    }

    /* I6 the C runtime aliases _lenient to to_int; pin that they agree on
     * every case above so a future divergence in ONE of them is caught. */
    {
        const char* cases[] = { "42", "-17", " 42 ", "abc", "42abc", "4.2", "" };
        int i;
        int agree = 1;
        for (i = 0; i < 7; i++) {
            int64_t a = rt_string_to_int(str(cases[i]));
            int64_t b = rt_string_to_int_lenient(str(cases[i]));
            if (a != b) {
                printf("   .. disagree on [%s]: to_int=%lld lenient=%lld\n",
                       cases[i], (long long)a, (long long)b);
                agree = 0;
            }
        }
        eq_i("I6 C to_int and to_int_lenient agree on 7 cases", agree, 1);
    }

    /* I7 lenient must take the leading numeric prefix. Discriminating. */
    eq_i("I7 lenient(4.2) == 4", rt_string_to_int_lenient(str("4.2")), 4);

    printf("%s: %d check(s), %d failure(s)\n",
           fails ? "FAIL" : "PASS", checks, fails);
    return fails ? 1 : 0;
}
