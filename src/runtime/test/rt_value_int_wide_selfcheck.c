/* Probe: does an integer wider than the 61-bit tagged payload survive boxing?
 *
 * The ANY-slot integer encoding is a pure arithmetic shift (ABI contract
 * doc/04_architecture/compiler/array_value_abi_contract.md §1.1):
 *
 *     encode(v) = v << 3 ; decode(w) = w >> 3
 *
 * which leaves a 61-bit payload. There was NO range check, so any |v| >= 2^60
 * silently sign-extended back to a DIFFERENT number: 2^60 flipped sign,
 * i64::MAX read as -1, 2^62 read as 0. Bug
 * doc/08_tracking/bug/int61_bit_truncation_jit_scalars_and_native_container_boxing_2026-08-09.md
 * measured exactly that on the native lane for any value stored in a list.
 * §1.1 already names the fix: "the encoder traps or heap-boxes; silently
 * truncating is a violation."
 *
 * P0 is the positive control: in-range values MUST keep the bit-identical
 *    `v << 3` immediate, so no existing consumer changes behavior.
 * P1 is the RED that names the bug: the four measured boundary values must
 *    round-trip.
 * P2 is the boundary pair, one below and one at the cutoff.
 * P3 checks the legacy entry point rt_value_int/rt_value_as_int agrees.
 * P4 checks a heap-boxed wide int is NOT mistaken for text or nil.
 *
 * Build + run (same line the sibling selfchecks document; the runtime dir holds
 * mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/value_int_wide_probe \
 *     src/runtime/test/rt_value_int_wide_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdint.h>

extern int64_t rt_value_int(int64_t value);
extern int64_t rt_value_as_int(int64_t value);
extern int64_t rt_value_int_wide(int64_t value);
extern int64_t rt_value_as_int_wide(int64_t value);

static int failures = 0;

static void check(const char* name, int64_t got, int64_t want) {
    if (got == want) {
        printf("  PASS %-56s got=%lld\n", name, (long long)got);
    } else {
        printf("  FAIL %-56s got=%lld want=%lld\n", name, (long long)got, (long long)want);
        failures++;
    }
}

static void roundtrip(const char* name, int64_t v) {
    check(name, rt_value_as_int_wide(rt_value_int_wide(v)), v);
}

int main(void) {
    printf("rt_value_int_wide 61-bit boundary selfcheck\n");

    printf("P0 in-range values keep the identical v<<3 immediate (control)\n");
    check("rt_value_int_wide(0) == 0", rt_value_int_wide(0), 0);
    check("rt_value_int_wide(1) == 8", rt_value_int_wide(1), 8);
    check("rt_value_int_wide(-1) == -8", rt_value_int_wide(-1), -8);
    check("rt_value_int_wide(42) == 336", rt_value_int_wide(42), 336);
    roundtrip("roundtrip 42", 42);
    roundtrip("roundtrip -123456789", -123456789);

    printf("P1 measured boundary values round-trip (RED)\n");
    roundtrip("roundtrip 2^60", 1152921504606846976LL);
    roundtrip("roundtrip 2^62", 4611686018427387904LL);
    roundtrip("roundtrip i64::MAX", 9223372036854775807LL);
    roundtrip("roundtrip -(i64::MAX)", -9223372036854775807LL);

    printf("P2 the cutoff itself\n");
    roundtrip("roundtrip 2^59 (largest safe)", 576460752303423488LL);
    roundtrip("roundtrip 2^60-1 (last in-range)", 1152921504606846975LL);
    check("2^60-1 still the inline immediate",
          rt_value_int_wide(1152921504606846975LL), 1152921504606846975LL << 3);

    printf("P3 the legacy entry point agrees\n");
    check("rt_value_as_int(rt_value_int(i64::MAX))",
          rt_value_as_int(rt_value_int(9223372036854775807LL)), 9223372036854775807LL);
    check("rt_value_as_int(rt_value_int(7))", rt_value_as_int(rt_value_int(7)), 7);

    printf("P4 a RAW untagged word still takes the bare shift (anti-regression)\n");
    check("rt_value_as_int_wide(80) == 10", rt_value_as_int_wide(80), 10);

    printf(failures == 0 ? "SELFCHECK PASS\n" : "SELFCHECK FAIL (%d)\n", failures);
    return failures == 0 ? 0 : 1;
}
