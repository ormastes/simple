/* Probe: does a Dict keyed by f64 keep the key EXACT?
 *
 * The runtime deliberately boxes floats on the heap (RtCoreFloat) so that "the
 * full double is stored verbatim so container/Any floats round-trip exactly"
 * (runtime_native.c, RtCoreFloat comment). rt_core_dict_canon_key then squeezed
 * that boxed double back into the LEGACY INLINE tagged form
 *
 *     (bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT
 *
 * to get a pointer-independent key. `& ~7` ZEROES THE LOW 3 MANTISSA BITS, so
 * every group of 8 adjacent doubles collapses to ONE dict key: d[a] = 1 then
 * d[b] = 2 silently overwrites, len() stays 1, and d[a] reads back 2.
 *
 * P0 is the live positive control (two doubles 1 ulp * 8 apart -- must be two
 *    distinct keys under ANY implementation).  If P0 fails, this oracle is dead.
 * P1 is the RED: two doubles 1 ulp apart.
 * P2 is the RED for key round-trip: dict_keys() must hand back the SAME double.
 * P3 guards the documented -0.0 -> +0.0 fold (must stay ONE key).
 * P4 guards NaN keys (bitwise-identical NaN must stay findable).
 * P5 guards ordinary int/text keys (regression control for the shared path).
 *
 * Build + run (same line the sibling selfchecks document; the runtime dir holds
 * mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/dict_float_probe \
 *     src/runtime/test/rt_dict_float_key_exactness_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

extern int64_t rt_value_float(double value_f64);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t  rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int64_t rt_dict_len(int64_t dict);
extern int64_t rt_dict_keys(int64_t dict);
extern int64_t rt_array_len_safe(int64_t value);
extern int64_t rt_array_get(void* a, int64_t idx);
extern int64_t rt_native_eq(int64_t left, int64_t right);

static int failures = 0;

/* Box a double, going through the ordinary rt_value_float entry point so this
 * probe exercises the SAME representation compiled Simple code produces. */
static int64_t mkf(double d) {
    return rt_value_float(d);
}

/* Tagged small int (RT_VALUE_TAG_INT == 0), so values are self-describing and
 * can be compared verbatim against what rt_dict_get hands back. */
static int64_t mki(int64_t v) { return v << 3; }

/* POSITIVE CAPABILITY PROBE for binary identity: if the boxed float does not
 * even round-trip through rt_native_eq, we are not linked against the real
 * runtime and every verdict below would be vacuous. */
static void capability_probe(void) {
    int64_t a = mkf(1.0000000000000002);
    int64_t b = mkf(1.0000000000000002);
    if (a == b) {
        printf("CAPABILITY FAIL: two boxes returned the same handle\n");
        failures++;
    }
    if (!rt_native_eq(a, b)) {
        printf("CAPABILITY FAIL: rt_native_eq cannot compare boxed floats "
               "-- probe is NOT linked against the real runtime\n");
        failures++;
    } else {
        printf("CAPABILITY OK: boxed floats are distinct handles, value-equal\n");
    }
}

static void two_key_case(const char* name, double x, double y, int expect_len) {
    int64_t d = rt_dict_new(8);
    int64_t kx = mkf(x), ky = mkf(y);
    rt_dict_set(d, kx, mki(100));
    rt_dict_set(d, ky, mki(200));
    int64_t len = rt_dict_len(d);
    int64_t gx = rt_dict_get(d, kx);
    int64_t gy = rt_dict_get(d, ky);
    int ok = (len == expect_len);
    if (expect_len == 2) ok = ok && gx == mki(100) && gy == mki(200);
    else ok = ok && gx == mki(200) && gy == mki(200);
    printf("%-8s x=%.17g y=%.17g  len=%lld d[x]=%lld d[y]=%lld  (expect len=%d) %s\n",
           name, x, y, (long long)len,
           (long long)(gx >> 3), (long long)(gy >> 3), expect_len,
           ok ? "OK" : "FAIL");
    if (!ok) failures++;
}

static void key_roundtrip(void) {
    double v = 1.0000000000000002; /* nextafter(1.0, 2.0) */
    int64_t d = rt_dict_new(8);
    int64_t k = mkf(v);
    rt_dict_set(d, k, mki(7));
    int64_t keys = rt_dict_keys(d);
    int64_t n = rt_array_len_safe(keys);
    int64_t back = n == 1 ? rt_array_get((void*)(uintptr_t)keys, 0) : 0;
    int ok = (n == 1) && back != 0 && rt_native_eq(back, k) != 0;
    printf("P2 KEYRT keys_len=%lld  stored_key_equals_original=%s  (expect yes) %s\n",
           (long long)n, (n == 1 && back && rt_native_eq(back, k)) ? "yes" : "no",
           ok ? "OK" : "FAIL");
    if (!ok) failures++;
}

static void nan_key(void) {
    int64_t d = rt_dict_new(8);
    int64_t k1 = mkf(NAN);
    int64_t k2 = mkf(NAN); /* a SECOND box of the same bit pattern */
    rt_dict_set(d, k1, mki(42));
    int64_t g1 = rt_dict_get(d, k1);
    int64_t g2 = rt_dict_get(d, k2);
    int ok = (g1 == mki(42)) && (g2 == mki(42)) && rt_dict_len(d) == 1;
    printf("P4 NAN    d[nan]=%lld via-second-box=%lld len=%lld (expect 42/42/1) %s\n",
           (long long)(g1 >> 3), (long long)(g2 >> 3),
           (long long)rt_dict_len(d), ok ? "OK" : "FAIL");
    if (!ok) failures++;
}

static void plain_keys(void) {
    int64_t d = rt_dict_new(8);
    const char* a = "alpha";
    const char* b = "beta";
    int64_t ka = rt_string_new((const uint8_t*)a, strlen(a));
    int64_t ka2 = rt_string_new((const uint8_t*)a, strlen(a)); /* distinct box */
    int64_t kb = rt_string_new((const uint8_t*)b, strlen(b));
    rt_dict_set(d, ka, mki(1));
    rt_dict_set(d, kb, mki(2));
    rt_dict_set(d, mki(11), mki(3));
    rt_dict_set(d, mki(12), mki(4));
    int ok = rt_dict_len(d) == 4 &&
             rt_dict_get(d, ka2) == mki(1) &&
             rt_dict_get(d, kb) == mki(2) &&
             rt_dict_get(d, mki(11)) == mki(3) &&
             rt_dict_get(d, mki(12)) == mki(4);
    printf("P5 PLAIN  text+int keys len=%lld (expect 4) all-lookups-correct=%s %s\n",
           (long long)rt_dict_len(d), ok ? "yes" : "no", ok ? "OK" : "FAIL");
    if (!ok) failures++;
}

int main(void) {
    capability_probe();
    /* P0 control: 8 ulp apart, so the low 3 mantissa bits are NOT what
     * distinguishes them -- must be two keys even with the truncating canon. */
    two_key_case("P0 CTRL", 1.0, 1.0000000000000018, 2);
    /* P1 RED: 1 ulp apart -- distinguished ONLY by the truncated bits. */
    two_key_case("P1 RED ", 1.0, 1.0000000000000002, 2);
    key_roundtrip();
    /* P3: IEEE says -0.0 == 0.0 and the runtime documents folding them. */
    two_key_case("P3 ZERO", 0.0, -0.0, 1);
    nan_key();
    plain_keys();
    printf("\nfailures=%d\n", failures);
    return failures == 0 ? 0 : 1;
}
