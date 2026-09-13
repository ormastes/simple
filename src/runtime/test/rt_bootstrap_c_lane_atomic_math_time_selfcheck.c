/* Stage2 bootstrap link (core-C-only lane): behavioural proof for the 32
 * `rt_*` symbols added to runtime_native.c/runtime_time.c to close the
 * undefined-symbol set found when relinking the real Stage2 failed-link
 * object set (native-objects-8HIZif, run22, 2026-09-07) with
 * `-Wl,--error-limit=0` instead of the linker's default 20-error cutoff --
 * see doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md.
 *
 * Covers: rt_time_monotonic_ns; the eleven rt_math_* libm passthroughs
 * (asin/acos/atan/atan2/sinh/cosh/tanh/floor/ceil/log/log10/log2); the full
 * rt_atomic_int_ and rt_atomic_bool_ family (store, swap, fetch ops, free,
 * plus the whole bool side, including the new fetch_and/fetch_or/fetch_not);
 * and rt_simple_abi_version / rt_simple_abi_version_deferred.
 *
 * Build (links against the standalone-compiled runtime_native.o, i.e. the
 * exact TU the core-C bootstrap archive is made from -- same recipe as
 * rt_runtime_kind_probes_core_c_selfcheck.c beside this file). Only
 * runtime_native.o is linked, not runtime_time.o: both define
 * rt_time_now_nanos/rt_time_monotonic_ns/etc as parallel implementations of
 * the same contract for different lanes (core-C-bootstrap vs. Rust-hosted),
 * and the real archives never combine them either.
 *   cc -c -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -DSIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 -Wl,--gc-sections \
 *      src/runtime/test/rt_bootstrap_c_lane_atomic_math_time_selfcheck.c \
 *      rn.o -lpthread -lm -ldl -o selfcheck && ./selfcheck
 */
#if defined(_WIN32)
/* The UCRT only declares M_PI and friends when _USE_MATH_DEFINES is defined
 * before <math.h>. Without it this TU does not even parse on Windows, which
 * left the push-blocking C-runtime gate RED on every Windows host. */
#define _USE_MATH_DEFINES
#endif

#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <time.h>

#if defined(_WIN32)
#define WIN32_LEAN_AND_MEAN
#define NOMINMAX
#include <windows.h>
#endif

extern int64_t rt_time_monotonic_ns(void);
extern int64_t rt_simple_abi_version(void);
extern int64_t rt_simple_abi_version_deferred(void);

extern double rt_math_asin(double x);
extern double rt_math_acos(double x);
extern double rt_math_atan(double x);
extern double rt_math_atan2(double y, double x);
extern double rt_math_sinh(double x);
extern double rt_math_cosh(double x);
extern double rt_math_tanh(double x);
extern double rt_math_floor(double x);
extern double rt_math_ceil(double x);
extern double rt_math_log(double x);
extern double rt_math_log10(double x);
extern double rt_math_log2(double x);

extern int64_t rt_atomic_int_new(int64_t initial);
extern int64_t rt_atomic_int_load(int64_t handle);
extern void rt_atomic_int_store(int64_t handle, int64_t value);
extern int64_t rt_atomic_int_swap(int64_t handle, int64_t value);
extern bool rt_atomic_int_compare_exchange(int64_t handle, int64_t current, int64_t new_value);
extern int64_t rt_atomic_int_fetch_add(int64_t handle, int64_t value);
extern int64_t rt_atomic_int_fetch_sub(int64_t handle, int64_t value);
extern int64_t rt_atomic_int_fetch_and(int64_t handle, int64_t value);
extern int64_t rt_atomic_int_fetch_or(int64_t handle, int64_t value);
extern int64_t rt_atomic_int_fetch_xor(int64_t handle, int64_t value);
extern void rt_atomic_int_free(int64_t handle);

extern int64_t rt_atomic_bool_new(bool initial);
extern bool rt_atomic_bool_load(int64_t handle);
extern void rt_atomic_bool_store(int64_t handle, bool value);
extern bool rt_atomic_bool_swap(int64_t handle, bool value);
extern bool rt_atomic_bool_compare_exchange(int64_t handle, bool current, bool new_value);
extern bool rt_atomic_bool_fetch_and(int64_t handle, bool value);
extern bool rt_atomic_bool_fetch_or(int64_t handle, bool value);
extern bool rt_atomic_bool_fetch_not(int64_t handle);
extern void rt_atomic_bool_free(int64_t handle);

static int failures = 0;

#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL: %s\n", msg); failures++; } \
} while (0)

#define CHECK_CLOSE(actual, expected, msg) \
    CHECK(fabs((actual) - (expected)) < 1e-9, msg)

static void check_time(void) {
    int64_t a = rt_time_monotonic_ns();
#if defined(_WIN32)
    /* Windows has no nanosleep; Sleep() takes milliseconds. Same oracle: a
     * real 20ms sleep must make the monotonic clock strictly advance. */
    Sleep(20);
#else
    struct timespec ts = {0, 20 * 1000 * 1000}; /* 20ms */
    nanosleep(&ts, NULL);
#endif
    int64_t b = rt_time_monotonic_ns();
    CHECK(a >= 0, "rt_time_monotonic_ns first reading must be non-negative");
    CHECK(b > a, "rt_time_monotonic_ns must strictly increase across a real sleep");
}

static void check_math(void) {
    CHECK_CLOSE(rt_math_asin(1.0), M_PI / 2.0, "rt_math_asin(1) == pi/2");
    CHECK_CLOSE(rt_math_acos(1.0), 0.0, "rt_math_acos(1) == 0");
    CHECK_CLOSE(rt_math_atan(1.0), M_PI / 4.0, "rt_math_atan(1) == pi/4");
    CHECK_CLOSE(rt_math_atan2(1.0, 1.0), M_PI / 4.0, "rt_math_atan2(1,1) == pi/4");
    CHECK_CLOSE(rt_math_sinh(0.0), 0.0, "rt_math_sinh(0) == 0");
    CHECK_CLOSE(rt_math_cosh(0.0), 1.0, "rt_math_cosh(0) == 1");
    CHECK_CLOSE(rt_math_tanh(0.0), 0.0, "rt_math_tanh(0) == 0");
    CHECK_CLOSE(rt_math_floor(1.7), 1.0, "rt_math_floor(1.7) == 1");
    CHECK_CLOSE(rt_math_ceil(1.2), 2.0, "rt_math_ceil(1.2) == 2");
    CHECK_CLOSE(rt_math_log(1.0), 0.0, "rt_math_log(1) == 0");
    CHECK_CLOSE(rt_math_log10(100.0), 2.0, "rt_math_log10(100) == 2");
    CHECK_CLOSE(rt_math_log2(8.0), 3.0, "rt_math_log2(8) == 3");
}

static void check_atomic_int(void) {
    int64_t h = rt_atomic_int_new(10);
    CHECK(h != 0, "rt_atomic_int_new must return a non-null handle");
    CHECK(rt_atomic_int_load(h) == 10, "rt_atomic_int_load reads back initial value");
    rt_atomic_int_store(h, 20);
    CHECK(rt_atomic_int_load(h) == 20, "rt_atomic_int_store then load == 20");
    CHECK(rt_atomic_int_swap(h, 30) == 20, "rt_atomic_int_swap returns previous value");
    CHECK(rt_atomic_int_load(h) == 30, "rt_atomic_int_swap installs new value");
    CHECK(rt_atomic_int_fetch_add(h, 5) == 30, "rt_atomic_int_fetch_add returns pre-add value");
    CHECK(rt_atomic_int_load(h) == 35, "rt_atomic_int_fetch_add applied +5");
    CHECK(rt_atomic_int_fetch_sub(h, 5) == 35, "rt_atomic_int_fetch_sub returns pre-sub value");
    CHECK(rt_atomic_int_load(h) == 30, "rt_atomic_int_fetch_sub applied -5");
    CHECK(rt_atomic_int_fetch_and(h, 0x0F) == 30, "rt_atomic_int_fetch_and returns pre-op value");
    CHECK(rt_atomic_int_load(h) == (30 & 0x0F), "rt_atomic_int_fetch_and applied mask");
    rt_atomic_int_store(h, 0x10);
    CHECK(rt_atomic_int_fetch_or(h, 0x01) == 0x10, "rt_atomic_int_fetch_or returns pre-op value");
    CHECK(rt_atomic_int_load(h) == 0x11, "rt_atomic_int_fetch_or applied bit");
    CHECK(rt_atomic_int_fetch_xor(h, 0x11) == 0x11, "rt_atomic_int_fetch_xor returns pre-op value");
    CHECK(rt_atomic_int_load(h) == 0, "rt_atomic_int_fetch_xor self-XOR zeroes");
    int64_t current = 0;
    CHECK(rt_atomic_int_compare_exchange(h, current, 99), "rt_atomic_int_compare_exchange succeeds on match");
    CHECK(rt_atomic_int_load(h) == 99, "compare_exchange installed new value");
    CHECK(!rt_atomic_int_compare_exchange(h, 0, 1), "compare_exchange fails on stale expected");
    rt_atomic_int_free(h);
}

static void check_atomic_bool(void) {
    int64_t h = rt_atomic_bool_new(false);
    CHECK(h != 0, "rt_atomic_bool_new must return a non-null handle");
    CHECK(rt_atomic_bool_load(h) == false, "rt_atomic_bool_load reads back initial false");
    rt_atomic_bool_store(h, true);
    CHECK(rt_atomic_bool_load(h) == true, "rt_atomic_bool_store then load == true");
    CHECK(rt_atomic_bool_swap(h, false) == true, "rt_atomic_bool_swap returns previous value");
    CHECK(rt_atomic_bool_load(h) == false, "rt_atomic_bool_swap installs new value");
    CHECK(rt_atomic_bool_compare_exchange(h, false, true), "compare_exchange succeeds on match");
    CHECK(rt_atomic_bool_load(h) == true, "compare_exchange installed true");
    CHECK(!rt_atomic_bool_compare_exchange(h, false, true), "compare_exchange fails on stale expected");
    CHECK(rt_atomic_bool_fetch_and(h, false) == true, "fetch_and returns pre-op value");
    CHECK(rt_atomic_bool_load(h) == false, "fetch_and(true, false) == false");
    CHECK(rt_atomic_bool_fetch_or(h, true) == false, "fetch_or returns pre-op value");
    CHECK(rt_atomic_bool_load(h) == true, "fetch_or(false, true) == true");
    CHECK(rt_atomic_bool_fetch_not(h) == true, "fetch_not returns pre-op value");
    CHECK(rt_atomic_bool_load(h) == false, "fetch_not(true) == false");
    CHECK(rt_atomic_bool_fetch_not(h) == false, "fetch_not returns pre-op value (2nd)");
    CHECK(rt_atomic_bool_load(h) == true, "fetch_not(false) == true");
    rt_atomic_bool_free(h);
}

static void check_abi_version(void) {
    /* Deferred (0) selects a positive version and vice versa -- runtime.h's
     * own #error guards (SIMPLE_ABI_VERSION_DEFERRED == (SIMPLE_ABI_VERSION
     * == 0)) already enforce this at compile time; this just proves both
     * accessors read the same macro pair consistently at runtime. */
    int64_t version = rt_simple_abi_version();
    int64_t deferred = rt_simple_abi_version_deferred();
    CHECK((deferred == 1) == (version == 0), "abi version and its deferred flag agree");
}

int main(void) {
    check_time();
    check_math();
    check_abi_version();
    check_atomic_int();
    check_atomic_bool();
    if (failures == 0) {
        printf("PASS: bootstrap core-C lane atomic/math/time additions behave correctly\n");
        return 0;
    }
    fprintf(stderr, "FAIL: %d assertion(s) failed\n", failures);
    return 1;
}
