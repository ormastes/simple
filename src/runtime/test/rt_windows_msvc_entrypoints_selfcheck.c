/* Behavioural self-check for the rt_* entry points a Windows/MSVC bootstrap
 * depends on. It exists because ~929 rt_* symbols are DEFINED in
 * runtime_native.c and almost none of them had ever been EXECUTED on Windows:
 * that file only started compiling there in 2026-08 -- 6d43be015eb for MinGW
 * gcc, e463dd5035e for clang-cl/MSVC. Linking is not evidence of behaviour.
 *
 * Every check below asserts a real VALUE. There are deliberately NO
 * "it did not crash" checks: on a surface this untested a non-crash is nearly
 * worthless, because the failure mode that motivated this whole lane
 * (rt_unwrap_or_trap, a NULL GOT slot) is precisely a call that links, runs,
 * and answers nonsense. Where an assertion is necessarily weak -- a clock band
 * spanning decades, an elapsed-time window wide enough to survive a loaded
 * machine -- the line says so.
 *
 * The MSVC-specific targets are the POSIX shims runtime_native.c must supply
 * because the UCRT does not: clock_gettime (CLOCK_REALTIME + CLOCK_MONOTONIC),
 * ftruncate (-> _chsize_s) and popen/pclose (-> _popen/_pclose). They are not
 * called directly here: they are static/#define-local to that translation
 * unit, so they are exercised through the rt_* entry points that wrap them --
 *   clock_gettime(CLOCK_REALTIME)  -> rt_time_now_unix_micros / rt_time_ms
 *   clock_gettime(CLOCK_MONOTONIC) -> rt_time_now_ns / rt_time_now_nanos
 *   ftruncate                      -> rt_file_truncate
 *   popen/pclose                   -> rt_shell_exec
 * which is also how the compiler reaches them, so it is the contract that
 * actually matters.
 *
 * Portable: the body is toolchain-neutral C11 and runs on Linux/macOS too,
 * where it measures the native implementations of the same entry points. The
 * only #if defined(_WIN32) branches are the path separator, the temp dir and
 * <process.h> vs <unistd.h> for getpid.
 *
 * Build + run (POSIX):
 *   cc -std=gnu11 -O1 -o /tmp/rtwin \
 *      src/runtime/test/rt_windows_msvc_entrypoints_selfcheck.c \
 *      src/runtime/runtime_native.c -lm -lpthread && /tmp/rtwin
 * Build + run (Windows, from a vcvars x64 environment):
 *   clang-cl /nologo /Isrc\runtime /Isrc\runtime\platform \
 *      src\runtime\test\rt_windows_msvc_entrypoints_selfcheck.c \
 *      src\runtime\runtime_native.c /link /out:rtwin.exe
 *
 * MEASURED 2026-08-30, clang-cl 18.1.8 + MSVC 14.44.35207 + Windows SDK
 * 10.0.26100, Windows 11 x64: SELFCHECK PASSED (50 checks, 0 failures).
 * Every entry point named above behaves correctly on Windows.
 *
 * Four MSVC build blockers had to be worked around to get there. None of them
 * is a behaviour defect and none was patched in src/ -- they are recorded here
 * because they are what stops the core-C archive from building under clang-cl:
 *   1. runtime_native.c at 8ca87866c61 has no MSVC shims at all and fatals on
 *      `#include <unistd.h>` (line 32). The shims (clock_gettime/ftruncate/
 *      popen) live only in e463dd5035e on work/windows-bootstrap-phase-pushes;
 *      that blob is what these 50 checks exercised.
 *   2. runtime_simd_dispatch.h:78-83 tests `__GNUC__ || __clang__` BEFORE
 *      `_MSC_VER`. clang-cl defines both, takes the GNU branch and includes
 *      <cpuid.h>, whose 5-arg `__cpuid` macro then eats the
 *      `void __cpuid(int[4], int);` declaration <intrin.h> makes at
 *      runtime_native.c:11602 -- "too few arguments provided to function-like
 *      macro invocation".
 *   3. runtime_legacy_core.c:746 -- `rt_legacy_stop_group(pid_t worker, ...)`
 *      has a `#if !defined(_WIN32)` BODY but an unguarded SIGNATURE, so the
 *      POSIX `pid_t` leaks into the MSVC build. MinGW has pid_t; MSVC has not.
 *   4. runtime_simd_utf8.c:125 -- clang-cl does not expose AVX2 intrinsics from
 *      <immintrin.h> at the default /arch, and `__attribute__((target("avx2")))`
 *      does not lift that in -fms-compatibility mode, so `__m256i` is
 *      undeclared. Reproduced on a 7-line standalone probe, so it is a
 *      toolchain-mode property, not something about this file.
 * Two MSVC-only LINK problems were also observed and stepped over with
 * /FORCE:MULTIPLE plus explicit libs: `spl_thread_cpu_count` is defined in BOTH
 * runtime_thread.o and runtime_legacy_core.o (LNK2005), and runtime_simd_dispatch.o
 * needs `__cpu_model`/`__cpu_indicator_init` from clang_rt.builtins.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

#if defined(_WIN32)
#  include <process.h>
#  define RT_SC_SEP '\\'
#  define RT_SC_GETPID() ((long)_getpid())
#else
#  include <unistd.h>
#  define RT_SC_SEP '/'
#  define RT_SC_GETPID() ((long)getpid())
#endif

typedef struct SplArray SplArray;

/* Bool-returning entries are declared `unsigned char`, matching the 1-byte
 * C `bool` return the runtime actually uses. Declaring them `int` would read
 * the undefined upper bits of the return register. */

/* --- time ------------------------------------------------------------- */
extern int64_t rt_time_now_unix(void);
extern int64_t rt_time_now_unix_micros(void);
extern int64_t rt_time_ms(void);
extern int64_t rt_time_now_ns(void);
extern int64_t rt_time_now_nanos(void);
extern void    rt_sleep_ms(int64_t ms);

/* --- files ------------------------------------------------------------ */
extern int     rt_file_truncate(const char* path, uint64_t size);
extern int64_t rt_file_size(const uint8_t* path_ptr, uint64_t path_len);
extern int     rt_file_write_bytes(const uint8_t* path_ptr, uint64_t path_len,
                                   const uint8_t* data, uint64_t len);
extern int     rt_file_exists(const uint8_t* path_ptr, uint64_t path_len);
extern int     rt_file_delete(const char* path);

/* --- directories ------------------------------------------------------ */
extern unsigned char rt_dir_create_cpath(const char* path, unsigned char recursive);
extern int           rt_dir_exists(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t       rt_dir_list(const uint8_t* path_ptr, uint64_t path_len);
extern unsigned char rt_dir_remove(const uint8_t* path_ptr, uint64_t path_len,
                                   unsigned char recursive);

/* --- shell / env ------------------------------------------------------ */
extern int64_t rt_shell_exec(int64_t cmd_value);
extern int64_t rt_env_get(const uint8_t* key_ptr, uint64_t key_len);

/* --- strings / arrays / heap ------------------------------------------ */
extern int64_t        rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t        rt_string_len(int64_t value);
extern const uint8_t* rt_string_data(int64_t value);
extern int64_t        rt_string_concat(int64_t left, int64_t right);
extern int64_t        rt_string_eq(int64_t left, int64_t right);
extern int64_t        rt_string_free(int64_t value);
extern int64_t        rt_heap_registry_count(void);
extern SplArray*      rt_array_new(int64_t cap);
extern signed char    rt_array_push(SplArray* a, int64_t val);
extern int64_t        rt_array_get(SplArray* a, int64_t idx);
extern int64_t        rt_array_len_safe(int64_t value);
extern int64_t        rt_array_pop(SplArray* a);

static int failures = 0;
static int checks = 0;

static void check(int cond, const char* what) {
    checks++;
    if (cond) { printf("  ok   %s\n", what); }
    else      { printf("  FAIL %s\n", what); failures++; }
}

/* Prints the offending value on failure -- a bare FAIL on a numeric contract
 * is not a measurement, it is a rumour. Callers pass a value they already
 * captured, so a failing check never re-invokes the entry point. */
static void check_i(int cond, const char* what, int64_t observed) {
    checks++;
    if (cond) { printf("  ok   %s\n", what); }
    else      { printf("  FAIL %s (observed %" PRId64 ")\n", what, observed); failures++; }
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}
static int64_t fsize(const char* p) {
    return rt_file_size((const uint8_t*)p, (uint64_t)strlen(p));
}
static int dir_exists(const char* p) {
    return rt_dir_exists((const uint8_t*)p, (uint64_t)strlen(p));
}
static int text_contains(int64_t value, const char* needle) {
    int64_t n = rt_string_len(value);
    const uint8_t* d = rt_string_data(value);
    size_t nl = strlen(needle);
    if (!d || n < 0 || (size_t)n < nl) return 0;
    for (size_t i = 0; i + nl <= (size_t)n; i++)
        if (memcmp(d + i, needle, nl) == 0) return 1;
    return 0;
}

int main(void) {
    char base[512], sub[640], f1[768], f2[768], f3[768];
    const char* tmp;
    int64_t v;

#if defined(_WIN32)
    tmp = getenv("TEMP");
    if (!tmp || !*tmp) tmp = ".";
#else
    tmp = "/tmp";
#endif
    snprintf(base, sizeof base, "%s%crt_win_selfcheck_%ld", tmp, RT_SC_SEP, RT_SC_GETPID());
    snprintf(sub, sizeof sub, "%s%cnested%cdeep", base, RT_SC_SEP, RT_SC_SEP);
    snprintf(f1, sizeof f1, "%s%calpha.bin", sub, RT_SC_SEP);
    snprintf(f2, sizeof f2, "%s%cbeta.bin", sub, RT_SC_SEP);
    snprintf(f3, sizeof f3, "%s%cgamma.bin", sub, RT_SC_SEP);
    printf("fixture root: %s\n", base);

    /* ============ 1. CLOCK_REALTIME via rt_time_now_unix_micros ========= */
    int64_t us = rt_time_now_unix_micros();
    /* The band is deliberately wide (2023..2100). It only proves the value is
     * a Unix-epoch MICROSECOND count and not a boot-relative or 1601-epoch
     * one: the FILETIME epoch is 11644473600s before 1970, so an unconverted
     * FILETIME in 100ns ticks lands ~1.3e17 -- far above this band. */
    check_i(us > INT64_C(1700000000000000) && us < INT64_C(4100000000000000),
            "rt_time_now_unix_micros is a plausible Unix-epoch microsecond value", us);
    int64_t secs = rt_time_now_unix();
    int64_t drift = secs - (us / 1000000);
    check_i(drift >= -2 && drift <= 2,
            "rt_time_now_unix agrees with rt_time_now_unix_micros within 2s", drift);
    int64_t msnow = rt_time_ms();
    int64_t msdrift = msnow - (us / 1000);
    check_i(msdrift >= -2000 && msdrift <= 2000,
            "rt_time_ms agrees with rt_time_now_unix_micros within 2s", msdrift);

    /* ============ 2. CLOCK_MONOTONIC via rt_time_now_ns ================= */
    int64_t prev = rt_time_now_ns();
    check_i(prev > 0, "rt_time_now_ns returns a positive value (not the -1 error path)", prev);
    int regressions = 0;
    int64_t worst = 0;
    for (int i = 0; i < 200000; i++) {
        int64_t now = rt_time_now_ns();
        if (now < prev) { regressions++; if (prev - now > worst) worst = prev - now; }
        prev = now;
    }
    check_i(regressions == 0, "rt_time_now_ns is non-decreasing over 200000 samples",
            regressions);
    if (regressions) printf("       worst backward step: %" PRId64 " ns\n", worst);

    int64_t t0 = rt_time_now_ns();
    rt_sleep_ms(50);
    int64_t t1 = rt_time_now_ns();
    int64_t elapsed_ms = (t1 - t0) / 1000000;
    /* Upper bound is generous on purpose: this repo's boxes run 30+ concurrent
     * jobs, and a scheduling stall is not a runtime defect. */
    check_i(elapsed_ms >= 40 && elapsed_ms <= 5000,
            "rt_time_now_ns advances 40..5000ms across rt_sleep_ms(50)", elapsed_ms);
    v = rt_time_now_nanos();
    check_i(v >= t1, "rt_time_now_nanos shares the rt_time_now_ns timebase", v - t1);

    /* A CLOCK_REALTIME nanosecond value exceeds 1.7e18; QueryPerformanceCounter
     * and CLOCK_MONOTONIC are boot-relative and cannot plausibly reach that. */
    check_i(t1 < INT64_C(1000000000000000000),
            "rt_time_now_ns is a monotonic timebase, not wall clock", t1);

    /* ============ 3. directories ======================================== */
    check(rt_dir_create_cpath(sub, 1) != 0, "rt_dir_create_cpath creates a nested path");
    v = dir_exists(sub);
    check_i(v == 1, "rt_dir_exists reports 1 for the created directory", v);
    check(rt_dir_create_cpath(sub, 1) != 0, "rt_dir_create_cpath on an existing path succeeds");
    v = dir_exists(base);
    check_i(v == 1, "rt_dir_exists reports 1 for the intermediate parent", v);
    v = dir_exists(f1);
    check_i(v == 0, "rt_dir_exists reports 0 for a path that is not a directory", v);

    /* ============ 4. ftruncate via rt_file_truncate ===================== */
    static const uint8_t payload[5] = { 'h', 'e', 'l', 'l', 'o' };
    check(rt_file_write_bytes((const uint8_t*)f1, (uint64_t)strlen(f1), payload, 5) != 0,
          "rt_file_write_bytes writes a 5-byte file");
    v = fsize(f1);
    check_i(v == 5, "rt_file_size reports 5 after the write", v);

    v = rt_file_truncate(f1, 100000);
    check_i(v == 1, "rt_file_truncate extends to 100000 and returns 1", v);
    v = fsize(f1);
    check_i(v == 100000, "rt_file_size reports 100000 after extend", v);
    {
        FILE* fp = fopen(f1, "rb");
        int prefix_ok = 0, zero_ok = 0;
        if (fp) {
            uint8_t head[5] = {0};
            prefix_ok = fread(head, 1, 5, fp) == 5 && memcmp(head, payload, 5) == 0;
            uint8_t tail[64];
            memset(tail, 0xAB, sizeof tail);
            if (fseek(fp, 99900, SEEK_SET) == 0 &&
                fread(tail, 1, sizeof tail, fp) == sizeof tail) {
                zero_ok = 1;
                for (size_t i = 0; i < sizeof tail; i++)
                    if (tail[i] != 0) { zero_ok = 0; break; }
            }
            fclose(fp);
        }
        check(prefix_ok, "extend preserves the original 5-byte prefix");
        check(zero_ok, "extend zero-fills the new region");
    }
    v = rt_file_truncate(f1, 3);
    check_i(v == 1, "rt_file_truncate shrinks to 3 and returns 1", v);
    v = fsize(f1);
    check_i(v == 3, "rt_file_size reports 3 after shrink", v);
    v = rt_file_truncate(f1, 0);
    check_i(v == 1, "rt_file_truncate to 0 returns 1", v);
    v = fsize(f1);
    check_i(v == 0, "rt_file_size reports 0 after truncate-to-zero", v);

    /* rt_file_truncate opens with O_CREAT, so a missing path is created. */
    v = rt_file_truncate(f2, 777);
    check_i(v == 1, "rt_file_truncate creates a missing file", v);
    v = fsize(f2);
    check_i(v == 777, "the created-by-truncate file is exactly 777 bytes", v);

    /* A path that cannot be opened for writing must report failure rather than
     * silent success. */
    v = rt_file_truncate(sub, 16);
    check_i(v == 0, "rt_file_truncate on a DIRECTORY reports failure", v);

    /* ============ 5. directory listing ================================== */
    check(rt_file_write_bytes((const uint8_t*)f3, (uint64_t)strlen(f3), payload, 5) != 0,
          "third fixture file written");
    int64_t listing = rt_dir_list((const uint8_t*)sub, (uint64_t)strlen(sub));
    int64_t n = rt_array_len_safe(listing);
    check_i(n == 3, "rt_dir_list returns exactly 3 entries", n);
    int saw_a = 0, saw_b = 0, saw_g = 0, saw_dot = 0;
    for (int64_t i = 0; i < n; i++) {
        int64_t e = rt_array_get((SplArray*)(uintptr_t)listing, i);
        if (text_contains(e, "alpha.bin")) saw_a = 1;
        if (text_contains(e, "beta.bin"))  saw_b = 1;
        if (text_contains(e, "gamma.bin")) saw_g = 1;
        if (rt_string_len(e) <= 2 && text_contains(e, ".")) saw_dot = 1;
    }
    check(saw_a && saw_b && saw_g, "rt_dir_list names all three files");
    check(!saw_dot, "rt_dir_list excludes . and ..");
    v = rt_array_len_safe(rt_dir_list((const uint8_t*)"no_such_dir_xyzzy", 17));
    check_i(v == 0, "rt_dir_list on a missing directory returns an EMPTY array (not nil)", v);

    /* ============ 6. shell / popen ====================================== */
    int64_t out = rt_shell_exec(mkstr("echo SPLTOKEN9137"));
    check(text_contains(out, "SPLTOKEN9137"),
          "rt_shell_exec (popen/_popen) returns the command's stdout");
    v = rt_string_len(out);
    check_i(v >= 13 && v <= 64,
            "rt_shell_exec output is the echoed token plus a line ending", v);

    /* ============ 7. env =============================================== */
    v = rt_string_len(rt_env_get((const uint8_t*)"PATH", 4));
    check_i(v > 0, "rt_env_get(PATH) returns a non-empty value", v);

    /* ============ 8. strings / arrays / heap ============================ */
    int64_t before = rt_heap_registry_count();
    int64_t s1 = mkstr("windows entry point behaviour check part one");
    int64_t s2 = mkstr(" and part two");
    v = rt_heap_registry_count() - before;
    check_i(v == 2, "two new strings register (+2)", v);
    int64_t cat = rt_string_concat(s1, s2);
    v = rt_string_len(cat);
    check_i(v == rt_string_len(s1) + rt_string_len(s2),
            "rt_string_concat length is the sum of its operands", v);
    check(text_contains(cat, "part one and part two"), "rt_string_concat content is correct");
    v = rt_string_eq(cat, rt_string_concat(s1, s2));
    check_i(v == 1, "rt_string_eq is 1 for equal content", v);
    v = rt_string_eq(s1, s2);
    check_i(v == 0, "rt_string_eq is 0 for different content", v);
    v = rt_string_free(s1);
    check_i(v == 1, "rt_string_free reclaims a heap string", v);
    v = rt_string_free(s1);
    check_i(v == 0, "a second rt_string_free of the same string is refused", v);

    SplArray* arr = rt_array_new(0);
    for (int64_t i = 0; i < 1000; i++) rt_array_push(arr, i * 7);
    v = rt_array_len_safe((int64_t)(uintptr_t)arr);
    check_i(v == 1000, "rt_array_push grew the array to 1000", v);
    int values_ok = 1;
    int64_t bad_index = -1;
    for (int64_t i = 0; i < 1000; i++)
        if (rt_array_get(arr, i) != i * 7) { values_ok = 0; bad_index = i; break; }
    check_i(values_ok, "every pushed element reads back with its exact value", bad_index);
    v = rt_array_get(arr, -1);
    check_i(v == 999 * 7, "a negative index reads from the end", v);
    v = rt_array_pop(arr);
    check_i(v == 999 * 7, "rt_array_pop returns the last element", v);
    v = rt_array_len_safe((int64_t)(uintptr_t)arr);
    check_i(v == 999, "rt_array_pop shrank the array by exactly one", v);

    /* ============ 9. delete / remove contracts + cleanup ================ */
    v = rt_dir_remove((const uint8_t*)sub, (uint64_t)strlen(sub), 0);
    check_i(v == 0, "non-recursive rt_dir_remove REFUSES a non-empty directory", v);
    check(rt_file_delete(f1) != 0, "rt_file_delete removes a file");
    v = rt_file_exists((const uint8_t*)f1, (uint64_t)strlen(f1));
    check_i(v == 0, "rt_file_exists reports 0 for the deleted file", v);
    rt_file_delete(f2);
    rt_file_delete(f3);
    check(rt_dir_remove((const uint8_t*)sub, (uint64_t)strlen(sub), 0) != 0,
          "non-recursive rt_dir_remove succeeds once the directory is empty");
    rt_dir_remove((const uint8_t*)base, (uint64_t)strlen(base), 1);

    printf("%s (%d check%s, %d failure%s)\n",
           failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           checks, checks == 1 ? "" : "s",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
