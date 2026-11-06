/* Self-check: the argv providers in a hosted bundle that carries BOTH
 * runtime.c and runtime_native.c return core-C arrays, in either link order.
 *
 * Defect (doc/08_tracking/bug/hosted_bundle_legacy_cli_args_wins_weak_tie_2026-11-07.md):
 * runtime.c and runtime_native.c both defined rt_cli_get_args /
 * rt_cli_arg_count / rt_cli_arg_at as WEAK on ELF. The hosted bundle
 * (70.backend/backend/runtime_compiler.spl, `var sources = ["runtime",
 * "runtime_native", ...]`) puts runtime.c first, so the linker kept runtime.c's
 * legacy copy, which builds a legacy spl_array_new() layout. That array is not
 * registered with the core-C heap, so the first rt_array_len() on it printed
 *
 *   [simple-runtime][error] rejected invalid array handle before dereference;
 *   probable compiler/FFI ABI mismatch
 *
 * and returned 0: every native CLI built on that bundle (app.t32_cli, ...)
 * saw an empty argument list at startup.
 *
 * Build + run (Linux, clang + lld; both link orders must pass, with and
 * without -DSIMPLE_CORE_C_STANDALONE=1 added to F). The MEMORY_OWNER define is
 * what every full-bundle composer passes; the runtime.c-only C-backend lane
 * does not.
 *   O=/tmp/argv; mkdir -p $O
 *   F="-w -Isrc/runtime -Isrc/runtime/platform -DSIMPLE_RUNTIME_MEMORY_OWNER=1"
 *   for f in runtime runtime_native runtime_memory runtime_alloc_observer runtime_memtrack; do
 *     clang -c $F src/runtime/$f.c -o $O/$f.o; done
 *   clang -c $F src/runtime/test/rt_cli_args_owner_order_selfcheck.c -o $O/check.o
 *   REST="$O/runtime_memory.o $O/runtime_alloc_observer.o $O/runtime_memtrack.o"
 *   # These five TUs reference a few symbols owned by other bundle members
 *   # that this check never calls; satisfy them with weak zero stubs:
 *   clang -fuse-ld=lld $O/check.o $O/runtime.o $O/runtime_native.o $REST -o $O/x \
 *     -lm -lpthread -ldl -Wl,--allow-multiple-definition -Wl,--error-limit=0 2>&1 |
 *     grep -o "undefined symbol: [A-Za-z0-9_]*" | sort -u | sed 's/undefined symbol: //' |
 *     awk '{print "__attribute__((weak)) long long " $1 "[64];"}' > $O/stubs.c
 *   clang -c -w $O/stubs.c -o $O/stubs.o
 *   # hosted order (runtime.o first), then reversed:
 *   clang -fuse-ld=lld $O/check.o $O/runtime.o $O/runtime_native.o $REST $O/stubs.o \
 *     -o $O/check -lm -lpthread -ldl -Wl,--allow-multiple-definition
 *   $O/check one two   -> "PASS — 5 argv provider checks, argc=3", exit 0
 * Before the fix the hosted order printed the rejected-handle diagnostic, three
 * "rt_array_len=0 want 3" FAILs, then SIGSEGV in rt_string_len(rt_cli_arg_at()).
 */
#include <stdint.h>
#include <stdio.h>

typedef struct SplArray SplArray;

extern void spl_init_args(int argc, char** argv);
extern int64_t spl_arg_count(void);
extern SplArray* sys_get_args(void);
extern SplArray* rt_get_args(void);
extern SplArray* rt_cli_get_args(void);
extern int64_t rt_cli_arg_count(void);
extern int64_t rt_cli_arg_at(int64_t index);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_string_len(int64_t value);

static int failures = 0;

static void expect_len(const char* what, SplArray* array, int64_t want) {
    int64_t got = rt_array_len(array);
    if (got != want) {
        fprintf(stderr, "FAIL %s: rt_array_len=%lld want %lld (handle=0x%llx)\n",
                what, (long long)got, (long long)want,
                (unsigned long long)(uintptr_t)array);
        failures++;
    }
}

int main(int argc, char** argv) {
    spl_init_args(argc, argv);
    int64_t want = spl_arg_count();
    if (want < 2) {
        fprintf(stderr, "ERROR — nothing was checked (run with at least one argument)\n");
        return 2;
    }
    expect_len("sys_get_args", sys_get_args(), want);
    expect_len("rt_get_args", rt_get_args(), want);
    expect_len("rt_cli_get_args", rt_cli_get_args(), want);
    if (rt_cli_arg_count() != want) {
        fprintf(stderr, "FAIL rt_cli_arg_count=%lld want %lld\n",
                (long long)rt_cli_arg_count(), (long long)want);
        failures++;
    }
    /* rt_cli_arg_at must return a core tagged text value, not a legacy
     * SplValue struct: its length must match the C string. */
    int64_t last = want - 1;
    int64_t text_len = rt_string_len(rt_cli_arg_at(last));
    int64_t c_len = 0;
    while (argv[last][c_len] != '\0') c_len++;
    if (text_len != c_len) {
        fprintf(stderr, "FAIL rt_cli_arg_at(%lld) len=%lld want %lld\n",
                (long long)last, (long long)text_len, (long long)c_len);
        failures++;
    }
    if (failures != 0) {
        printf("FAIL — %d of 5 argv provider checks failed\n", failures);
        return 1;
    }
    printf("PASS — 5 argv provider checks, argc=%lld\n", (long long)want);
    return 0;
}
