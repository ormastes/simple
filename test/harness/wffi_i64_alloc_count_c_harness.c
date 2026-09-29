/* Allocation census for the checked i64 WFFI transports.
 *
 * Counts real heap allocations performed per checked call, for both the legacy
 * `[status, value]` array transport and the scalar status/out transport. Built
 * as a single TU (runtime_native.c is #included, exactly as
 * wffi_i64_checked_c_harness.c does) and linked with
 * `-Wl,--wrap=malloc,--wrap=calloc,--wrap=realloc`, so every allocation the
 * runtime performs on the call path is redirected through the counters below.
 *
 * The array transport MUST report a non-zero per-call figure: that is what
 * proves the counter discriminates, so the scalar transport's zero cannot be a
 * vacuous "the counter never fired" result.
 */
#include <stddef.h>
#include <stdint.h>

void* __real_malloc(size_t size);
void* __real_calloc(size_t count, size_t size);
void* __real_realloc(void* ptr, size_t size);

static long alloc_count = 0;

void* __wrap_malloc(size_t size) {
    alloc_count++;
    return __real_malloc(size);
}

void* __wrap_calloc(size_t count, size_t size) {
    alloc_count++;
    return __real_calloc(count, size);
}

void* __wrap_realloc(void* ptr, size_t size) {
    alloc_count++;
    return __real_realloc(ptr, size);
}

#include "../../src/runtime/runtime_native.c"

#define WFFI_ALLOC_ITERATIONS 10000

static int64_t add_values(int64_t a, int64_t b) { return a + b; }

int main(void) {
    SplArray* args = rt_array_new(2);
    rt_array_push(args, rt_value_int(3));
    rt_array_push(args, rt_value_int(4));
    int64_t args_value = (int64_t)(uintptr_t)args;
    int64_t fptr = (int64_t)(intptr_t)add_values;
    int failed = 0;

    /* Status parity across every documented outcome. The same four cases are
     * asserted against the Rust provider by the `try_call_i64_out_*` tests in
     * src/compiler_rust/runtime/src/value/wsffi_native.rs, so the two lanes are
     * pinned to one status table and a dual-run shadow cannot diverge. */
    struct {
        const char* name;
        int64_t nargs;
        int64_t use_null_fptr;
        int64_t expect_status;
        int64_t expect_value;
    } cases[] = {
        {"valid call yields status 0 and the foreign result", 2, 0, 0, 7},
        {"null function pointer yields status 2", 2, 1, 2, 0},
        {"count beyond the argument array yields status 1", 3, 0, 1, 0},
        {"arity above eight yields status 3", 9, 0, 3, 0},
    };
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
        int64_t call_fptr = cases[i].use_null_fptr ? 0 : fptr;
        int64_t out = -1;
        int64_t out_status = spl_wffi_try_call_i64_out(call_fptr, args_value, cases[i].nargs, &out);
        int64_t legacy = spl_wffi_call_i64_checked(call_fptr, args_value, cases[i].nargs);
        int64_t legacy_status = rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)legacy, 0));
        int64_t legacy_value = rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)legacy, 1));
        rt_array_free((SplArray*)(uintptr_t)legacy);
        int ok = out_status == cases[i].expect_status && out == cases[i].expect_value
                 && legacy_status == cases[i].expect_status && legacy_value == cases[i].expect_value;
        printf("[%s] %s (out=%lld/%lld array=%lld/%lld)\n", ok ? " ok " : "FAIL", cases[i].name,
               (long long)out_status, (long long)out, (long long)legacy_status, (long long)legacy_value);
        if (!ok) failed = 1;
    }
    {
        int64_t null_out_status = spl_wffi_try_call_i64_out(fptr, args_value, 2, NULL);
        int ok = null_out_status == 1;
        printf("[%s] a null output slot yields status 1 (%lld)\n", ok ? " ok " : "FAIL",
               (long long)null_out_status);
        if (!ok) failed = 1;
    }

    long before = alloc_count;
    for (int i = 0; i < WFFI_ALLOC_ITERATIONS; i++) {
        int64_t result = spl_wffi_call_i64_checked(fptr, args_value, 2);
        rt_array_free((SplArray*)(uintptr_t)result);
    }
    long array_allocs = alloc_count - before;

    before = alloc_count;
    int64_t out_value = 0;
    for (int i = 0; i < WFFI_ALLOC_ITERATIONS; i++) {
        (void)spl_wffi_try_call_i64_out(fptr, args_value, 2, &out_value);
    }
    long out_allocs = alloc_count - before;

    printf("iterations=%d\n", WFFI_ALLOC_ITERATIONS);
    printf("array_transport_allocs=%ld per_call=%.4f\n",
           array_allocs, (double)array_allocs / (double)WFFI_ALLOC_ITERATIONS);
    printf("out_transport_allocs=%ld per_call=%.4f\n",
           out_allocs, (double)out_allocs / (double)WFFI_ALLOC_ITERATIONS);

    if (array_allocs <= 0) {
        printf("[FAIL] array transport reported zero allocations; counter is not discriminating\n");
        failed = 1;
    } else {
        printf("[ ok ] array transport allocates on every checked call\n");
    }
    if (out_allocs != 0) {
        printf("[FAIL] scalar out transport allocated %ld time(s)\n", out_allocs);
        failed = 1;
    } else {
        printf("[ ok ] scalar out transport allocates nothing\n");
    }
    return failed;
}
