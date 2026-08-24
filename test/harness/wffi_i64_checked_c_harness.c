/* Cross-lane contract harness for the pure-C checked i64 WFFI transport. */
#include "../../src/runtime/runtime_native.c"

static int checked = 0;
static int failed = 0;

static int64_t zero_value(void) { return 0; }
static int64_t add_values(int64_t a, int64_t b) { return a + b; }

static void report(const char* name, int ok) {
    checked++;
    if (!ok) failed++;
    printf("[%s] %s\n", ok ? " ok " : "FAIL", name);
}

static int64_t result_at(int64_t result, int64_t index) {
    return rt_value_as_int(rt_array_get((SplArray*)(uintptr_t)result, index));
}

static void release_result(int64_t result) {
    rt_array_free((SplArray*)(uintptr_t)result);
}

int main(void) {
    SplArray* empty = rt_array_new(0);
    int64_t result = spl_wffi_call_i64_checked(
        (int64_t)(intptr_t)zero_value, (int64_t)(uintptr_t)empty, 0);
    report("valid foreign zero remains success", result_at(result, 0) == 0 && result_at(result, 1) == 0);
    release_result(result);

    SplArray* two = rt_array_new(2);
    rt_array_push(two, rt_value_int(20));
    rt_array_push(two, rt_value_int(22));
    result = spl_wffi_call_i64_checked(
        (int64_t)(intptr_t)add_values, (int64_t)(uintptr_t)two, 2);
    report("two integer arguments preserve value", result_at(result, 0) == 0 && result_at(result, 1) == 42);
    release_result(result);

    result = spl_wffi_call_i64_checked(0, (int64_t)(uintptr_t)empty, 0);
    report("null function is status 2", result_at(result, 0) == 2);
    release_result(result);

    result = spl_wffi_call_i64_checked(
        (int64_t)(intptr_t)zero_value, (int64_t)(uintptr_t)empty, 9);
    report("unsupported arity is status 3", result_at(result, 0) == 3);
    release_result(result);

    result = spl_wffi_call_i64_checked(
        (int64_t)(intptr_t)add_values, (int64_t)(uintptr_t)empty, 2);
    report("short argument array is status 1", result_at(result, 0) == 1);
    release_result(result);

    SplArray* invalid = rt_array_new(1);
    rt_array_push(invalid, rt_core_nil());
    result = spl_wffi_call_i64_checked(
        (int64_t)(intptr_t)zero_value, (int64_t)(uintptr_t)invalid, 1);
    report("non-integer argument is status 1", result_at(result, 0) == 1);
    release_result(result);

    rt_array_free(empty);
    rt_array_free(two);
    rt_array_free(invalid);

    if (checked == 0) {
        printf("ERROR — nothing was checked\n");
        return 2;
    }
    if (failed != 0) {
        printf("FAIL — %d of %d checked C WFFI case(s) failed\n", failed, checked);
        return 1;
    }
    printf("PASS — %d checked C WFFI case(s)\n", checked);
    return 0;
}
