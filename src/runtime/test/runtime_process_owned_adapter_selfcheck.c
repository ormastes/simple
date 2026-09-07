/* Windows: runtime_process_owned.c is gated `#if !defined(_WIN32) && defined(__unix__)` and has no Windows implementation,
 * so the behaviour exercised below does not exist on this platform.  The file is
 * still fed to the compiler by scripts/check/check-c-runtime-compiles-push.shs and
 * still proves it parses; it compiles to a well-formed no-op rather than being
 * excluded from the scan.  The POSIX body below is unchanged. */
#if defined(_WIN32)
int main(void) { return 0; }
#else
#include "../runtime.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct TestText { int64_t handle; const uint8_t* data; int64_t len; } TestText;
static TestText texts[64];
static int text_count;
static int host_alloc_call;
static int host_fail_at;
static int host_live;
static int runtime_alloc_call;
static int runtime_fail_at;

static void* injected_malloc(size_t size) {
    if (++host_alloc_call == host_fail_at) return NULL;
    void* ptr = malloc(size); if (ptr) host_live++; return ptr;
}
static void* injected_calloc(size_t count, size_t size) {
    if (++host_alloc_call == host_fail_at) return NULL;
    void* ptr = calloc(count, size); if (ptr) host_live++; return ptr;
}
static void injected_free(void* ptr) { if (ptr) host_live--; free(ptr); }
#define RT_OWNED_HOST_MALLOC injected_malloc
#define RT_OWNED_HOST_CALLOC injected_calloc
#define RT_OWNED_HOST_FREE injected_free

static int64_t test_text(const uint8_t* data, int64_t len) {
    int64_t handle = 0x100000 + text_count;
    texts[text_count++] = (TestText){handle, data, len};
    return handle;
}

int64_t rt_string_len(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) return texts[i].len;
    return -1;
}

const uint8_t* rt_string_data(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) return texts[i].data;
    return NULL;
}

int64_t rt_string_new(const uint8_t* data, uint64_t len) {
    if (++runtime_alloc_call == runtime_fail_at) return 0;
    uint8_t* copy = (uint8_t*)malloc((size_t)len + 1);
    assert(copy); memcpy(copy, data, (size_t)len); copy[len] = 0;
    return test_text(copy, (int64_t)len);
}

SplArray* rt_array_new(int64_t cap) {
    if (++runtime_alloc_call == runtime_fail_at) return NULL;
    SplArray* array = (SplArray*)calloc(1, sizeof(SplArray));
    assert(array); array->cap = cap > 0 ? cap : 1;
    array->items = (SplValue*)calloc((size_t)array->cap, sizeof(SplValue));
    assert(array->items); return array;
}

int64_t rt_array_len(SplArray* array) { return array ? array->len : -1; }
int64_t rt_array_get(SplArray* array, int64_t index) {
    return array && index >= 0 && index < array->len ? array->items[index].as_int : 3;
}
int8_t rt_array_push(SplArray* array, int64_t value) {
    if (!array || array->len >= array->cap) return 0;
    array->items[array->len++].as_int = value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
void* rt_alloc(int64_t size) {
    if (++runtime_alloc_call == runtime_fail_at) return NULL;
    return size > 0 ? calloc(1, (size_t)size) : NULL;
}
void rt_free(void* ptr) { free(ptr); }
void rt_array_free(SplArray* array) { if (array) { free(array->items); free(array); } }
int64_t rt_free_deep(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) { free((void*)texts[i].data); return 1; }
    return 0;
}

#include "../runtime_process_owned.c"

static SplArray* args_of(const int64_t* values, int64_t count) {
    SplArray* args = rt_array_new(count);
    for (int64_t i = 0; i < count; i++) assert(rt_array_push(args, values[i]));
    return args;
}

int main(void) {
    const uint8_t dash_c[] = "-c";
    const uint8_t script[] = "printf ok";
    int64_t values[] = {test_text(dash_c, 2), test_text(script, 9)};
    SplArray* args = args_of(values, 2);
    int64_t* tuple = rt_process_run_owned_bounded_value("/bin/sh", 7, args, 2000, 32);
    assert(tuple);
    assert(rt_string_len(tuple[0]) == 2);
    assert(memcmp(rt_string_data(tuple[0]), "ok", 2) == 0);
    SplArray* receipt = (SplArray*)(uintptr_t)tuple[2];
    assert(rt_array_len(receipt) == 19);
    assert(rt_array_get(receipt, 0) == RT_OWNED_PROCESS_RECEIPT_VERSION);
    assert(rt_array_get(receipt, 3) > 0 && rt_array_get(receipt, 5) > 0);
    assert(rt_array_get(receipt, 10) == 0 && rt_array_get(receipt, 15) == 1);

    int64_t* observed_tuple = rt_process_run_owned_observed_bounded_value("/bin/sh", 7, args, 2000, 32);
    assert(observed_tuple);
    SplArray* observed = (SplArray*)(uintptr_t)observed_tuple[2];
    assert(rt_array_len(observed) == 30);
    assert(rt_array_get(observed, 19) == RT_OWNED_PROCESS_OBSERVATION_VERSION);
    assert(rt_array_get(observed, 20) & RT_PROCESS_EVIDENCE_DIRECT_CHILD_RUSAGE);
    assert(rt_array_get(observed, 23) > 0);
    assert(rt_array_get(observed, 28) == 0);

    const uint8_t tree_script[] = "sleep 0.2 & wait";
    int64_t tree_values[] = {test_text(dash_c, 2), test_text(tree_script, 16)};
    int64_t* tree_tuple = rt_process_run_owned_observed_bounded_value(
        "/bin/sh", 7, args_of(tree_values, 2), 2000, 32);
    assert(tree_tuple);
    SplArray* tree_observed = (SplArray*)(uintptr_t)tree_tuple[2];
    assert(rt_array_get(tree_observed, 20) & RT_PROCESS_EVIDENCE_SAMPLED_TREE);
    assert(rt_array_get(tree_observed, 24) > 0);
    assert(rt_array_get(tree_observed, 27) >= 2);

    const uint8_t signal_script[] = "kill -SEGV $$";
    int64_t signal_values[] = {test_text(dash_c, 2), test_text(signal_script, 13)};
    int64_t* signal_tuple = rt_process_run_owned_observed_bounded_value(
        "/bin/sh", 7, args_of(signal_values, 2), 2000, 32);
    assert(signal_tuple);
    SplArray* signal_observed = (SplArray*)(uintptr_t)signal_tuple[2];
    /* The typed signal is the oracle.  The compatibility exit code remains
     * diagnostic evidence and must never be used to infer this cause. */
    assert(rt_array_get(signal_observed, 28) == SIGSEGV);
    assert(rt_array_get(signal_observed, 29) == 0);

    assert(!rt_process_run_owned_bounded_value("/bin/sh", 7, NULL, 10, 1));
    int64_t malformed[] = {42};
    assert(!rt_process_run_owned_bounded_value("/bin/sh", 7, args_of(malformed, 1), 10, 1));
    const char command_nul[] = {'/', 'b', 'i', 'n', '\0', 'x'};
    assert(!rt_process_run_owned_bounded_value(command_nul, sizeof(command_nul), args, 10, 1));
    const uint8_t arg_nul[] = {'a', 0, 'b'};
    int64_t embedded[] = {test_text(arg_nul, 3)};
    assert(!rt_process_run_owned_bounded_value("/bin/sh", 7, args_of(embedded, 1), 10, 1));

    for (int fail = 1; fail <= 6; fail++) {
        host_alloc_call = 0; host_fail_at = fail; host_live = 0;
        assert(!rt_process_run_owned_bounded_value("/bin/sh", 7, args, 2000, 32));
        assert(host_live == 0);
    }
    host_fail_at = 0;
    for (int fail = 1; fail <= 4; fail++) {
        runtime_alloc_call = 0; runtime_fail_at = fail;
        assert(!rt_process_run_owned_bounded_value("/bin/sh", 7, args, 2000, 32));
        assert(host_live == 0);
    }
    runtime_fail_at = 0;

    puts("runtime_process_owned_adapter_selfcheck: PASS");
    return 0;
}
#endif /* !_WIN32 */
