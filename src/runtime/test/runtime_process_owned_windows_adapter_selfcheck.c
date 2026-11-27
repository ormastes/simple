/* Real Win32 opaque-handle/SplArray ABI test. Includes the production provider,
 * without CORE_ONLY; the small value host supplies only array/text allocation.
 * This is native boundary evidence, not self-hosted Simple qualification. */
#include <stdio.h>
#if !defined(_WIN32)
int main(void) { fputs("UNSUPPORTED: native Windows required\n", stderr); return 77; }
#else
#ifdef NDEBUG
#error "The adapter selfcheck requires active assertions"
#endif
#include <windows.h>
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "../runtime.h"

typedef struct TestText { int64_t handle, length; uint8_t* data; } TestText;
static TestText texts[64];
static int text_count;
static int checks;
static void check(int condition, const char* name) {
    ++checks;
    if (!condition) { fprintf(stderr, "FAIL: %s (check %d)\n", name, checks); exit(1); }
}
int64_t rt_string_len(int64_t value) {
    for (int i = 0; i < text_count; ++i) if (texts[i].handle == value) return texts[i].length;
    return -1;
}
const uint8_t* rt_string_data(int64_t value) {
    for (int i = 0; i < text_count; ++i) if (texts[i].handle == value) return texts[i].data;
    return NULL;
}
int64_t rt_string_new(const uint8_t* data, uint64_t length) {
    assert(text_count < 64 && length < SIZE_MAX);
    uint8_t* copy = (uint8_t*)malloc((size_t)length + 1);
    assert(copy); memcpy(copy, data, (size_t)length); copy[length] = 0;
    int64_t handle = 0x100000 + text_count;
    texts[text_count++] = (TestText){handle, (int64_t)length, copy};
    return handle;
}
SplArray* rt_array_new(int64_t capacity) {
    SplArray* array = (SplArray*)calloc(1, sizeof(*array)); assert(array);
    array->cap = capacity > 0 ? capacity : 1;
    array->items = (SplValue*)calloc((size_t)array->cap, sizeof(*array->items));
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
int8_t rt_array_set(SplArray* array, int64_t index, int64_t value) {
    if (!array || index < 0 || index >= array->len) return 0;
    array->items[index].as_int = value; return 1;
}
void rt_array_free(SplArray* array) { if (array) { free(array->items); free(array); } }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    if (!array || array->len < 0) return -1;
    for (int64_t i = 0; i < array->len; ++i)
        if (rt_array_get(array, i) < 0 || rt_array_get(array, i) > 255) return -1;
    return array->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* output, int64_t capacity) {
    int64_t count = rt_array_bytes_validate(value);
    if (count < 0 || count > capacity || (count && !output)) return -1;
    for (int64_t i = 0; i < count; ++i) output[i] = (uint8_t)rt_array_get((SplArray*)(uintptr_t)value, i);
    return count;
}
int64_t rt_value_int(int64_t value) { return value; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_tuple_new(int64_t length) {
    SplArray* tuple = rt_array_new(length); tuple->len = length; return (int64_t)(uintptr_t)tuple;
}
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    return rt_array_set((SplArray*)(uintptr_t)tuple, index, value);
}
int64_t rt_tuple_get(int64_t tuple, int64_t index) { return rt_array_get((SplArray*)(uintptr_t)tuple, index); }
int64_t rt_free_deep(int64_t value) {
    for (int i = 0; i < text_count; ++i) if (texts[i].handle == value) {
        free(texts[i].data); texts[i].data = NULL; return 1;
    }
    return 0;
}
int64_t rt_process_acquire_pinned_executable(int64_t handle) { (void)handle; return -1; }

#include "../runtime_process_owned.c"
#ifndef RT_OWNED_WIN32_V3_ADAPTER
#error "The real Windows opaque adapter must be compiled"
#endif
#ifdef RT_PROCESS_OWNED_CORE_ONLY
#error "CORE_ONLY would omit the adapter under test"
#endif

static int live_adapter_slots(void) {
    int count = 0;
    for (uint32_t i = 0; i < OWNED_WIN_V3_SLOTS; ++i) if (owned_win_v3_slots[i].active) ++count;
    return count;
}
static SplArray* arguments(const char* mode, int special) {
    SplArray* array = rt_array_new(special ? 4 : 1);
    assert(rt_array_push(array, rt_string_new((const uint8_t*)mode, strlen(mode))));
    if (special) {
        const char* values[] = {"two words", "", "quote\"and\\tail\\"};
        for (int i = 0; i < 3; ++i)
            assert(rt_array_push(array, rt_string_new((const uint8_t*)values[i], strlen(values[i]))));
    }
    return array;
}
static int64_t start(const char* executable, const char* mode, int special, int64_t timeout, int64_t cap) {
    SplArray* args = arguments(mode, special);
    SplArray* input = rt_array_new(0);
    SplArray* receipt = rt_process_owned_v3_start_value(executable, strlen(executable), args, input, timeout, 20, cap);
    check(receipt && rt_array_len(receipt) == 4, "start receipt shape");
    check(rt_array_get(receipt, 1) == RT_OWNED_PROCESS_OPAQUE_V3_VERSION, "start version");
    check(rt_array_get(receipt, 2) == 1 && rt_array_get(receipt, 3) == 0, "start accepted");
    int64_t handle = rt_array_get(receipt, 0);
    check(handle > 0 && live_adapter_slots() == 1, "opaque positive handle owns exactly one slot");
    rt_array_free(receipt); rt_array_free(args); rt_array_free(input);
    return handle;
}
typedef struct Capture { char out[256], err[256]; size_t out_count, err_count; int64_t result[15]; } Capture;
static void capture_and_collect(int64_t handle, Capture* capture) {
    memset(capture, 0, sizeof(*capture));
    int drained = 0;
    for (int attempt = 0; attempt < 250; ++attempt) {
        SplArray* tuple = rt_process_owned_v3_poll_value(handle, 20, 64, 64);
        check(tuple && rt_array_len(tuple) == 3, "poll tuple shape");
        SplArray* out = (SplArray*)(uintptr_t)rt_array_get(tuple, 0);
        SplArray* err = (SplArray*)(uintptr_t)rt_array_get(tuple, 1);
        SplArray* words = (SplArray*)(uintptr_t)rt_array_get(tuple, 2);
        check(words && rt_array_len(words) == 17, "poll receipt shape");
        check(rt_array_get(words, 0) == RT_OWNED_PROCESS_OPAQUE_V3_VERSION, "poll version");
        check(rt_array_get(words, 16) == 0, "poll has no provider error");
        check(rt_array_len(out) == rt_array_get(words, 14) && rt_array_len(err) == rt_array_get(words, 15), "byte-array counts match receipt");
        check(capture->out_count + (size_t)rt_array_len(out) < sizeof(capture->out), "stdout test buffer bound");
        check(capture->err_count + (size_t)rt_array_len(err) < sizeof(capture->err), "stderr test buffer bound");
        for (int64_t i = 0; i < rt_array_len(out); ++i) capture->out[capture->out_count++] = (char)rt_array_get(out, i);
        for (int64_t i = 0; i < rt_array_len(err); ++i) capture->err[capture->err_count++] = (char)rt_array_get(err, i);
        drained = rt_array_get(words, 2) == 1 && rt_array_get(words, 14) == 0 && rt_array_get(words, 15) == 0;
        rt_array_free(out); rt_array_free(err); rt_array_free(words); rt_array_free(tuple);
        if (drained) break;
    }
    check(drained, "terminal child and both output streams drained before deadline");
    SplArray* result = rt_process_owned_v3_result_value(handle);
    check(result && rt_array_len(result) == 15, "result shape");
    for (int i = 0; i < 15; ++i) capture->result[i] = rt_array_get(result, i);
    check(capture->result[0] == RT_OWNED_PROCESS_OPAQUE_V3_VERSION, "result version");
    check(capture->result[7] == 1 && capture->result[14] == 0, "child reaped without provider error");
    check(live_adapter_slots() == 1, "result observation retains ownership");
    SplArray* collected = rt_process_owned_v3_collect_value(handle);
    check(collected && rt_array_len(collected) == 15, "collect shape");
    for (int i = 0; i < 15; ++i) check(rt_array_get(collected, i) == capture->result[i], "collect preserves terminal receipt fields");
    check(live_adapter_slots() == 0, "collect consumes exactly one opaque lease");
    rt_array_free(result); rt_array_free(collected);
    SplArray* stale = rt_process_owned_v3_result_value(handle);
    check(stale && rt_array_get(stale, 14) == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR, "consumed handle is stale");
    check(!rt_process_owned_v3_release_value(handle), "double release cannot consume a stale lease");
    rt_array_free(stale);
}
int main(int argc, char** argv) {
    if (argc > 1 && strcmp(argv[1], "--child-argv") == 0) {
        if (argc != 5 || strcmp(argv[2], "two words") || strcmp(argv[3], "") || strcmp(argv[4], "quote\"and\\tail\\")) return 97;
        fputs("argv-ok", stdout); fputs("stderr-ok", stderr); return 7;
    }
    if (argc > 1 && strcmp(argv[1], "--child-wait") == 0) { Sleep(30000); return 98; }
    if (argc > 1 && strcmp(argv[1], "--child-flood") == 0) {
        for (int i = 0; i < 256; ++i) fputc('A', stdout);
        for (int i = 0; i < 192; ++i) fputc('B', stderr);
        return 0;
    }
    char self[32768];
    DWORD length = GetModuleFileNameA(NULL, self, sizeof(self));
    check(length > 0 && length < sizeof(self), "resolve own executable");
    check(live_adapter_slots() == 0, "initial adapter owner set empty");
    Capture normal;
    int64_t first = start(self, "--child-argv", 1, 3000, 64);
    capture_and_collect(first, &normal);
    check(strcmp(normal.out, "argv-ok") == 0 && strcmp(normal.err, "stderr-ok") == 0, "argv spacing, empty and quote/backslash boundaries and split output");
    check(normal.result[1] == 7 && !normal.result[2], "actual nonzero child status retained");

    SplArray* invalid = rt_array_new(1);
    const uint8_t embedded_nul[] = {'a', 0, 'b'};
    assert(rt_array_push(invalid, rt_string_new(embedded_nul, sizeof(embedded_nul))));
    SplArray* empty = rt_array_new(0);
    SplArray* rejected = rt_process_owned_v3_start_value(self, strlen(self), invalid, empty, 100, 20, 32);
    check(rejected && rt_array_len(rejected) == 4 && rt_array_get(rejected, 0) == 0 && !rt_array_get(rejected, 2), "embedded NUL argument rejected before ownership");
    check(rt_array_get(rejected, 3) == EINVAL && live_adapter_slots() == 0, "rejected argument creates no opaque lease");
    rt_array_free(rejected); rt_array_free(invalid); rt_array_free(empty);

    Capture timeout;
    int64_t timed = start(self, "--child-wait", 0, 50, 32);
    capture_and_collect(timed, &timeout);
    check(timeout.result[2] == 1 && timeout.out_count == 0, "deadline terminates and reaps the owned child");

    Capture flood;
    int64_t flooded = start(self, "--child-flood", 0, 3000, 32);
    capture_and_collect(flooded, &flood);
    check(flood.out_count <= 32 && flood.err_count <= 32, "output capture bounded independently");
    check(flood.result[8] && flood.result[9] && flood.result[10] >= 256 && flood.result[11] >= 192, "both truncation and seen-byte fields retained");

    Capture cancelled;
    int64_t current = start(self, "--child-wait", 0, 3000, 32);
    SplArray* early = rt_process_owned_v3_collect_value(current);
    check(early && rt_array_get(early, 14) == EAGAIN && live_adapter_slots() == 1, "early collect fails without consuming live ownership");
    rt_array_free(early);
    SplArray* stale_cancel = rt_process_owned_v3_cancel_value(first);
    check(stale_cancel && !rt_array_get(stale_cancel, 1) && rt_array_get(stale_cancel, 3) == RT_OWNED_PROCESS_WINDOWS_STALE_ERROR, "old handle cannot cancel the reused slot");
    rt_array_free(stale_cancel);
    SplArray* cancel = rt_process_owned_v3_cancel_value(current);
    check(cancel && rt_array_get(cancel, 1) == 1 && rt_array_get(cancel, 3) == 0, "current owner can cancel its lease");
    rt_array_free(cancel);
    capture_and_collect(current, &cancelled);
    check(cancelled.result[3] == 1, "cancel receipt propagates to final result");
    check(live_adapter_slots() == 0, "all native adapter leases consumed");
    printf("PASS Windows opaque process adapter checks=%d\n", checks);
    for (int i = 0; i < text_count; ++i) free(texts[i].data);
    return 0;
}
#endif
