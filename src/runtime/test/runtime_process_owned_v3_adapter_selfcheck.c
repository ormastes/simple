/* Focused opaque V3 bridge test.  It includes the provider with a tiny value
 * runtime so its array/text boundary is exercised rather than cast away. */
#if defined(_WIN32)
int main(void) { return 0; }
#else
#include "../runtime.h"

#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>

typedef struct TestText { int64_t handle; uint8_t* bytes; int64_t length; } TestText;
static TestText texts[32];
static int text_count;

static int64_t test_text(const uint8_t* bytes, int64_t length) {
    uint8_t* copy = (uint8_t*)malloc((size_t)length + 1);
    assert(copy); memcpy(copy, bytes, (size_t)length); copy[length] = 0;
    int64_t handle = 0x700000 + text_count;
    texts[text_count++] = (TestText){handle, copy, length};
    return handle;
}
int64_t rt_string_len(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) return texts[i].length;
    return -1;
}
const uint8_t* rt_string_data(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) return texts[i].bytes;
    return NULL;
}
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) {
    return test_text(bytes ? bytes : (const uint8_t*)"", (int64_t)length);
}
SplArray* rt_array_new(int64_t capacity) {
    SplArray* array = (SplArray*)calloc(1, sizeof(*array));
    assert(array); array->cap = capacity > 0 ? capacity : 1;
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
int64_t rt_value_int(int64_t value) { return value; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
void rt_array_free(SplArray* array) { if (array) { free(array->items); free(array); } }
int64_t rt_free_deep(int64_t value) {
    for (int i = 0; i < text_count; i++) if (texts[i].handle == value) { free(texts[i].bytes); return 1; }
    return 0;
}
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    if (!array || array->len < 0 || array->len > INT64_MAX) return -1;
    for (int64_t i = 0; i < array->len; i++) if (rt_array_get(array, i) < 0 || rt_array_get(array, i) > 255) return -1;
    return array->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t capacity) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    int64_t length = rt_array_bytes_validate(value);
    if (length < 0 || length > capacity || (length && !out)) return -1;
    for (int64_t i = 0; i < length; i++) out[i] = (uint8_t)rt_array_get(array, i);
    return length;
}
static int pinned_self_fd = -1;
int64_t rt_process_acquire_pinned_executable(int64_t handle) {
    if (handle != 77 || pinned_self_fd < 0) return -1;
    return fcntl(pinned_self_fd, F_DUPFD_CLOEXEC, 3);
}

#include "../runtime_process_owned.c"

static SplArray* array_of(const int64_t* values, int64_t count) {
    SplArray* array = rt_array_new(count);
    for (int64_t i = 0; i < count; i++) assert(rt_array_push(array, values[i]));
    return array;
}
static int64_t field(SplArray* receipt, int64_t index) { return rt_array_get(receipt, index); }

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--pinned-child") == 0) {
        uint8_t bytes[3];
        if (read(STDIN_FILENO, bytes, sizeof(bytes)) != (ssize_t)sizeof(bytes)) return 90;
        if (write(STDOUT_FILENO, bytes, sizeof(bytes)) != (ssize_t)sizeof(bytes)) return 91;
        return 0;
    }
    const uint8_t dash_c[] = "-c", cat_script[] = "cat", sleep_script[] = "sleep 3", exit_script[] = "exit 0";
    int64_t cat_args[] = {test_text(dash_c, 2), test_text(cat_script, 3)};
    int64_t input_values[] = {0, 0x80, 'A'};
    SplArray* start = rt_process_owned_v3_start_value("/bin/sh", 7, array_of(cat_args, 2),
        array_of(input_values, 3), 2000, 20, 1024);
    assert(start && field(start, 1) == RT_OWNED_PROCESS_OPAQUE_V3_VERSION && field(start, 2) == 1);
    int64_t handle = field(start, 0);
    assert(handle > 0 && handle != 1);
    SplArray* input = rt_process_owned_v3_input_value(handle);
    assert(field(input, 1) == 3 && field(input, 2) <= 3 && field(input, 6) == 0);
    int terminal = 0, saw_bytes = 0;
    for (int attempts = 0; attempts < 100 && !terminal; attempts++) {
        SplArray* poll = rt_process_owned_v3_poll_value(handle, 20, 32, 32);
        assert(poll && rt_array_len(poll) == 3);
        SplArray* out = (SplArray*)(uintptr_t)field(poll, 0);
        SplArray* receipt = (SplArray*)(uintptr_t)field(poll, 2);
        assert(field(receipt, 0) == RT_OWNED_PROCESS_OPAQUE_V3_VERSION && field(receipt, 16) == 0);
        if (field(receipt, 14)) {
            assert(field(receipt, 14) == rt_array_len(out));
            assert(field(out, 0) == 0 && field(out, 1) == 0x80 && field(out, 2) == 'A');
            saw_bytes = 1;
        }
        terminal = field(receipt, 2) != 0;
    }
    assert(terminal && saw_bytes);
    input = rt_process_owned_v3_input_value(handle);
    assert(field(input, 1) == 3 && field(input, 2) == 3 && field(input, 3) && field(input, 4) && field(input, 5));
    SplArray* collected = rt_process_owned_v3_collect_value(handle);
    assert(field(collected, 7) && field(collected, 14) == 0);
    SplArray* stale_poll = rt_process_owned_v3_poll_value(handle, 0, 1, 1);
    assert(field((SplArray*)(uintptr_t)field(stale_poll, 2), 16) == ESTALE);
    assert(field(rt_process_owned_v3_result_value(0x1234), 14) == ESTALE);

    SplArray forged = {NULL, (int64_t)RT_OWNED_PROCESS_MAX_INPUT_BYTES + 1,
                       (int64_t)RT_OWNED_PROCESS_MAX_INPUT_BYTES + 1};
    start = rt_process_owned_v3_start_value("/bin/sh", 7, array_of(cat_args, 2), &forged, 1000, 20, 0);
    assert(field(start, 0) == 0 && field(start, 2) == 0 && field(start, 3) == EINVAL);

    int64_t sleep_args[] = {test_text(dash_c, 2), test_text(sleep_script, 7)};
    start = rt_process_owned_v3_start_value("/bin/sh", 7, array_of(sleep_args, 2), array_of(NULL, 0), 4000, 20, 0);
    handle = field(start, 0); assert(handle > 0);
    SplArray* cancel = rt_process_owned_v3_cancel_value(handle);
    assert(field(cancel, 1) && field(cancel, 2));
    collected = rt_process_owned_v3_collect_value(handle);
    assert(field(collected, 7));

    int64_t exit_args[] = {test_text(dash_c, 2), test_text(exit_script, 6)};
    start = rt_process_owned_v3_start_value("/bin/sh", 7, array_of(exit_args, 2), array_of(NULL, 0), 1000, 20, 0);
    handle = field(start, 0); assert(handle > 0);
    for (int attempts = 0; attempts < 100; attempts++) {
        SplArray* poll = rt_process_owned_v3_poll_value(handle, 20, 1, 1);
        if (field((SplArray*)(uintptr_t)field(poll, 2), 2)) break;
    }
    assert(rt_process_owned_v3_release_value(handle));
    assert(!rt_process_owned_v3_release_value(handle)); /* idempotent no-detach */

    /* This binary is compiled static by the focused command.  The owner stub
     * models the private duplicate returned under the pin registry lock; the
     * V3 path must fexecve it with fixed cwd/env and byte-exact stdin. */
    pinned_self_fd = open("/proc/self/exe", O_RDONLY | O_CLOEXEC);
    assert(pinned_self_fd >= 3);
    const uint8_t child_arg[] = "--pinned-child";
    int64_t pinned_args[] = {test_text(child_arg, (int64_t)sizeof(child_arg) - 1)};
    start = rt_process_owned_v3_start_pinned_value(77, array_of(pinned_args, 1),
        array_of(input_values, 3), 2000, 20, 1024);
    handle = field(start, 0); assert(handle > 0 && field(start, 2));
    terminal = 0; saw_bytes = 0;
    for (int attempts = 0; attempts < 100 && !terminal; attempts++) {
        SplArray* poll = rt_process_owned_v3_poll_value(handle, 20, 32, 32);
        SplArray* out = (SplArray*)(uintptr_t)field(poll, 0);
        SplArray* receipt = (SplArray*)(uintptr_t)field(poll, 2);
        if (field(receipt, 14)) {
            assert(field(out, 0) == 0 && field(out, 1) == 0x80 && field(out, 2) == 'A');
            saw_bytes = 1;
        }
        terminal = field(receipt, 2) != 0;
    }
    assert(terminal && saw_bytes);
    collected = rt_process_owned_v3_collect_value(handle);
    assert(field(collected, 1) == 0 && field(collected, 6) && field(collected, 7));
    close(pinned_self_fd); pinned_self_fd = -1;
    puts("runtime_process_owned_v3_adapter_selfcheck: PASS");
    return 0;
}
#endif
