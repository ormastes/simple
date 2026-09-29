/* Real pin-owner integration: compile this test static, pin its own sealed
 * image through runtime_process.c, then execute that image only via fexecve. */
#if defined(_WIN32)
int main(void) { return 0; }
#else
#include "../runtime.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef struct TestText { int64_t handle; uint8_t* bytes; int64_t length; } TestText;
static TestText texts[16];
static int text_count;

static int64_t text_of(const uint8_t* bytes, int64_t length) {
    uint8_t* copy = (uint8_t*)malloc((size_t)length + 1);
    assert(copy); memcpy(copy, bytes, (size_t)length); copy[length] = 0;
    int64_t handle = 0x910000 + text_count;
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
    return text_of(bytes ? bytes : (const uint8_t*)"", (int64_t)length);
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
    if (!array || array->len < 0) return -1;
    for (int64_t i = 0; i < array->len; i++) if (rt_array_get(array, i) < 0 || rt_array_get(array, i) > 255) return -1;
    return array->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t capacity) {
    int64_t length = rt_array_bytes_validate(value);
    if (length < 0 || length > capacity || (length && !out)) return -1;
    SplArray* array = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < length; i++) out[i] = (uint8_t)rt_array_get(array, i);
    return length;
}

static SplArray* array_of(const int64_t* values, int64_t count) {
    SplArray* array = rt_array_new(count);
    for (int64_t i = 0; i < count; i++) assert(rt_array_push(array, values[i]));
    return array;
}
static int64_t field(SplArray* values, int64_t index) { return rt_array_get(values, index); }

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--owned-pin-child") == 0) {
        uint8_t bytes[3];
        if (read(STDIN_FILENO, bytes, sizeof(bytes)) != (ssize_t)sizeof(bytes)) return 90;
        if (write(STDOUT_FILENO, bytes, sizeof(bytes)) != (ssize_t)sizeof(bytes)) return 91;
        return 0;
    }
    const uint8_t child_arg[] = "--owned-pin-child";
    const int64_t args[] = {text_of(child_arg, (int64_t)sizeof(child_arg) - 1)};
    const int64_t input_values[] = {0, 0x80, 'Z'};

    /* Compatibility: the established raw-FD contract remains hashable via
     * /proc/self/fd and closable by its legacy close API. */
    int64_t legacy = rt_process_pin_executable("/proc/self/exe");
    assert(legacy >= 3);
    char legacy_path[64];
    int path_length = snprintf(legacy_path, sizeof(legacy_path), "/proc/self/fd/%lld", (long long)legacy);
    assert(path_length > 0 && access(legacy_path, R_OK) == 0);
    assert(rt_process_close_pinned_executable(legacy));
    assert(!rt_process_close_pinned_executable(legacy));

    int64_t owned = rt_process_pin_executable_owned("/proc/self/exe");
    assert(owned > 0 && owned != legacy);
    SplArray* start = rt_process_owned_v3_start_pinned_value(owned, array_of(args, 1),
        array_of(input_values, 3), 2000, 20, 1024);
    int64_t process = field(start, 0);
    assert(process > 0 && field(start, 2) == 1 && field(start, 3) == 0);
    int terminal = 0, saw_bytes = 0;
    for (int attempts = 0; attempts < 100 && !terminal; attempts++) {
        SplArray* poll = rt_process_owned_v3_poll_value(process, 20, 32, 32);
        assert(poll && field(poll, 2));
        SplArray* out = (SplArray*)(uintptr_t)field(poll, 0);
        SplArray* receipt = (SplArray*)(uintptr_t)field(poll, 2);
        if (field(receipt, 14)) {
            assert(field(out, 0) == 0 && field(out, 1) == 0x80 && field(out, 2) == 'Z');
            saw_bytes = 1;
        }
        terminal = field(receipt, 2) != 0;
    }
    assert(terminal && saw_bytes);
    SplArray* result = rt_process_owned_v3_collect_value(process);
    assert(field(result, 1) == 0 && field(result, 6) && field(result, 7));
    assert(rt_process_close_pinned_executable(owned));
    assert(rt_process_acquire_pinned_executable(owned) < 0);
    start = rt_process_owned_v3_start_pinned_value(owned, array_of(args, 1),
        array_of(input_values, 3), 1000, 20, 0);
    assert(field(start, 0) == 0 && field(start, 2) == 0 && field(start, 3) == ESTALE);
    puts("runtime_process_owned_pinned_integration_selfcheck: PASS");
    return 0;
}
#endif
