/* Support-only test doubles for hosted-owner selfchecks. File-lock behavior
 * always comes from production runtime_host_file_exports.c. */
#include "../runtime.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct { uint64_t len; uint8_t* data; } TestString;

int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    TestString* string = (TestString*)malloc(sizeof(TestString));
    if (!string) return 0;
    string->data = (uint8_t*)malloc(len ? len : 1);
    if (!string->data) { free(string); return 0; }
    memcpy(string->data, bytes, len);
    string->len = len;
    return (int64_t)(intptr_t)string;
}
int64_t rt_string_len(int64_t value) { return value ? (int64_t)((TestString*)(intptr_t)value)->len : 0; }
const uint8_t* rt_string_data(int64_t value) { return value ? ((TestString*)(intptr_t)value)->data : NULL; }
int64_t rt_string_free(int64_t value) {
    if (!value) return 0;
    free(((TestString*)(intptr_t)value)->data);
    free((void*)(intptr_t)value);
    return 0;
}

SplArray* rt_byte_array_new_len(uint64_t len) {
    SplArray* array = (SplArray*)calloc(1, sizeof(SplArray));
    if (!array) return NULL;
    array->items = (SplValue*)calloc(len ? (size_t)len : 1U, sizeof(SplValue));
    if (!array->items) { free(array); return NULL; }
    array->len = (int64_t)len;
    array->cap = (int64_t)len;
    return array;
}
int64_t rt_array_bytes_store_checked(int64_t value, const uint8_t* bytes, int64_t length) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    if (!array || length < 0 || length > array->len || (length && !bytes)) return -1;
    for (int64_t i = 0; i < length; i++) array->items[i].as_int = bytes[i];
    return length;
}
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    if (!array || array->len < 0) return -1;
    for (int64_t i = 0; i < array->len; i++) {
        int64_t byte = array->items[i].as_int;
        if (byte < 0 || byte > 255) return -1;
    }
    return array->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t capacity) {
    int64_t length = rt_array_bytes_validate(value);
    if (length < 0 || length > capacity || (length && !out)) return -1;
    SplArray* array = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < length; i++) out[i] = (uint8_t)array->items[i].as_int;
    return length;
}
void rt_array_free(SplArray* array) {
    if (array) { free(array->items); free(array); }
}
