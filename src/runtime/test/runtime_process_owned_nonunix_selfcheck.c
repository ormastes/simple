#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int64_t rt_value_int(int64_t value) { return value; }
SplArray* rt_array_new(int64_t cap) {
    SplArray* array = calloc(1, sizeof(*array));
    array->cap = cap; array->items = calloc((size_t)cap, sizeof(*array->items)); return array;
}
int8_t rt_array_push(SplArray* array, int64_t value) {
    if (!array || array->len >= array->cap) return 0;
    array->items[array->len++].as_int = value; return 1;
}
int64_t rt_array_len(SplArray* array) { return array ? array->len : -1; }
int64_t rt_array_get(SplArray* array, int64_t index) { return array->items[index].as_int; }
int64_t rt_string_new(const uint8_t* data, uint64_t len) { (void)data; (void)len; return 7; }
void* rt_alloc(int64_t size) { return calloc(1, (size_t)size); }
void rt_free(void* ptr) { free(ptr); }
void rt_array_free(SplArray* array) { free(array->items); free(array); }
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }

#define _WIN32 1
#include "../runtime_process_owned.c"

int main(void) {
    RtOwnedProcessTokenV2 token;
    RtOwnedProcessStartReceiptV2 start;
    const char* argv[] = {"never-spawned", NULL};
    assert(!rt_process_owned_start_v2(argv[0], argv, 1000, 100, 16, &token, &start));
    assert(start.runtime_error == ENOTSUP && token.high == 0 && token.low == 0);
    int64_t* tuple = rt_process_run_owned_bounded_value(NULL, 0, NULL, 0, 0);
    assert(tuple);
    SplArray* receipt = (SplArray*)(uintptr_t)tuple[2];
    assert(rt_array_len(receipt) == 19);
    assert(rt_array_get(receipt, 0) == RT_OWNED_PROCESS_RECEIPT_VERSION);
    assert(rt_array_get(receipt, 10) == -1);
    assert(rt_array_get(receipt, 18) == ENOTSUP);
    puts("runtime_process_owned_nonunix_selfcheck: PASS");
    return 0;
}
