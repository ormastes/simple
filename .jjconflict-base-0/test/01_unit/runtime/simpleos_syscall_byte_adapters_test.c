#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static uint64_t seen_id;
static uint64_t seen_args[5];
static int alloc_calls;
static int successful_allocs;
static int free_calls;
static int fail_alloc_call;

void *rt_alloc(int64_t size) {
    ++alloc_calls;
    if (fail_alloc_call == alloc_calls) return NULL;
    ++successful_allocs;
    return malloc((size_t)size);
}
void rt_free(void *ptr) {
    if (ptr) ++free_calls;
    free(ptr);
}
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray *array = (SplArray *)(uintptr_t)value;
    return array ? array->len : -22;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t *out, int64_t capacity) {
    SplArray *array = (SplArray *)(uintptr_t)value;
    if (!array || capacity < array->len) return -22;
    for (int64_t i = 0; i < array->len; ++i) out[i] = (uint8_t)array->items[i].as_int;
    return array->len;
}
int64_t rt_array_bytes_store_checked(int64_t value, const uint8_t *input, int64_t length) {
    SplArray *array = (SplArray *)(uintptr_t)value;
    if (!array || length < 0 || length > array->len) return -22;
    for (int64_t i = 0; i < length; ++i) array->items[i].as_int = input[i];
    return length;
}

int64_t simpleos_syscall(uint64_t id, uint64_t a0, uint64_t a1,
                         uint64_t a2, uint64_t a3, uint64_t a4) {
    seen_id = id;
    seen_args[0] = a0;
    seen_args[1] = a1;
    seen_args[2] = a2;
    seen_args[3] = a3;
    seen_args[4] = a4;
    if (id == 31 || id == 76) {
        uint8_t *out = (uint8_t *)(uintptr_t)a1;
        for (uint64_t i = 0; i < a2; ++i) out[i] = (uint8_t)(0xa0u + i);
        return (int64_t)a2;
    }
    return 7;
}

static SplArray bytes(SplValue *items, int64_t length) {
    SplArray array = {.items = items, .len = length, .cap = length};
    return array;
}

int main(void) {
    SplValue path_items[3] = {
        {.tag = SPL_INT, .as_int = 'a'},
        {.tag = SPL_INT, .as_int = 'b'},
        {.tag = SPL_INT, .as_int = 'c'},
    };
    SplArray path = bytes(path_items, 3);
    assert(rt_simpleos_file_open_bytes((int64_t)(uintptr_t)&path, 9) == 7);
    assert(seen_id == 30 && seen_args[1] == 3 && seen_args[2] == 9);
    assert(successful_allocs == free_calls);

    int before_alloc = alloc_calls;
    int before_free = free_calls;
    fail_alloc_call = before_alloc + 1;
    assert(rt_simpleos_file_open_bytes((int64_t)(uintptr_t)&path, 9) == -12);
    assert(alloc_calls == before_alloc + 1 && free_calls == before_free);
    fail_alloc_call = 0;

    SplValue out_items[4] = {0};
    SplArray out = bytes(out_items, 4);
    assert(rt_simpleos_file_read_bytes(5, (int64_t)(uintptr_t)&out, 4) == 4);
    assert(seen_id == 31 && out_items[0].as_int == 0xa0 && out_items[3].as_int == 0xa3);
    assert(rt_simpleos_socket_recv_bytes(6, (int64_t)(uintptr_t)&out, 5) == -22);

    SplValue addr_items[16] = {0};
    SplArray addr = bytes(addr_items, 16);
    assert(rt_simpleos_socket_bind_bytes(8, (int64_t)(uintptr_t)&addr) == 7);
    assert(seen_id == 71 && seen_args[2] == 16);
    addr.len = 15;
    assert(rt_simpleos_socket_connect_bytes(8, (int64_t)(uintptr_t)&addr) == -22);

    SplValue new_items[1] = {{.tag = SPL_INT, .as_int = 'z'}};
    SplArray new_path = bytes(new_items, 1);
    assert(rt_simpleos_file_rename_bytes(
               (int64_t)(uintptr_t)&path, (int64_t)(uintptr_t)&new_path) == 7);
    assert(seen_id == 44 && seen_args[1] == 3 && seen_args[3] == 1);
    assert(successful_allocs == free_calls);

    before_alloc = alloc_calls;
    before_free = free_calls;
    fail_alloc_call = before_alloc + 2;
    assert(rt_simpleos_file_rename_bytes(
               (int64_t)(uintptr_t)&path, (int64_t)(uintptr_t)&new_path) == -12);
    assert(alloc_calls == before_alloc + 2 && free_calls == before_free + 1);
    assert(successful_allocs == free_calls);
    fail_alloc_call = 0;

    SplArray empty = bytes(NULL, 0);
    assert(rt_simpleos_file_open_bytes((int64_t)(uintptr_t)&empty, 0) == -22);
    SplArray too_large = bytes(NULL, 1024 * 1024 + 1);
    assert(rt_simpleos_file_write_bytes(4, (int64_t)(uintptr_t)&too_large) == -75);
    return 0;
}
