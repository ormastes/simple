#include "runtime.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

static uint64_t seen_id;
static uint64_t seen_len;
static uint8_t seen_bytes[32];

int64_t simpleos_syscall(uint64_t id, uint64_t a0, uint64_t a1,
                         uint64_t a2, uint64_t a3, uint64_t a4) {
    (void)a3;
    (void)a4;
    seen_id = id;
    const uint8_t *input = NULL;
    seen_len = 0;
    if (id == 30 || id == 44) {
        input = (const uint8_t *)(uintptr_t)a0;
        seen_len = a1;
    } else if (id == 32 || id == 71 || id == 73 || id == 75) {
        input = (const uint8_t *)(uintptr_t)a1;
        seen_len = a2;
    }
    if (input && seen_len <= sizeof(seen_bytes)) {
        memcpy(seen_bytes, input, (size_t)seen_len);
    }
    if (id == 31 || id == 76) {
        uint8_t *out = (uint8_t *)(uintptr_t)a1;
        for (uint64_t i = 0; i < a2; ++i) out[i] = (uint8_t)(0xb0u + i);
        return (int64_t)a2;
    }
    return 7;
}

static SplArray *generic_bytes(const int64_t *values, int64_t length) {
    SplArray *array = rt_array_new(length);
    assert(array);
    for (int64_t i = 0; i < length; ++i) {
        assert(rt_array_push(array, rt_value_int(values[i])));
    }
    return array;
}

int main(void) {
    SplArray *packed = rt_byte_array_new_len(3);
    assert(packed);
    assert(rt_array_bytes_store_checked(
               (int64_t)(uintptr_t)packed, (const uint8_t *)"abc", 3) == 3);
    assert(rt_simpleos_file_open_bytes((int64_t)(uintptr_t)packed, 9) == 7);
    assert(seen_id == 30 && seen_len == 3 && memcmp(seen_bytes, "abc", 3) == 0);

    const int64_t generic_values[] = {1, 2, 255};
    SplArray *generic = generic_bytes(generic_values, 3);
    assert(rt_simpleos_file_write_bytes(4, (int64_t)(uintptr_t)generic) == 7);
    assert(seen_id == 32 && seen_len == 3 && seen_bytes[2] == 255);

    const int64_t invalid_values[] = {1, 256};
    SplArray *invalid = generic_bytes(invalid_values, 2);
    assert(rt_simpleos_socket_send_bytes(4, (int64_t)(uintptr_t)invalid) == -22);
    assert(rt_simpleos_socket_send_bytes(4, 17) == -22);

    SplArray *out = rt_byte_array_new_len(4);
    assert(out);
    assert(rt_simpleos_socket_recv_bytes(5, (int64_t)(uintptr_t)out, 4) == 4);
    uint8_t copied[4] = {0};
    assert(rt_array_bytes_copy_checked(
               (int64_t)(uintptr_t)out, copied, 4) == 4);
    assert(copied[0] == 0xb0 && copied[3] == 0xb3);
    assert(rt_simpleos_file_read_bytes(5, (int64_t)(uintptr_t)out, 5) == -22);
    return 0;
}
