#include "runtime.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int rt_sha256_file_raw_v1(const char *path, uint8_t out[32]);
extern int64_t rt_file_read_bytes(const uint8_t *path, uint64_t length);

int main(int argc, char **argv) {
    const int64_t size = 109939334;
    const uint64_t byte_limit = UINT64_C(1073741824);
    const char *expected = "dc022e2afae05a4e4be06413ef8ef81a1b46a329da480f4ee8e2cf2d43d6093a";
    assert(argc == 2);
    /* These refusals must precede any large allocation. */
    assert(rt_array_new(100000001) == NULL);
    assert(rt_array_new_with_cap_u64(100000001) == NULL);
    assert(rt_byte_array_new(byte_limit + 1) == NULL);
    assert(rt_byte_array_new(UINT64_MAX) == NULL);
    uint8_t digest[32];
    char hex[65];
    assert(rt_sha256_file_raw_v1(argv[1], digest));
    for (int i = 0; i < 32; ++i) sprintf(hex + i * 2, "%02x", digest[i]);
    assert(strcmp(hex, expected) == 0);
    SplArray *archive = (SplArray *)(uintptr_t)rt_file_read_bytes(
        (const uint8_t *)argv[1], strlen(argv[1]));
    assert(archive != NULL && rt_array_len(archive) == size);
    /* Push must grow capacity without producing a subsequently invalid header. */
    assert(rt_array_push(archive, rt_value_int(0x5a)));
    assert(rt_array_len(archive) == size + 1);
    assert(rt_array_set_len_known(rt_array_header_ptr(archive), size));
    uint8_t *bytes = (uint8_t *)(uintptr_t)rt_array_data_ptr(archive);
    assert(bytes != NULL && memcmp(bytes, "!<arch>\n", 8) == 0);
    /* Cross the old element cap through real packed storage and copy. */
    uint8_t saved = bytes[100000000];
    bytes[100000000] = (uint8_t)(saved ^ 0xa5);
    SplArray *copy = rt_array_copy(archive);
    assert(copy != NULL && rt_array_len(copy) == size);
    uint8_t *copied = (uint8_t *)(uintptr_t)rt_array_data_ptr(copy);
    assert(memcmp(bytes, copied, (size_t)size) == 0);
    assert(copied[100000000] == (uint8_t)(saved ^ 0xa5));
    bytes[100000000] = saved;
    assert(copied[100000000] != bytes[100000000]);
    SplArray *joined = rt_array_concat(archive, copy);
    assert(joined != NULL && rt_array_len(joined) == size * 2);
    uint8_t *joined_bytes = (uint8_t *)(uintptr_t)rt_array_data_ptr(joined);
    assert(memcmp(joined_bytes, bytes, (size_t)size) == 0);
    assert(memcmp(joined_bytes + size, copied, (size_t)size) == 0);
    SplArray *ordinary = rt_array_new(4);
    assert(ordinary != NULL);
    /* Mixed output uses tagged slots and must retain the generic limit. */
    assert(rt_array_concat(archive, ordinary) == NULL);
    rt_array_free(ordinary);
    rt_array_free(joined);
    rt_array_free(copy);
    rt_array_free(archive);
    puts("packed-byte-capacity archive/copy/concat passed");
    return 0;
}
