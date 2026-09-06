#include <assert.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t RuntimeValue;
typedef struct {
    uint32_t type;
    uint32_t size;
    uint64_t len;
    uint64_t cap;
    RuntimeValue *items;
} RuntimeArray;

static uint32_t len_u32(RuntimeArray *array)
{
    return (uint32_t)array->len;
}

static int32_t len_i32_raw(RuntimeArray *array)
{
    uint64_t len = (uint64_t)len_u32(array);
    return len > 0x7fffffffULL ? 0x7fffffff : (int32_t)len;
}

static int finds_sys(const uint8_t *data, int32_t len)
{
    for (int32_t offset = 0; offset + 32 <= len; offset += 32) {
        if (data[offset] == 'S' && data[offset + 1] == 'Y' && data[offset + 2] == 'S') {
            return 1;
        }
    }
    return 0;
}

int main(void)
{
    RuntimeArray cluster = {2, 0, 1024, 65536, 0};
    uint8_t data[1024];
    memset(data, 0xe5, sizeof(data));
    memcpy(data + 512, "SYS        ", 11);
    assert(len_i32_raw(&cluster) == 1024);
    assert(!finds_sys(data, (int32_t)(cluster.len >> 3)));
    assert(finds_sys(data, len_i32_raw(&cluster)));
    return 0;
}
