#include <stdint.h>
#include <stddef.h>

typedef long long spl_i64;

#define X86_TAG_MASK 0x7ULL
#define X86_TAG_INT 0x0ULL
#define X86_TAG_HEAP 0x1ULL
#define X86_HEAP_ARRAY 2

typedef struct {
    uint32_t type;
    uint32_t size;
} X86HeapHeader;

typedef struct {
    X86HeapHeader hdr;
    uint64_t len;
    uint64_t cap;
    spl_i64 *items;
} X86RuntimeArray;

extern void *malloc(size_t size);

static inline spl_i64 *x86_runtime_array_inline_items(X86RuntimeArray *a)
{
    return (spl_i64 *)((uint8_t *)a + sizeof(X86RuntimeArray));
}

static inline spl_i64 *x86_runtime_array_items(X86RuntimeArray *a)
{
    return a && a->items ? a->items : x86_runtime_array_inline_items(a);
}

static spl_i64 x86_aes_helper_byte_array_new_len(spl_i64 encoded_len)
{
    uint64_t len = ((uint64_t)encoded_len) >> 3;
    size_t bytes = sizeof(X86RuntimeArray) + (size_t)len * sizeof(spl_i64);
    X86RuntimeArray *a = (X86RuntimeArray *)malloc(bytes);
    if (!a) return 0x3;
    a->hdr.type = X86_HEAP_ARRAY;
    a->hdr.size = (uint32_t)bytes;
    a->len = len;
    a->cap = len;
    a->items = x86_runtime_array_inline_items(a);
    for (uint64_t i = 0; i < len; i++) a->items[i] = 0;
    return (spl_i64)((uint64_t)(uintptr_t)a | X86_TAG_HEAP);
}

static spl_i64 x86_aes_helper_array_data_ptr(spl_i64 array_value)
{
    if ((((uint64_t)array_value) & X86_TAG_MASK) != X86_TAG_HEAP) return 0;
    X86RuntimeArray *a = (X86RuntimeArray *)((uint64_t)array_value & ~X86_TAG_MASK);
    if (!a || a->hdr.type != X86_HEAP_ARRAY) return 0;
    return (spl_i64)(uintptr_t)x86_runtime_array_items(a);
}

static spl_i64 x86_aes_helper_array_get(spl_i64 array_value, spl_i64 encoded_index)
{
    if ((((uint64_t)array_value) & X86_TAG_MASK) != X86_TAG_HEAP) return 0x3;
    X86RuntimeArray *a = (X86RuntimeArray *)((uint64_t)array_value & ~X86_TAG_MASK);
    uint64_t index = ((uint64_t)encoded_index) >> 3;
    if (!a || a->hdr.type != X86_HEAP_ARRAY || index >= a->len) return 0x3;
    return x86_runtime_array_items(a)[index];
}

#define rt_byte_array_new_len x86_aes_helper_byte_array_new_len
#define rt_array_data_ptr x86_aes_helper_array_data_ptr
#define rt_array_get x86_aes_helper_array_get

#include "../../riscv64/boot/tls13_aes256_gcm_helper.c"
