#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

#define TAG_MASK    0x7ULL
#define TAG_INT     0x0ULL
#define TAG_HEAP    0x1ULL
#define TAG_SPECIAL 0x3ULL

#define ENCODE_INT(v)  ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define ENCODE_PTR(p)  ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)  ((void*)((uint64_t)(v) & ~TAG_MASK))
#define DECODE_INT(v)  ((int64_t)((uint64_t)(v) >> 3))
#define IS_INT(v)      (((uint64_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)     (((uint64_t)(v) & TAG_MASK) == TAG_HEAP)
#define NIL_VALUE      ((RuntimeValue)TAG_SPECIAL)

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader   hdr;
    uint32_t     len;
    uint32_t     cap;
    RuntimeValue items[];
} RuntimeArray;

#define HEAP_ARRAY 2

extern void *malloc(size_t size);

static inline uint8_t _rv_byte(RuntimeValue v)
{
    int64_t byte_val = IS_INT(v) ? DECODE_INT(v) : (int64_t)v;
    return (uint8_t)(byte_val & 0xFF);
}

int ring_core_0_17_14__CRYPTO_memcmp(const void *a, const void *b, size_t n)
{
    const uint8_t *pa = (const uint8_t *)a;
    const uint8_t *pb = (const uint8_t *)b;
    uint8_t diff = 0;
    for (size_t i = 0; i < n; i++) diff |= (uint8_t)(pa[i] ^ pb[i]);
    return diff;
}

#include "../../../../../src/compiler_rust/vendor/ring/crypto/curve25519/curve25519.c"

RuntimeValue rt_tls13_x25519_shared_secret(RuntimeValue scalar_rv, RuntimeValue point_rv)
{
    if (!IS_HEAP(scalar_rv) || !IS_HEAP(point_rv)) return NIL_VALUE;

    RuntimeArray *scalar = (RuntimeArray *)DECODE_PTR(scalar_rv);
    RuntimeArray *point = (RuntimeArray *)DECODE_PTR(point_rv);
    if (!scalar || !point || scalar->hdr.type != HEAP_ARRAY || point->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    if (scalar->len != 32 || point->len != 32) return NIL_VALUE;

    uint8_t scalar_raw[32];
    uint8_t point_raw[32];
    uint8_t out_raw[32];
    for (uint32_t i = 0; i < 32; i++) {
        scalar_raw[i] = _rv_byte(scalar->items[i]);
        point_raw[i] = _rv_byte(point->items[i]);
    }

    x25519_scalar_mult_generic_masked(out_raw, scalar_raw, point_raw);

    RuntimeArray *out = (RuntimeArray *)malloc(sizeof(RuntimeArray) + 32u * sizeof(RuntimeValue));
    if (!out) return NIL_VALUE;
    out->hdr.type = HEAP_ARRAY;
    out->hdr.size = (uint32_t)(sizeof(RuntimeArray) + 32u * sizeof(RuntimeValue));
    out->len = 32;
    out->cap = 32;
    for (uint32_t i = 0; i < 32; i++) out->items[i] = ENCODE_INT(out_raw[i]);
    return ENCODE_PTR(out);
}
