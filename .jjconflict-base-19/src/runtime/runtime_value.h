#ifndef RUNTIME_VALUE_H
#define RUNTIME_VALUE_H

#include <stdint.h>
#include <string.h>

typedef uint64_t RuntimeValue;

#define TAG_MASK    0x7ULL
#define TAG_INT     0x0ULL
#define TAG_HEAP    0x1ULL
#define TAG_FLOAT   0x2ULL
#define TAG_SPECIAL 0x3ULL

#define SPECIAL_NIL   0ULL
#define SPECIAL_TRUE  1ULL
#define SPECIAL_FALSE 2ULL
#define SPECIAL_ERROR 3ULL

#define RT_NIL   ((SPECIAL_NIL   << 3) | TAG_SPECIAL)
#define RT_TRUE  ((SPECIAL_TRUE  << 3) | TAG_SPECIAL)
#define RT_FALSE ((SPECIAL_FALSE << 3) | TAG_SPECIAL)
#define RT_ERROR ((SPECIAL_ERROR << 3) | TAG_SPECIAL)

static inline uint64_t rv_tag(RuntimeValue v) { return v & TAG_MASK; }
static inline uint64_t rv_payload(RuntimeValue v) { return v >> 3; }
static inline RuntimeValue rv_from_tag_payload(uint64_t tag, uint64_t payload) {
    return (payload << 3) | tag;
}

static inline RuntimeValue rv_from_int(int64_t i) { return (uint64_t)i << 3; }
static inline int64_t rv_to_int(RuntimeValue v) { return (int64_t)v >> 3; }

static inline RuntimeValue rv_from_float(double f) {
    uint64_t bits;
    memcpy(&bits, &f, sizeof(double));
    return rv_from_tag_payload(TAG_FLOAT, bits >> 3);
}
static inline double rv_to_float(RuntimeValue v) {
    uint64_t bits = rv_payload(v) << 3;
    double f;
    memcpy(&f, &bits, sizeof(double));
    return f;
}

static inline RuntimeValue rv_from_bool(int b) { return b ? RT_TRUE : RT_FALSE; }
static inline int rv_to_bool(RuntimeValue v) {
    return rv_tag(v) == TAG_SPECIAL && rv_payload(v) == SPECIAL_TRUE;
}

static inline int rv_is_int(RuntimeValue v) { return rv_tag(v) == TAG_INT; }
static inline int rv_is_float(RuntimeValue v) { return rv_tag(v) == TAG_FLOAT; }
static inline int rv_is_heap(RuntimeValue v) { return rv_tag(v) == TAG_HEAP; }
static inline int rv_is_nil(RuntimeValue v) { return v == RT_NIL; }
static inline int rv_is_bool(RuntimeValue v) {
    return rv_tag(v) == TAG_SPECIAL &&
           (rv_payload(v) == SPECIAL_TRUE || rv_payload(v) == SPECIAL_FALSE);
}
static inline int rv_is_error(RuntimeValue v) {
    return rv_tag(v) == TAG_SPECIAL && rv_payload(v) == SPECIAL_ERROR;
}

/* Heap object type tags (matches HeapObjectType repr(u8)) */
#define HEAP_TYPE_STRING  0x01
#define HEAP_TYPE_ARRAY   0x02
#define HEAP_TYPE_DICT    0x03
#define HEAP_TYPE_ENUM    0x07

/* HeapHeader: #[repr(C)] — 8 bytes */
typedef struct {
    uint8_t  object_type;
    uint8_t  gc_flags;
    uint16_t reserved;
    uint32_t size;
} HeapHeader;

/* RuntimeString: HeapHeader + len + hash + inline UTF-8 bytes */
typedef struct {
    HeapHeader header;
    uint64_t len;
    uint64_t hash;
    /* uint8_t data[] follows */
} RuntimeString;

/* RuntimeEnum: HeapHeader + enum_id + discriminant + payload */
typedef struct {
    HeapHeader header;
    uint32_t enum_id;
    uint32_t discriminant;
    RuntimeValue payload;
} RuntimeEnum;

/* Extract heap pointer from a RuntimeValue (strips tag bits) */
static inline void *rv_as_heap_ptr(RuntimeValue v) {
    return (void *)(v & ~(uint64_t)TAG_MASK);
}

#define MIN_HEAP_ADDR 0x100000

#endif
