#include "runtime_value.h"
#include <stdbool.h>
#include <math.h>

uint8_t rt_value_eq(RuntimeValue a, RuntimeValue b) {
    if (a == b) return 1;

    uint64_t tag_a = rv_tag(a);
    uint64_t tag_b = rv_tag(b);

    if (tag_a == TAG_INT && tag_b == TAG_INT)
        return rv_to_int(a) == rv_to_int(b) ? 1 : 0;
    if (tag_a == TAG_FLOAT && tag_b == TAG_FLOAT)
        return rv_to_float(a) == rv_to_float(b) ? 1 : 0;
    if (tag_a == TAG_SPECIAL && tag_b == TAG_SPECIAL)
        return 0; /* same raw bits already checked */

    if (tag_a == TAG_HEAP && tag_b == TAG_HEAP) {
        HeapHeader *ptr_a = (HeapHeader *)rv_as_heap_ptr(a);
        HeapHeader *ptr_b = (HeapHeader *)rv_as_heap_ptr(b);
        if (!ptr_a || !ptr_b) return 0;
        if ((uintptr_t)ptr_a < MIN_HEAP_ADDR || (uintptr_t)ptr_b < MIN_HEAP_ADDR) return 0;

        if (ptr_a->object_type == HEAP_TYPE_STRING && ptr_b->object_type == HEAP_TYPE_STRING) {
            RuntimeString *sa = (RuntimeString *)ptr_a;
            RuntimeString *sb = (RuntimeString *)ptr_b;
            if (sa->len != sb->len) return 0;
            const uint8_t *da = (const uint8_t *)(sa + 1);
            const uint8_t *db = (const uint8_t *)(sb + 1);
            return memcmp(da, db, (size_t)sa->len) == 0 ? 1 : 0;
        }

        if (ptr_a->object_type == HEAP_TYPE_ENUM && ptr_b->object_type == HEAP_TYPE_ENUM) {
            RuntimeEnum *ea = (RuntimeEnum *)ptr_a;
            RuntimeEnum *eb = (RuntimeEnum *)ptr_b;
            if (ea->discriminant != eb->discriminant) return 0;
            return rt_value_eq(ea->payload, eb->payload);
        }
    }

    return 0;
}

int64_t rt_value_compare(RuntimeValue a, RuntimeValue b) {
    if (a == b) return 0;

    uint64_t tag_a = rv_tag(a);
    uint64_t tag_b = rv_tag(b);

    /* Integer comparison */
    if (tag_a == TAG_INT && tag_b == TAG_INT) {
        int64_t ai = rv_to_int(a), bi = rv_to_int(b);
        return ai < bi ? -1 : (ai > bi ? 1 : 0);
    }

    /* Float comparison */
    if (tag_a == TAG_FLOAT && tag_b == TAG_FLOAT) {
        double af = rv_to_float(a), bf = rv_to_float(b);
        if (af < bf) return -1;
        if (af > bf) return 1;
        return 0;
    }

    /* String comparison (lexicographic) */
    if (tag_a == TAG_HEAP && tag_b == TAG_HEAP) {
        HeapHeader *ptr_a = (HeapHeader *)rv_as_heap_ptr(a);
        HeapHeader *ptr_b = (HeapHeader *)rv_as_heap_ptr(b);
        if (ptr_a && ptr_b &&
            (uintptr_t)ptr_a >= MIN_HEAP_ADDR && (uintptr_t)ptr_b >= MIN_HEAP_ADDR &&
            ptr_a->object_type == HEAP_TYPE_STRING && ptr_b->object_type == HEAP_TYPE_STRING) {
            RuntimeString *sa = (RuntimeString *)ptr_a;
            RuntimeString *sb = (RuntimeString *)ptr_b;
            const uint8_t *da = (const uint8_t *)(sa + 1);
            const uint8_t *db = (const uint8_t *)(sb + 1);
            uint64_t min_len = sa->len < sb->len ? sa->len : sb->len;
            int cmp = memcmp(da, db, (size_t)min_len);
            if (cmp != 0) return cmp < 0 ? -1 : 1;
            if (sa->len < sb->len) return -1;
            if (sa->len > sb->len) return 1;
            return 0;
        }
    }

    /* Mixed int/float comparison */
    if (tag_a == TAG_INT && tag_b == TAG_FLOAT) {
        double bf = rv_to_float(b);
        if (fpclassify(bf) == FP_SUBNORMAL) goto raw_fallback;
        double af = (double)rv_to_int(a);
        return af < bf ? -1 : (af > bf ? 1 : 0);
    }
    if (tag_a == TAG_FLOAT && tag_b == TAG_INT) {
        double af = rv_to_float(a);
        if (fpclassify(af) == FP_SUBNORMAL) goto raw_fallback;
        double bf = (double)rv_to_int(b);
        return af < bf ? -1 : (af > bf ? 1 : 0);
    }

    /* Bool comparison */
    if (tag_a == TAG_SPECIAL && tag_b == TAG_SPECIAL) {
        uint64_t pa = rv_payload(a), pb = rv_payload(b);
        return pa < pb ? -1 : (pa > pb ? 1 : 0);
    }

raw_fallback:;
    int64_t ra = (int64_t)a, rb = (int64_t)b;
    return ra < rb ? -1 : (ra > rb ? 1 : 0);
}

int64_t rt_native_eq(int64_t a, int64_t b) {
    if (a == b) return 1;

    uint64_t au = (uint64_t)a;
    uint64_t bu = (uint64_t)b;
    if ((au & 7) == TAG_HEAP && (bu & 7) == TAG_HEAP) {
        uintptr_t ptr_a = (uintptr_t)(au & ~(uint64_t)7);
        uintptr_t ptr_b = (uintptr_t)(bu & ~(uint64_t)7);
        if (ptr_a >= MIN_HEAP_ADDR && ptr_b >= MIN_HEAP_ADDR) {
            return (int64_t)rt_value_eq((RuntimeValue)au, (RuntimeValue)bu);
        }
    }
    return 0;
}

int64_t rt_native_neq(int64_t a, int64_t b) {
    return rt_native_eq(a, b) == 1 ? 0 : 1;
}
