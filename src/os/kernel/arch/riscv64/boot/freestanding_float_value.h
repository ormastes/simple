#ifndef SIMPLE_RV64_FREESTANDING_FLOAT_VALUE_H
#define SIMPLE_RV64_FREESTANDING_FLOAT_VALUE_H

typedef struct RtFloat {
    spl_u32 kind;
    spl_u32 reserved;
    double value;
} RtFloat;

static spl_i64 rt_float_box_value(double value, void *(*allocator)(spl_i64)) {
    RtFloat *boxed = (RtFloat *)allocator((spl_i64)sizeof(RtFloat));
    if (boxed) {
        boxed->kind = RT_VALUE_HEAP_FLOAT;
        boxed->reserved = 0;
        boxed->value = value;
        return (spl_i64)(((spl_u64)boxed) | RT_VALUE_TAG_HEAP);
    }
    union {
        double value;
        spl_u64 bits;
    } inline_box;
    inline_box.value = value;
    return (spl_i64)((inline_box.bits & ~RT_VALUE_TAG_MASK) | 0x2ULL);
}

static double rt_float_unbox_value(spl_i64 value) {
    union {
        spl_u64 bits;
        double value;
    } inline_box;
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        RtFloat *boxed = (RtFloat *)((spl_u64)value & ~RT_VALUE_TAG_MASK);
        if (boxed && boxed->kind == RT_VALUE_HEAP_FLOAT) {
            return boxed->value;
        }
    }
    inline_box.bits = (spl_u64)value & ~RT_VALUE_TAG_MASK;
    return inline_box.value;
}

#endif
