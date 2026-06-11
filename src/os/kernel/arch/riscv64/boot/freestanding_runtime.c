/* RISC-V freestanding runtime bridge.
 *
 * This file is compiled as a boot object by native-build for the RV64 entry.
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;
typedef unsigned int spl_u32;
typedef unsigned short spl_u16;
typedef unsigned char spl_u8;

#define RT_VALUE_TAG_MASK 0x7ULL
#define RT_VALUE_TAG_INT 0x0ULL
#define RT_VALUE_TAG_HEAP 0x1ULL
#define RT_VALUE_TAG_SPECIAL 0x3ULL
#define RT_VALUE_SPECIAL_NIL 0x0ULL
#define RT_VALUE_SPECIAL_TRUE 0x1ULL
#define RT_VALUE_SPECIAL_FALSE 0x2ULL
#define RT_HEAP_STRING 0x01U
#define RT_HEAP_ARRAY 0x02U
#define RT_HEAP_TUPLE 0x04U
#define RT_HEAP_ENUM 0x07U

typedef struct RtHeapHeader {
    spl_u8 object_type;
    spl_u8 gc_flags;
    unsigned short reserved;
    spl_u32 size;
} RtHeapHeader;

typedef struct RtString {
    RtHeapHeader header;
    spl_u64 len;
    spl_u64 hash;
    char data[];
} RtString;

typedef struct RtArray {
    RtHeapHeader header;
    spl_u64 len;
    spl_u64 capacity;
    spl_i64 *data;
} RtArray;

typedef struct RtTuple {
    RtHeapHeader header;
    spl_u64 len;
    spl_i64 data[];
} RtTuple;

typedef struct RtEnum {
    RtHeapHeader header;
    spl_u32 enum_id;
    spl_u32 discriminant;
    spl_i64 payload;
} RtEnum;

__asm__(
    ".section .text.entry,\"ax\",@progbits\n"
    ".globl _start\n"
    "_start:\n"
    "j spl_start\n"
);

extern spl_i64 kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(spl_i64 size) __attribute__((weak));

static spl_u64 g_freestanding_heap_next = 0x87000000ULL;
static spl_u64 g_freestanding_heap_limit = 0x88000000ULL;

static spl_u64 rt_align8(spl_u64 value) {
    return (value + 7ULL) & ~7ULL;
}

void *rt_alloc(spl_i64 size) {
    spl_u64 next;
    spl_u64 bytes;
    void *boot_alloc;
    if (size <= 0) {
        return (void *)0;
    }
    if (kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc) {
        boot_alloc = (void *)(spl_u64)kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(size);
        if (boot_alloc) {
            return boot_alloc;
        }
    }
    bytes = rt_align8((spl_u64)size);
    next = rt_align8(g_freestanding_heap_next);
    if (next + bytes > g_freestanding_heap_limit) {
        return (void *)0;
    }
    g_freestanding_heap_next = next + bytes;
    return (void *)next;
}

void rt_free(void *ptr) {
    (void)ptr;
}

void *rt_memcpy(void *dst, const void *src, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = s[i];
    }
    return dst;
}

void *rt_memset(void *dst, signed char val, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = (unsigned char)val;
    }
    return dst;
}

static spl_i64 rt_special(spl_u64 payload) {
    return (spl_i64)((payload << 3) | RT_VALUE_TAG_SPECIAL);
}

static spl_i64 rt_int(spl_i64 value) {
    return value << 3;
}

static spl_i64 rt_nil(void) {
    return rt_special(RT_VALUE_SPECIAL_NIL);
}

static spl_i64 rt_heap(void *ptr) {
    if (!ptr) {
        return rt_nil();
    }
    return (spl_i64)(((spl_u64)ptr) | RT_VALUE_TAG_HEAP);
}

static RtHeapHeader *rt_as_heap(spl_i64 value, spl_u8 kind) {
    spl_u64 raw = (spl_u64)value;
    RtHeapHeader *header;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) {
        return (RtHeapHeader *)0;
    }
    header = (RtHeapHeader *)(raw & ~RT_VALUE_TAG_MASK);
    if (!header || header->object_type != kind) {
        return (RtHeapHeader *)0;
    }
    return header;
}

static RtString *rt_as_string(spl_i64 value) {
    return (RtString *)rt_as_heap(value, RT_HEAP_STRING);
}

static RtArray *rt_as_array(spl_i64 value) {
    return (RtArray *)rt_as_heap(value, RT_HEAP_ARRAY);
}

static RtTuple *rt_as_tuple(spl_i64 value) {
    return (RtTuple *)rt_as_heap(value, RT_HEAP_TUPLE);
}

static RtEnum *rt_as_enum(spl_i64 value) {
    return (RtEnum *)rt_as_heap(value, RT_HEAP_ENUM);
}

static spl_i64 rt_index_arg(spl_i64 value) {
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
        return value >> 3;
    }
    return value;
}

static void rt_write_decimal(char *buf, spl_u64 *len, spl_u64 value) {
    char tmp[20];
    spl_u64 count = 0;
    if (value == 0) {
        buf[0] = '0';
        *len = 1;
        return;
    }
    while (value > 0) {
        tmp[count] = (char)('0' + (value % 10));
        value = value / 10;
        count = count + 1;
    }
    *len = count;
    for (spl_u64 i = 0; i < count; i = i + 1) {
        buf[i] = tmp[count - 1 - i];
    }
}

spl_i64 rt_string_new(spl_i64 bytes_value, spl_i64 len_value) {
    const spl_u8 *bytes = (const spl_u8 *)(spl_u64)bytes_value;
    spl_u64 len = len_value < 0 ? 0 : (spl_u64)len_value;
    RtString *out = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + len + 1));
    if (!out) {
        return rt_nil();
    }
    out->header.object_type = RT_HEAP_STRING;
    out->header.gc_flags = 0;
    out->header.reserved = 0;
    out->header.size = (spl_u32)(sizeof(RtString) + len);
    out->len = len;
    out->hash = 0;
    for (spl_u64 i = 0; i < len; i = i + 1) {
        out->data[i] = bytes ? (char)bytes[i] : 0;
    }
    out->data[len] = 0;
    return rt_heap(out);
}

spl_i64 rt_raw_u64_to_string(spl_i64 raw) {
    char buf[20];
    spl_u64 len = 0;
    rt_write_decimal(buf, &len, (spl_u64)raw);
    return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)len);
}

spl_i64 rt_to_string(spl_i64 value) {
    char buf[21];
    spl_u64 len = 0;
    spl_i64 signed_value;
    if (rt_as_string(value)) {
        return value;
    }
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
        signed_value = value >> 3;
        if (signed_value < 0) {
            buf[0] = '-';
            rt_write_decimal(buf + 1, &len, (spl_u64)(-signed_value));
            return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)(len + 1));
        }
        rt_write_decimal(buf, &len, (spl_u64)signed_value);
        return rt_string_new((spl_i64)(spl_u64)buf, (spl_i64)len);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) {
        return rt_string_new((spl_i64)(spl_u64)"true", 4);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) {
        return rt_string_new((spl_i64)(spl_u64)"false", 5);
    }
    if (value == rt_nil()) {
        return rt_string_new((spl_i64)(spl_u64)"nil", 3);
    }
    return rt_string_new((spl_i64)(spl_u64)"<value>", 7);
}

spl_i64 rt_value_to_string(spl_i64 value) {
    return rt_to_string(value);
}

spl_i64 rt_string_concat(spl_i64 left, spl_i64 right) {
    RtString *a;
    RtString *b;
    RtString *out;
    spl_i64 left_text = rt_to_string(left);
    spl_i64 right_text = rt_to_string(right);
    a = rt_as_string(left_text);
    b = rt_as_string(right_text);
    if (!a || !b) {
        return rt_nil();
    }
    out = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + a->len + b->len + 1));
    if (!out) {
        return rt_nil();
    }
    out->header.object_type = RT_HEAP_STRING;
    out->header.gc_flags = 0;
    out->header.reserved = 0;
    out->header.size = (spl_u32)(sizeof(RtString) + a->len + b->len);
    out->len = a->len + b->len;
    out->hash = 0;
    for (spl_u64 i = 0; i < a->len; i = i + 1) {
        out->data[i] = a->data[i];
    }
    for (spl_u64 i = 0; i < b->len; i = i + 1) {
        out->data[a->len + i] = b->data[i];
    }
    out->data[out->len] = 0;
    return rt_heap(out);
}

spl_i64 rt_len(spl_i64 value) {
    RtString *s = rt_as_string(value);
    RtArray *a;
    RtTuple *t;
    if (s) {
        return (spl_i64)s->len;
    }
    a = rt_as_array(value);
    if (a) {
        return (spl_i64)a->len;
    }
    t = rt_as_tuple(value);
    if (t) {
        return (spl_i64)t->len;
    }
    return 0;
}

spl_i64 rt_array_new(spl_i64 capacity_value) {
    spl_u64 capacity = capacity_value <= 4 ? 4 : (spl_u64)capacity_value;
    RtArray *array = (RtArray *)rt_alloc((spl_i64)sizeof(RtArray));
    if (!array) {
        return rt_nil();
    }
    array->data = (spl_i64 *)rt_alloc((spl_i64)(capacity * sizeof(spl_i64)));
    if (!array->data) {
        return rt_nil();
    }
    array->header.object_type = RT_HEAP_ARRAY;
    array->header.gc_flags = 0;
    array->header.reserved = 0;
    array->header.size = (spl_u32)sizeof(RtArray);
    array->len = 0;
    array->capacity = capacity;
    for (spl_u64 i = 0; i < capacity; i = i + 1) {
        array->data[i] = rt_nil();
    }
    return rt_heap(array);
}

spl_i64 rt_array_len(spl_i64 array_value) {
    RtArray *array = rt_as_array(array_value);
    return array ? (spl_i64)array->len : -1;
}

spl_i64 rt_array_new_with_cap_u64(spl_i64 capacity_value) {
    return rt_array_new(capacity_value);
}

spl_i64 rt_array_push(spl_i64 array_value, spl_i64 value) {
    RtArray *array = rt_as_array(array_value);
    spl_i64 *new_data;
    spl_u64 new_capacity;
    if (!array) {
        return 0;
    }
    if (array->len >= array->capacity) {
        new_capacity = array->capacity < 4 ? 4 : array->capacity * 2;
        new_data = (spl_i64 *)rt_alloc((spl_i64)(new_capacity * sizeof(spl_i64)));
        if (!new_data) {
            return 0;
        }
        for (spl_u64 i = 0; i < array->len; i = i + 1) {
            new_data[i] = array->data[i];
        }
        for (spl_u64 i = array->len; i < new_capacity; i = i + 1) {
            new_data[i] = rt_nil();
        }
        array->data = new_data;
        array->capacity = new_capacity;
    }
    array->data[array->len] = value;
    array->len = array->len + 1;
    return 1;
}

spl_i64 rt_index_get(spl_i64 collection, spl_i64 index_value) {
    RtArray *array = rt_as_array(collection);
    RtTuple *tuple;
    RtString *string;
    spl_i64 index = rt_index_arg(index_value);
    if (array) {
        if (index < 0) {
            index = (spl_i64)array->len + index;
        }
        if (index < 0 || (spl_u64)index >= array->len) {
            return rt_nil();
        }
        return array->data[index];
    }
    tuple = rt_as_tuple(collection);
    if (tuple) {
        if (index < 0) {
            index = (spl_i64)tuple->len + index;
        }
        if (index < 0 || (spl_u64)index >= tuple->len) {
            return rt_nil();
        }
        return tuple->data[index];
    }
    string = rt_as_string(collection);
    if (string) {
        if (index < 0) {
            index = (spl_i64)string->len + index;
        }
        if (index < 0 || (spl_u64)index >= string->len) {
            return rt_nil();
        }
        return rt_string_new((spl_i64)(spl_u64)&string->data[index], 1);
    }
    return rt_nil();
}

spl_i64 rt_index_set(spl_i64 collection, spl_i64 index_value, spl_i64 value) {
    RtArray *array = rt_as_array(collection);
    spl_i64 index = rt_index_arg(index_value);
    if (!array) {
        return 0;
    }
    if (index < 0) {
        index = (spl_i64)array->len + index;
    }
    if (index < 0 || (spl_u64)index >= array->len) {
        return 0;
    }
    array->data[index] = value;
    return 1;
}

spl_i64 rt_typed_words_u64_set(spl_i64 collection, spl_i64 index_value, spl_i64 value) {
    return rt_index_set(collection, index_value, value);
}

spl_i64 rt_typed_bytes_u8_push(spl_i64 collection, spl_i64 value) {
    return rt_array_push(collection, value & 0xffLL);
}

spl_i64 rt_push_byte(spl_i64 collection, spl_i64 value) {
    rt_array_push(collection, value & 0xffLL);
    return collection;
}

spl_i64 rt_typed_words_u32_push(spl_i64 collection, spl_i64 value) {
    return rt_array_push(collection, value & 0xffffffffLL);
}

spl_i64 rt_typed_words_u64_push(spl_i64 collection, spl_i64 value) {
    return rt_array_push(collection, value);
}

spl_i64 rt_slice(spl_i64 value, spl_i64 start_value, spl_i64 end_value, spl_i64 step_value) {
    RtString *string = rt_as_string(value);
    spl_i64 start = rt_index_arg(start_value);
    spl_i64 end = rt_index_arg(end_value);
    spl_i64 step = rt_index_arg(step_value);
    if (!string) {
        return rt_nil();
    }
    if (step == 0) {
        step = 1;
    }
    if (start < 0) {
        start = (spl_i64)string->len + start;
    }
    if (end < 0) {
        end = (spl_i64)string->len + end;
    }
    if (start < 0) {
        start = 0;
    }
    if (end < start) {
        end = start;
    }
    if ((spl_u64)end > string->len) {
        end = (spl_i64)string->len;
    }
    if (step != 1) {
        return rt_string_new((spl_i64)(spl_u64)"", 0);
    }
    return rt_string_new((spl_i64)(spl_u64)&string->data[start], end - start);
}

spl_i64 rt_array_repeat(spl_i64 value, spl_i64 count_value) {
    spl_i64 count = rt_index_arg(count_value);
    spl_i64 array;
    if (count <= 0) {
        return rt_array_new(0);
    }
    array = rt_array_new(count);
    for (spl_i64 i = 0; i < count; i = i + 1) {
        rt_array_push(array, value);
    }
    return array;
}

spl_i64 rt_tuple_new(spl_i64 len_value) {
    spl_u64 len = len_value < 0 ? 0 : (spl_u64)len_value;
    RtTuple *tuple = (RtTuple *)rt_alloc((spl_i64)(sizeof(RtTuple) + len * sizeof(spl_i64)));
    if (!tuple) {
        return rt_nil();
    }
    tuple->header.object_type = RT_HEAP_TUPLE;
    tuple->header.gc_flags = 0;
    tuple->header.reserved = 0;
    tuple->header.size = (spl_u32)(sizeof(RtTuple) + len * sizeof(spl_i64));
    tuple->len = len;
    for (spl_u64 i = 0; i < len; i = i + 1) {
        tuple->data[i] = rt_nil();
    }
    return rt_heap(tuple);
}

spl_i64 rt_tuple_get(spl_i64 tuple_value, spl_i64 index_value) {
    RtTuple *tuple = rt_as_tuple(tuple_value);
    spl_i64 index = rt_index_arg(index_value);
    if (!tuple || index < 0 || (spl_u64)index >= tuple->len) {
        return rt_nil();
    }
    return tuple->data[index];
}

spl_i64 rt_tuple_set(spl_i64 tuple_value, spl_i64 index_value, spl_i64 value) {
    RtTuple *tuple = rt_as_tuple(tuple_value);
    spl_i64 index = rt_index_arg(index_value);
    if (!tuple || index < 0 || (spl_u64)index >= tuple->len) {
        return 0;
    }
    tuple->data[index] = value;
    return 1;
}

spl_i64 rt_enum_new(spl_u32 enum_id, spl_u32 discriminant, spl_i64 payload) {
    RtEnum *value = (RtEnum *)rt_alloc((spl_i64)sizeof(RtEnum));
    if (!value) {
        return rt_nil();
    }
    value->header.object_type = RT_HEAP_ENUM;
    value->header.gc_flags = 0;
    value->header.reserved = 0;
    value->header.size = (spl_u32)sizeof(RtEnum);
    value->enum_id = enum_id;
    value->discriminant = discriminant;
    value->payload = payload;
    return rt_heap(value);
}

spl_i64 rt_enum_payload(spl_i64 value) {
    RtEnum *enum_value = rt_as_enum(value);
    return enum_value ? enum_value->payload : rt_nil();
}

spl_i64 rt_enum_check_discriminant(spl_i64 value, spl_i64 expected) {
    RtEnum *enum_value = rt_as_enum(value);
    return enum_value && enum_value->discriminant == (spl_u32)expected ? 1 : 0;
}

spl_i64 common__config_env__ConfigEnv_dot_len(spl_i64 value) {
    (void)value;
    return 0;
}

spl_i64 rt_native_eq(spl_i64 lhs, spl_i64 rhs) {
    RtString *a = rt_as_string(lhs);
    RtString *b = rt_as_string(rhs);
    if (a || b) {
        if (!a || !b || a->len != b->len) {
            return 0;
        }
        for (spl_u64 i = 0; i < a->len; i = i + 1) {
            if (a->data[i] != b->data[i]) {
                return 0;
            }
        }
        return 1;
    }
    return lhs == rhs ? 1 : 0;
}

spl_i64 rt_string_eq(spl_i64 lhs, spl_i64 rhs) {
    RtString *a = rt_as_string(lhs);
    RtString *b = rt_as_string(rhs);
    if (!a || !b || a->len != b->len) {
        return 0;
    }
    for (spl_u64 i = 0; i < a->len; i = i + 1) {
        if (a->data[i] != b->data[i]) {
            return 0;
        }
    }
    return 1;
}

spl_i64 rt_string_char_code_at(spl_i64 value, spl_i64 index_value) {
    RtString *string = rt_as_string(value);
    spl_i64 index = rt_index_arg(index_value);
    if (!string) {
        return -1;
    }
    if (index < 0) {
        index = (spl_i64)string->len + index;
    }
    if (index < 0 || (spl_u64)index >= string->len) {
        return -1;
    }
    return (spl_i64)(spl_u8)string->data[index];
}

spl_i64 rt_string_starts_with(spl_i64 value, spl_i64 prefix_value) {
    RtString *string = rt_as_string(value);
    RtString *prefix = rt_as_string(prefix_value);
    if (!string || !prefix) {
        return 0;
    }
    if (prefix->len > string->len) {
        return 0;
    }
    for (spl_u64 i = 0; i < prefix->len; i = i + 1) {
        if (string->data[i] != prefix->data[i]) {
            return 0;
        }
    }
    return 1;
}

spl_i64 rt_string_trim(spl_i64 value) {
    RtString *string = rt_as_string(value);
    spl_u64 start = 0;
    spl_u64 end;
    if (!string) {
        return rt_nil();
    }
    end = string->len;
    while (start < end) {
        spl_u8 ch = (spl_u8)string->data[start];
        if (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') {
            start = start + 1;
        } else {
            break;
        }
    }
    while (end > start) {
        spl_u8 ch = (spl_u8)string->data[end - 1];
        if (ch == ' ' || ch == '\n' || ch == '\r' || ch == '\t') {
            end = end - 1;
        } else {
            break;
        }
    }
    return rt_string_new((spl_i64)(spl_u64)&string->data[start], (spl_i64)(end - start));
}

spl_i64 rt_string_ends_with(spl_i64 value, spl_i64 suffix_value) {
    RtString *string = rt_as_string(value);
    RtString *suffix = rt_as_string(suffix_value);
    if (!string || !suffix) {
        return 0;
    }
    if (suffix->len > string->len) {
        return 0;
    }
    for (spl_u64 i = 0; i < suffix->len; i = i + 1) {
        if (string->data[string->len - suffix->len + i] != suffix->data[i]) {
            return 0;
        }
    }
    return 1;
}

spl_i64 rt_string_split(spl_i64 value, spl_i64 sep_value) {
    RtString *string = rt_as_string(value);
    RtString *sep = rt_as_string(sep_value);
    spl_i64 out = rt_array_new(4);
    spl_u64 start = 0;
    if (!string || !sep) {
        return out;
    }
    if (sep->len == 0) {
        rt_array_push(out, value);
        return out;
    }
    while (start <= string->len) {
        spl_u64 match_at = string->len;
        for (spl_u64 i = start; i + sep->len <= string->len; i = i + 1) {
            spl_i64 matched = 1;
            for (spl_u64 j = 0; j < sep->len; j = j + 1) {
                if (string->data[i + j] != sep->data[j]) {
                    matched = 0;
                    break;
                }
            }
            if (matched) {
                match_at = i;
                break;
            }
        }
        if (match_at == string->len) {
            rt_array_push(out, rt_string_new((spl_i64)(spl_u64)&string->data[start], (spl_i64)(string->len - start)));
            break;
        }
        rt_array_push(out, rt_string_new((spl_i64)(spl_u64)&string->data[start], (spl_i64)(match_at - start)));
        start = match_at + sep->len;
        if (start == string->len) {
            rt_array_push(out, rt_string_new((spl_i64)(spl_u64)"", 0));
            break;
        }
    }
    return out;
}

spl_i64 rt_string_from_byte_array(spl_i64 array_value) {
    RtArray *array = rt_as_array(array_value);
    RtString *out;
    if (!array) {
        return rt_string_new((spl_i64)(spl_u64)"", 0);
    }
    out = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + array->len + 1));
    if (!out) {
        return rt_nil();
    }
    out->header.object_type = RT_HEAP_STRING;
    out->header.gc_flags = 0;
    out->header.reserved = 0;
    out->header.size = (spl_u32)(sizeof(RtString) + array->len);
    out->len = array->len;
    out->hash = 0;
    for (spl_u64 i = 0; i < array->len; i = i + 1) {
        out->data[i] = (char)(rt_index_arg(array->data[i]) & 0xff);
    }
    out->data[array->len] = 0;
    return rt_heap(out);
}

spl_i64 rt_bytes_slice(spl_i64 array_value, spl_i64 start_value, spl_i64 len_value) {
    RtArray *array = rt_as_array(array_value);
    spl_i64 start = rt_index_arg(start_value);
    spl_i64 len = rt_index_arg(len_value);
    spl_i64 out;
    if (!array || len <= 0) {
        return rt_array_new(0);
    }
    if (start < 0) {
        start = (spl_i64)array->len + start;
    }
    if (start < 0) {
        start = 0;
    }
    if ((spl_u64)start >= array->len) {
        return rt_array_new(0);
    }
    if ((spl_u64)(start + len) > array->len) {
        len = (spl_i64)array->len - start;
    }
    out = rt_array_new(len);
    for (spl_i64 i = 0; i < len; i = i + 1) {
        rt_array_push(out, array->data[start + i]);
    }
    return out;
}

spl_i64 rt_bytes_concat(spl_i64 left_value, spl_i64 right_value) {
    RtArray *left = rt_as_array(left_value);
    RtArray *right = rt_as_array(right_value);
    spl_i64 out;
    if (!left || !right) {
        return rt_array_new(0);
    }
    out = rt_array_new((spl_i64)(left->len + right->len));
    for (spl_u64 i = 0; i < left->len; i = i + 1) {
        rt_array_push(out, left->data[i]);
    }
    for (spl_u64 i = 0; i < right->len; i = i + 1) {
        rt_array_push(out, right->data[i]);
    }
    return out;
}

spl_i64 rt_for_iterable(spl_i64 collection) {
    return collection;
}

spl_i64 rt_native_neq(spl_i64 lhs, spl_i64 rhs) {
    return rt_native_eq(lhs, rhs) ? 0 : 1;
}

spl_i64 rt_any_add(spl_i64 lhs, spl_i64 rhs) {
    if (rt_as_string(lhs) || rt_as_string(rhs)) {
        return rt_string_concat(lhs, rhs);
    }
    return lhs + rhs;
}

spl_i64 rt_mmio_read_u8(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned char *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u16(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned short *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u32(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned int *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u64(spl_i64 addr) {
    return (spl_i64)(*(volatile spl_u64 *)(spl_u64)addr);
}

void rt_mmio_write_u8(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned char *)(spl_u64)addr = (unsigned char)value;
}

void rt_mmio_write_u16(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned short *)(spl_u64)addr = (unsigned short)value;
}

void rt_mmio_write_u32(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned int *)(spl_u64)addr = (unsigned int)value;
}

void rt_mmio_write_u64(spl_i64 addr, spl_i64 value) {
    *(volatile spl_u64 *)(spl_u64)addr = (spl_u64)value;
}

static void uart_put_byte(spl_u8 byte) {
    *(volatile spl_u8 *)0x10000000ULL = byte;
}

void rt_riscv_uart_put(spl_u64 byte) {
    uart_put_byte((spl_u8)byte);
}

static void uart_write_bytes(const char *data, spl_u64 len) {
    if (!data) {
        return;
    }
    for (spl_u64 i = 0; i < len; i = i + 1) {
        uart_put_byte((spl_u8)data[i]);
    }
}

void log_raw_println(spl_i64 msg) {
    RtString *text = rt_as_string(msg);
    spl_i64 rendered;
    if (!text) {
        rendered = rt_to_string(msg);
        text = rt_as_string(rendered);
    }
    if (text) {
        uart_write_bytes(text->data, text->len);
    }
    uart_put_byte(13);
    uart_put_byte(10);
}

void serial_println(spl_i64 msg) {
    log_raw_println(msg);
}

spl_i64 rt_string_len(spl_i64 value) {
    RtString *string = rt_as_string(value);
    return string ? (spl_i64)string->len : 0;
}

spl_i64 rt_string_data(spl_i64 value) {
    RtString *string = rt_as_string(value);
    if (!string) {
        return 0;
    }
    return (spl_i64)(spl_u64)string->data;
}

spl_i64 rt_byte_array_new(spl_i64 capacity_value) {
    return rt_array_new(capacity_value);
}

spl_i64 rt_byte_array_new_len(spl_i64 len_value) {
    spl_i64 array = rt_array_new(len_value);
    RtArray *arr = rt_as_array(array);
    spl_i64 len = rt_index_arg(len_value);
    if (!arr || len <= 0) {
        return array;
    }
    for (spl_i64 i = 0; i < len; i = i + 1) {
        rt_array_push(array, rt_int(0));
    }
    return array;
}

spl_i64 rt_text_to_bytes(spl_i64 text_value) {
    RtString *string = rt_as_string(text_value);
    spl_i64 out;
    if (!string) {
        return rt_array_new(0);
    }
    out = rt_array_new((spl_i64)string->len);
    for (spl_u64 i = 0; i < string->len; i = i + 1) {
        rt_array_push(out, rt_int((spl_i64)(unsigned char)string->data[i]));
    }
    return out;
}

spl_i64 rt_ssh_userauth_password_only_failure_payload(void) {
    spl_i64 out = rt_array_new(14);
    rt_array_push(out, rt_int(51));
    rt_array_push(out, rt_int(0));
    rt_array_push(out, rt_int(0));
    rt_array_push(out, rt_int(0));
    rt_array_push(out, rt_int(8));
    rt_array_push(out, rt_int('p'));
    rt_array_push(out, rt_int('a'));
    rt_array_push(out, rt_int('s'));
    rt_array_push(out, rt_int('s'));
    rt_array_push(out, rt_int('w'));
    rt_array_push(out, rt_int('o'));
    rt_array_push(out, rt_int('r'));
    rt_array_push(out, rt_int('d'));
    rt_array_push(out, rt_special(RT_VALUE_SPECIAL_FALSE));
    return out;
}

spl_i64 rt_string_join(spl_i64 array_value, spl_i64 separator_value) {
    RtArray *array = rt_as_array(array_value);
    RtString *separator = rt_as_string(separator_value);
    RtString *joined;
    spl_u64 total_len = 0;
    spl_u64 out_index = 0;
    if (!array) {
        return rt_string_new((spl_i64)(spl_u64)"", 0);
    }
    for (spl_u64 i = 0; i < array->len; i = i + 1) {
        RtString *elem = rt_as_string(rt_to_string(array->data[i]));
        if (elem) {
            total_len = total_len + elem->len;
        }
        if (separator && i + 1 < array->len) {
            total_len = total_len + separator->len;
        }
    }
    joined = (RtString *)rt_alloc((spl_i64)(sizeof(RtString) + total_len + 1));
    if (!joined) {
        return rt_nil();
    }
    joined->header.object_type = RT_HEAP_STRING;
    joined->header.gc_flags = 0;
    joined->header.reserved = 0;
    joined->header.size = (spl_u32)(sizeof(RtString) + total_len);
    joined->len = total_len;
    joined->hash = 0;
    for (spl_u64 i = 0; i < array->len; i = i + 1) {
        RtString *elem = rt_as_string(rt_to_string(array->data[i]));
        if (elem) {
            for (spl_u64 j = 0; j < elem->len; j = j + 1) {
                joined->data[out_index] = elem->data[j];
                out_index = out_index + 1;
            }
        }
        if (separator && i + 1 < array->len) {
            for (spl_u64 j = 0; j < separator->len; j = j + 1) {
                joined->data[out_index] = separator->data[j];
                out_index = out_index + 1;
            }
        }
    }
    joined->data[out_index] = 0;
    return rt_heap(joined);
}

void unsafe(void) {
}

static spl_u64 g_riscv_pmm_base = 0;
static spl_u64 g_riscv_pmm_limit = 0;
static spl_u64 g_riscv_pmm_next = 0;
static spl_u64 g_riscv_pmm_free_pages = 0;
static spl_u64 g_riscv_pmm_total_pages = 0;
static spl_i64 g_riscv_pmm_ready = 0;

static spl_u64 rt_normalize_phys32(spl_u64 value) {
    if ((value >> 32) == 0xffffffffULL) {
        return value & 0xffffffffULL;
    }
    return value;
}

static void uart_line(const char *text) {
    spl_u64 len = 0;
    while (text[len]) {
        len = len + 1;
    }
    uart_write_bytes(text, len);
    uart_put_byte(13);
    uart_put_byte(10);
}

spl_i64 rt_riscv_noalloc_pmm_init(
    spl_u64 ram_base,
    spl_u64 ram_size,
    spl_u64 reserved_end,
    spl_u64 heap_start
) {
    const spl_u64 page_size = 4096ULL;
    spl_u64 ram_end;
    spl_u64 alloc_base;
    spl_u64 alloc_limit;
    ram_base = rt_normalize_phys32(ram_base);
    reserved_end = rt_normalize_phys32(reserved_end);
    heap_start = rt_normalize_phys32(heap_start);
    if (ram_size <= page_size || reserved_end <= ram_base || heap_start <= reserved_end) {
        uart_line("PMM FAIL");
        return rt_special(RT_VALUE_SPECIAL_FALSE);
    }
    ram_end = ram_base + ram_size;
    if (ram_end <= ram_base || heap_start > ram_end) {
        uart_line("PMM FAIL");
        return rt_special(RT_VALUE_SPECIAL_FALSE);
    }
    alloc_base = (reserved_end + page_size - 1ULL) & ~(page_size - 1ULL);
    alloc_limit = heap_start;
    if (alloc_base >= alloc_limit) {
        uart_line("PMM FAIL");
        return rt_special(RT_VALUE_SPECIAL_FALSE);
    }
    g_riscv_pmm_base = alloc_base;
    g_riscv_pmm_limit = alloc_limit;
    g_riscv_pmm_next = alloc_base;
    g_riscv_pmm_total_pages = (alloc_limit - alloc_base) / page_size;
    g_riscv_pmm_free_pages = g_riscv_pmm_total_pages;
    g_riscv_pmm_ready = 1;
    uart_line("PMM OK");
    return rt_special(RT_VALUE_SPECIAL_TRUE);
}

spl_i64 rt_riscv_noalloc_pmm_init_default(void) {
    return rt_riscv_noalloc_pmm_init(
        0x80000000ULL,
        128ULL * 1024ULL * 1024ULL,
        0x80400000ULL,
        0x87000000ULL
    );
}

spl_u64 rt_riscv_noalloc_alloc_page(void) {
    const spl_u64 page_size = 4096ULL;
    spl_u64 page;
    if (!g_riscv_pmm_ready || g_riscv_pmm_next >= g_riscv_pmm_limit) {
        return 0;
    }
    page = g_riscv_pmm_next;
    g_riscv_pmm_next = g_riscv_pmm_next + page_size;
    if (g_riscv_pmm_free_pages > 0) {
        g_riscv_pmm_free_pages = g_riscv_pmm_free_pages - 1;
    }
    return page;
}

spl_i64 rt_riscv_noalloc_pmm_is_ready(void) {
    return g_riscv_pmm_ready ? rt_special(RT_VALUE_SPECIAL_TRUE) : rt_special(RT_VALUE_SPECIAL_FALSE);
}

spl_u64 rt_riscv_noalloc_pmm_free_pages(void) {
    return g_riscv_pmm_free_pages;
}

spl_u64 rt_riscv_noalloc_pmm_total_pages(void) {
    return g_riscv_pmm_total_pages;
}

spl_u64 rt_riscv_qemu_ram_base(void) {
    return 0x80000000ULL;
}

spl_u64 rt_riscv_qemu_ram_size(void) {
    return 128ULL * 1024ULL * 1024ULL;
}

spl_u64 rt_riscv_qemu_reserved_end(void) {
    return 0x80400000ULL;
}

spl_u64 rt_riscv_qemu_heap_start(void) {
    return 0x87000000ULL;
}

spl_u64 rt_riscv_qemu_heap_size(void) {
    return 16ULL * 1024ULL * 1024ULL;
}

spl_i64 rt_time_now_unix_micros(void) {
    spl_u64 cycles;
    __asm__ volatile("rdtime %0" : "=r"(cycles));
    return (spl_i64)(cycles / 10ULL);
}

void rt_thread_sleep(spl_i64 millis) {
    spl_i64 start;
    spl_i64 target_delta;
    if (millis <= 0) {
        return;
    }
    start = rt_time_now_unix_micros();
    target_delta = millis * 1000LL;
    while ((rt_time_now_unix_micros() - start) < target_delta) {
        __asm__ volatile("" ::: "memory");
    }
}

spl_u64 rt_riscv_seed(void) {
    spl_u64 cycle;
    spl_u64 time;
    spl_u64 instret;
    __asm__ volatile("rdcycle %0" : "=r"(cycle));
    __asm__ volatile("rdtime %0" : "=r"(time));
    __asm__ volatile("rdinstret %0" : "=r"(instret));
    return cycle ^ (time << 21) ^ (time >> 7) ^ (instret << 13) ^ (instret >> 17);
}

spl_i64 vmm_map_page(spl_i64 virt, spl_i64 phys, spl_i64 flags) {
    (void)flags;
    return virt == phys ? 1 : 0;
}

typedef struct RtPciDevice {
    spl_i64 bus;
    spl_i64 device;
    spl_i64 function;
    spl_i64 class_code;
    spl_i64 subclass;
    spl_i64 vendor;
    spl_i64 device_id;
    spl_i64 bar0;
    spl_i64 irq;
} RtPciDevice;

#define RT_PCI_ECAM_BASE 0x30000000ULL
#define RT_PCI_IO_BASE 0x03000000ULL
#define RT_PCI_MMIO_BASE 0x40000000ULL
#define RT_PCI_LEGACY_NET_IO_PORT 0x1000ULL
#define RT_PCI_LEGACY_GPU_IO_PORT 0x2000ULL
#define RT_PCI_LEGACY_BLK_IO_PORT 0x3000ULL
#define RT_PCI_CMD_IO 0x1U
#define RT_PCI_CMD_MEM 0x2U
#define RT_PCI_CMD_BUS_MASTER 0x4U
#define RT_PCI_MAX_DEVICES 32
#define RT_VIRTIO_VENDOR_ID 0x1af4
#define RT_VIRTIO_NET_LEGACY_DEVICE_ID 0x1000
#define RT_VIRTIO_NET_MODERN_DEVICE_ID 0x1041
#define RT_VIRTIO_BLK_LEGACY_DEVICE_ID 0x1001
#define RT_VIRTIO_BLK_MODERN_DEVICE_ID 0x1042
#define RT_VIRTIO_GPU_LEGACY_DEVICE_ID 0x1010
#define RT_VIRTIO_GPU_MODERN_DEVICE_ID 0x1050
#define RT_VIRTIO_PCI_HOST_FEATURES 0x00ULL
#define RT_VIRTIO_PCI_GUEST_FEATURES 0x04ULL
#define RT_VIRTIO_PCI_QUEUE_PFN 0x08ULL
#define RT_VIRTIO_PCI_QUEUE_SIZE 0x0cULL
#define RT_VIRTIO_PCI_QUEUE_SEL 0x0eULL
#define RT_VIRTIO_PCI_QUEUE_NOTIFY 0x10ULL
#define RT_VIRTIO_PCI_STATUS 0x12ULL
#define RT_VIRTIO_NET_MAC_OFFSET 0x14ULL
#define RT_PCI_CAP_ID_VENDOR_SPECIFIC 0x09U
#define RT_VIRTIO_PCI_CAP_COMMON_CFG 1U
#define RT_VIRTIO_PCI_CAP_NOTIFY_CFG 2U
#define RT_VIRTIO_MODERN_DEVICE_FEATURE_SELECT 0x00ULL
#define RT_VIRTIO_MODERN_DEVICE_FEATURE 0x04ULL
#define RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT 0x08ULL
#define RT_VIRTIO_MODERN_DRIVER_FEATURE 0x0cULL
#define RT_VIRTIO_MODERN_NUM_QUEUES 0x12ULL
#define RT_VIRTIO_MODERN_DEVICE_STATUS 0x14ULL
#define RT_VIRTIO_MODERN_QUEUE_SELECT 0x16ULL
#define RT_VIRTIO_MODERN_QUEUE_SIZE 0x18ULL
#define RT_VIRTIO_MODERN_QUEUE_ENABLE 0x1cULL
#define RT_VIRTIO_MODERN_QUEUE_NOTIFY_OFF 0x1eULL
#define RT_VIRTIO_MODERN_QUEUE_DESC_LO 0x20ULL
#define RT_VIRTIO_MODERN_QUEUE_DESC_HI 0x24ULL
#define RT_VIRTIO_MODERN_QUEUE_DRIVER_LO 0x28ULL
#define RT_VIRTIO_MODERN_QUEUE_DRIVER_HI 0x2cULL
#define RT_VIRTIO_MODERN_QUEUE_DEVICE_LO 0x30ULL
#define RT_VIRTIO_MODERN_QUEUE_DEVICE_HI 0x34ULL
#define RT_VIRTIO_STATUS_ACKNOWLEDGE 1U
#define RT_VIRTIO_STATUS_DRIVER 2U
#define RT_VIRTIO_STATUS_DRIVER_OK 4U
#define RT_VIRTIO_STATUS_FEATURES_OK 8U
#define RT_VIRTIO_STATUS_FAILED 128U
#define RT_VIRTIO_NET_RX_QUEUE 0U
#define RT_VIRTIO_NET_TX_QUEUE 1U
#define RT_VIRTIO_NET_HDR_SIZE 10U
#define RT_VIRTQ_DESC_F_NEXT 1U
#define RT_VIRTQ_DESC_F_WRITE 2U
#define RT_NET_QUEUE_CAP 256U
#define RT_NET_RX_POST_COUNT 8U
#define RT_NET_BUFFER_SIZE 2048U
#define RT_VIRTIO_BLK_QUEUE 0U
#define VIRTIO_BLK_T_IN 0U
#define VIRTIO_BLK_T_OUT 1U
#define RT_VIRTIO_BLK_CONFIG_CAPACITY 0x14ULL
#define RT_VIRTIO_BLK_SECTOR_SIZE 512U
#define RT_NVFS_MAGIC 0x4e564653U
#define RT_NVFS_VERSION 2U
#define RT_GPU_QUEUE_CAP 64U
#define RT_GPU_WIDTH 320U
#define RT_GPU_HEIGHT 240U
#define RT_GPU_RESOURCE_ID 1U
#define RT_GPU_CMD_GET_DISPLAY_INFO 0x0100U
#define RT_GPU_CMD_RESOURCE_CREATE_2D 0x0101U
#define RT_GPU_CMD_SET_SCANOUT 0x0103U
#define RT_GPU_CMD_RESOURCE_FLUSH 0x0104U
#define RT_GPU_CMD_TRANSFER_TO_HOST_2D 0x0105U
#define RT_GPU_CMD_RESOURCE_ATTACH_BACKING 0x0106U
#define RT_GPU_RESP_OK_NODATA 0x1100U
#define RT_GPU_RESP_OK_DISPLAY_INFO 0x1101U
#define RT_GPU_FORMAT_B8G8R8A8_UNORM 1U

static RtPciDevice g_rt_pci_devices[RT_PCI_MAX_DEVICES];
static spl_i64 g_rt_pci_count = -1;
static spl_i64 g_rt_net_ready = 0;
static spl_i64 g_rt_net_tx_ready = 0;
static spl_i64 g_rt_net_rx_ready = 0;
static spl_i64 g_rt_net_tx_probe_code = -1;
static spl_u64 g_rt_net_bar0 = 0;
static spl_u64 g_rt_rx_desc = 0;
static spl_u64 g_rt_rx_avail = 0;
static spl_u64 g_rt_rx_used = 0;
static spl_u64 g_rt_rx_bufs = 0;
static spl_u16 g_rt_rx_qsize = 0;
static spl_u16 g_rt_rx_last_used = 0;
static spl_u64 g_rt_tx_desc = 0;
static spl_u64 g_rt_tx_avail = 0;
static spl_u64 g_rt_tx_used = 0;
static spl_u64 g_rt_tx_bufs = 0;
static spl_u16 g_rt_tx_qsize = 0;
static spl_u16 g_rt_tx_last_used = 0;
static spl_i64 g_rt_storage_ready = 0;
static spl_i64 g_rt_storage_probe_ready = 0;
static spl_u64 g_rt_blk_bar0 = 0;
static spl_u64 g_rt_blk_desc = 0;
static spl_u64 g_rt_blk_avail = 0;
static spl_u64 g_rt_blk_used = 0;
static spl_u16 g_rt_blk_qsize = 0;
static spl_u16 g_rt_blk_last_used = 0;
static spl_u64 g_rt_blk_req = 0;
static spl_u64 g_rt_blk_data = 0;
static spl_u64 g_rt_blk_capacity = 0;
static spl_i64 g_rt_blk_nvfs_ready = 0;
static spl_i64 g_rt_blk_nvfs_arena_ready = 0;
static spl_i64 g_rt_display_ready = 0;
static spl_i64 g_rt_gpu_modern = 0;
static spl_u64 g_rt_gpu_bar0 = 0;
static spl_u64 g_rt_gpu_common = 0;
static spl_u64 g_rt_gpu_notify = 0;
static spl_u32 g_rt_gpu_notify_multiplier = 0;
static spl_u16 g_rt_gpu_notify_off = 0;
static spl_u64 g_rt_gpu_desc = 0;
static spl_u64 g_rt_gpu_avail = 0;
static spl_u64 g_rt_gpu_used = 0;
static spl_u16 g_rt_gpu_qsize = 0;
static spl_u16 g_rt_gpu_last_used = 0;
static spl_u64 g_rt_gpu_cmd = 0;
static spl_u64 g_rt_gpu_resp = 0;
static spl_u64 g_rt_gpu_fb = 0;

static spl_u32 rt_pci_read_config32(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + (reg & ~3ULL);
    return *(volatile spl_u32 *)addr;
}

static spl_u8 rt_pci_read_config8(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + reg;
    return *(volatile spl_u8 *)addr;
}

static void rt_pci_write_config32(spl_u64 bus, spl_u64 dev, spl_u64 func, spl_u64 reg, spl_u32 value) {
    spl_u64 addr = RT_PCI_ECAM_BASE
        + (bus << 20)
        + (dev << 15)
        + (func << 12)
        + (reg & ~3ULL);
    *(volatile spl_u32 *)addr = value;
}

static spl_u8 rt_mmio_read8_raw(spl_u64 addr) {
    return *(volatile spl_u8 *)addr;
}

static spl_u16 rt_mmio_read16_raw(spl_u64 addr) {
    return *(volatile spl_u16 *)addr;
}

static void rt_mmio_write8_raw(spl_u64 addr, spl_u8 value) {
    *(volatile spl_u8 *)addr = value;
}

static void rt_mmio_write16_raw(spl_u64 addr, spl_u16 value) {
    *(volatile spl_u16 *)addr = value;
}

static void rt_mmio_write32_raw(spl_u64 addr, spl_u32 value) {
    *(volatile spl_u32 *)addr = value;
}

static spl_u8 rt_io_read8(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u8 *)(base + off);
}

static spl_u16 rt_io_read16(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u16 *)(base + off);
}

static spl_u32 rt_io_read32(spl_u64 base, spl_u64 off) {
    return *(volatile spl_u32 *)(base + off);
}

static void rt_io_write8(spl_u64 base, spl_u64 off, spl_u8 value) {
    *(volatile spl_u8 *)(base + off) = value;
}

static void rt_io_write16(spl_u64 base, spl_u64 off, spl_u16 value) {
    *(volatile spl_u16 *)(base + off) = value;
}

static void rt_io_write32(spl_u64 base, spl_u64 off, spl_u32 value) {
    *(volatile spl_u32 *)(base + off) = value;
}

static void rt_memzero(void *ptr, spl_u64 bytes) {
    spl_u8 *data = (spl_u8 *)ptr;
    for (spl_u64 i = 0; i < bytes; i = i + 1) {
        data[i] = 0;
    }
}

static spl_u64 rt_alloc_contiguous_pages(spl_u64 pages) {
    spl_u64 base = 0;
    spl_u64 prev = 0;
    if (pages == 0) {
        return 0;
    }
    for (spl_u64 i = 0; i < pages; i = i + 1) {
        spl_u64 page = rt_riscv_noalloc_alloc_page();
        if (page == 0) {
            return 0;
        }
        if (i == 0) {
            base = page;
        } else if (page != prev + 4096ULL) {
            return 0;
        }
        prev = page;
    }
    return base;
}

static spl_u64 rt_virtqueue_desc_size(spl_u16 qsize) {
    return (spl_u64)qsize * 16ULL;
}

static spl_u64 rt_virtqueue_avail_size(spl_u16 qsize) {
    return 4ULL + 2ULL * (spl_u64)qsize;
}

static spl_u64 rt_virtqueue_total_size(spl_u16 qsize) {
    spl_u64 desc_avail = rt_virtqueue_desc_size(qsize) + rt_virtqueue_avail_size(qsize);
    spl_u64 used = 4ULL + 8ULL * (spl_u64)qsize;
    return ((desc_avail + 4095ULL) & ~4095ULL) + used;
}

static void rt_desc_write(spl_u64 desc_base, spl_u16 idx, spl_u64 addr, spl_u32 len, spl_u16 flags, spl_u16 next) {
    volatile spl_u32 *lo = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL);
    volatile spl_u32 *hi = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL + 4ULL);
    volatile spl_u32 *dlen = (volatile spl_u32 *)(desc_base + (spl_u64)idx * 16ULL + 8ULL);
    volatile spl_u16 *dflags = (volatile spl_u16 *)(desc_base + (spl_u64)idx * 16ULL + 12ULL);
    volatile spl_u16 *dnext = (volatile spl_u16 *)(desc_base + (spl_u64)idx * 16ULL + 14ULL);
    *lo = (spl_u32)(addr & 0xffffffffULL);
    *hi = (spl_u32)(addr >> 32);
    *dlen = len;
    *dflags = flags;
    *dnext = next;
}

static void rt_avail_push(spl_u64 avail_base, spl_u16 qsize, spl_u16 desc_idx) {
    volatile spl_u16 *idxp = (volatile spl_u16 *)(avail_base + 2ULL);
    spl_u16 idx = *idxp;
    volatile spl_u16 *slot = (volatile spl_u16 *)(avail_base + 4ULL + ((spl_u64)(idx % qsize) * 2ULL));
    *slot = desc_idx;
    *idxp = idx + 1U;
}

static spl_i64 rt_setup_virtqueue(spl_u64 bar0, spl_u16 queue, spl_u64 *desc, spl_u64 *avail, spl_u64 *used, spl_u16 *qsize) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 ring;
    spl_u64 pages;
    spl_u64 desc_avail;
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_SEL, queue);
    max_size = rt_io_read16(bar0, RT_VIRTIO_PCI_QUEUE_SIZE);
    if (max_size == 0) {
        return -1;
    }
    if (max_size > RT_NET_QUEUE_CAP) {
        return -1;
    }
    size = max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -1;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    *desc = ring;
    *avail = ring + rt_virtqueue_desc_size(size);
    *used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    *qsize = size;
    rt_io_write32(bar0, RT_VIRTIO_PCI_QUEUE_PFN, (spl_u32)(ring >> 12));
    return 0;
}

static spl_i64 rt_setup_virtqueue_capped(spl_u64 bar0, spl_u16 queue, spl_u16 cap, spl_u64 *desc, spl_u64 *avail, spl_u64 *used, spl_u16 *qsize) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 ring;
    spl_u64 pages;
    spl_u64 desc_avail;
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_SEL, queue);
    max_size = rt_io_read16(bar0, RT_VIRTIO_PCI_QUEUE_SIZE);
    if (max_size == 0) {
        return -1;
    }
    size = max_size > cap ? cap : max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -1;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    *desc = ring;
    *avail = ring + rt_virtqueue_desc_size(size);
    *used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    *qsize = size;
    rt_io_write32(bar0, RT_VIRTIO_PCI_QUEUE_PFN, (spl_u32)(ring >> 12));
    return 0;
}

static spl_i64 rt_prepost_rx(spl_u64 bar0) {
    spl_u16 count = g_rt_rx_qsize;
    spl_u64 pages;
    if (count > RT_NET_RX_POST_COUNT) {
        count = RT_NET_RX_POST_COUNT;
    }
    pages = (((spl_u64)count * RT_NET_BUFFER_SIZE) + 4095ULL) / 4096ULL;
    g_rt_rx_bufs = rt_alloc_contiguous_pages(pages);
    if (g_rt_rx_bufs == 0) {
        return -1;
    }
    rt_memzero((void *)g_rt_rx_bufs, pages * 4096ULL);
    for (spl_u16 i = 0; i < count; i = i + 1) {
        spl_u64 buf = g_rt_rx_bufs + (spl_u64)i * (spl_u64)RT_NET_BUFFER_SIZE;
        rt_desc_write(g_rt_rx_desc, i, buf, RT_NET_BUFFER_SIZE, RT_VIRTQ_DESC_F_WRITE, 0);
        rt_avail_push(g_rt_rx_avail, g_rt_rx_qsize, i);
    }
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_NET_RX_QUEUE);
    return 0;
}

static spl_i64 rt_submit_tx_probe(spl_u64 bar0) {
    spl_u64 packet;
    spl_u64 payload;
    volatile spl_u16 *used_idx;
    spl_u16 start;
    g_rt_tx_bufs = rt_riscv_noalloc_alloc_page();
    if (g_rt_tx_bufs == 0 || g_rt_tx_qsize < 2) {
        return -10;
    }
    rt_memzero((void *)g_rt_tx_bufs, 4096ULL);
    packet = g_rt_tx_bufs;
    payload = packet + RT_VIRTIO_NET_HDR_SIZE;
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        ((volatile spl_u8 *)payload)[i] = 0xffU;
    }
    for (spl_u64 i = 6; i < 12; i = i + 1) {
        ((volatile spl_u8 *)payload)[i] = (spl_u8)(0x52U + i);
    }
    ((volatile spl_u8 *)payload)[12] = 0x08U;
    ((volatile spl_u8 *)payload)[13] = 0x06U;
    rt_desc_write(g_rt_tx_desc, 0, packet, 70U, 0, 0);
    rt_avail_push(g_rt_tx_avail, g_rt_tx_qsize, 0);
    used_idx = (volatile spl_u16 *)(g_rt_tx_used + 2ULL);
    start = *used_idx;
    rt_io_write16(bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_NET_TX_QUEUE);
    for (spl_u64 polls = 0; polls < 1000000ULL; polls = polls + 1) {
        if (*used_idx != start) {
            g_rt_tx_last_used = *used_idx;
            return 0;
        }
    }
    return -11;
}

static spl_u8 g_rt_net_mac[6];
static spl_i64 g_boot_tcp_bound = 0;
static spl_i64 g_boot_tcp_client_ready = 0;
static spl_i64 g_boot_tcp_client_open = 0;
static spl_u8 g_boot_tcp_peer_mac[6];
static spl_u32 g_boot_tcp_peer_ip = 0;
static spl_u16 g_boot_tcp_peer_port = 0;
static spl_u32 g_boot_tcp_recv_next = 0;
static spl_u32 g_boot_tcp_send_next = 0x10203040U;
static spl_i64 g_boot_tcp_response_kind = 0;

static spl_u16 rt_be16(const spl_u8 *p) {
    return (spl_u16)(((spl_u16)p[0] << 8) | (spl_u16)p[1]);
}

static spl_u32 rt_be32(const spl_u8 *p) {
    return ((spl_u32)p[0] << 24) | ((spl_u32)p[1] << 16) | ((spl_u32)p[2] << 8) | (spl_u32)p[3];
}

static void rt_put_be16(spl_u8 *p, spl_u16 v) {
    p[0] = (spl_u8)(v >> 8);
    p[1] = (spl_u8)v;
}

static void rt_put_be32(spl_u8 *p, spl_u32 v) {
    p[0] = (spl_u8)(v >> 24);
    p[1] = (spl_u8)(v >> 16);
    p[2] = (spl_u8)(v >> 8);
    p[3] = (spl_u8)v;
}

static spl_u32 rt_checksum_add(spl_u32 sum, const spl_u8 *data, spl_u64 len) {
    spl_u64 i = 0;
    while (i + 1ULL < len) {
        sum = sum + (((spl_u32)data[i] << 8) | (spl_u32)data[i + 1ULL]);
        i = i + 2ULL;
    }
    if (i < len) {
        sum = sum + ((spl_u32)data[i] << 8);
    }
    return sum;
}

static spl_u16 rt_checksum_finish(spl_u32 sum) {
    while (sum >> 16) {
        sum = (sum & 0xffffU) + (sum >> 16);
    }
    return (spl_u16)(~sum);
}

static spl_i64 rt_send_frame(const spl_u8 *frame, spl_u64 frame_len) {
    spl_u64 packet;
    volatile spl_u16 *used_idx;
    spl_u16 start;
    if (!g_rt_net_tx_ready || g_rt_tx_bufs == 0 || frame_len + RT_VIRTIO_NET_HDR_SIZE > RT_NET_BUFFER_SIZE) {
        return -1;
    }
    packet = g_rt_tx_bufs + RT_NET_BUFFER_SIZE;
    rt_memzero((void *)packet, frame_len + RT_VIRTIO_NET_HDR_SIZE);
    for (spl_u64 i = 0; i < frame_len; i = i + 1) {
        ((volatile spl_u8 *)(packet + RT_VIRTIO_NET_HDR_SIZE))[i] = frame[i];
    }
    rt_desc_write(g_rt_tx_desc, 1, packet, (spl_u32)(frame_len + RT_VIRTIO_NET_HDR_SIZE), 0, 0);
    rt_avail_push(g_rt_tx_avail, g_rt_tx_qsize, 1);
    used_idx = (volatile spl_u16 *)(g_rt_tx_used + 2ULL);
    start = *used_idx;
    rt_io_write16(g_rt_net_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_NET_TX_QUEUE);
    for (spl_u64 polls = 0; polls < 1000000ULL; polls = polls + 1) {
        if (*used_idx != start) {
            g_rt_tx_last_used = *used_idx;
            return 0;
        }
    }
    return -1;
}

static void rt_build_eth(spl_u8 *frame, const spl_u8 *dst, spl_u16 ethertype) {
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        frame[i] = dst[i];
        frame[6 + i] = g_rt_net_mac[i];
    }
    rt_put_be16(frame + 12, ethertype);
}

static void rt_send_arp_reply(const spl_u8 *rx) {
    spl_u8 frame[42];
    const spl_u8 *arp = rx + 14;
    spl_u32 sender_ip = rt_be32(arp + 14);
    spl_u32 target_ip = rt_be32(arp + 24);
    rt_build_eth(frame, rx + 6, 0x0806U);
    rt_put_be16(frame + 14, 1);
    rt_put_be16(frame + 16, 0x0800U);
    frame[18] = 6;
    frame[19] = 4;
    rt_put_be16(frame + 20, 2);
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        frame[22 + i] = g_rt_net_mac[i];
        frame[32 + i] = rx[6 + i];
    }
    rt_put_be32(frame + 28, target_ip);
    rt_put_be32(frame + 38, sender_ip);
    rt_send_frame(frame, 42);
}

static void rt_send_tcp_packet(spl_u8 flags, const spl_u8 *payload, spl_u16 payload_len) {
    spl_u8 frame[256];
    spl_u16 ip_len = (spl_u16)(20U + 20U + payload_len);
    spl_u16 tcp_len = (spl_u16)(20U + payload_len);
    spl_u32 sum;
    if (14U + ip_len > sizeof(frame)) {
        return;
    }
    rt_memzero(frame, sizeof(frame));
    rt_build_eth(frame, g_boot_tcp_peer_mac, 0x0800U);
    frame[14] = 0x45U;
    frame[15] = 0;
    rt_put_be16(frame + 16, ip_len);
    rt_put_be16(frame + 18, 1);
    rt_put_be16(frame + 20, 0x4000U);
    frame[22] = 64;
    frame[23] = 6;
    rt_put_be32(frame + 26, 0x0a00020fU);
    rt_put_be32(frame + 30, g_boot_tcp_peer_ip);
    rt_put_be16(frame + 34, 8080);
    rt_put_be16(frame + 36, g_boot_tcp_peer_port);
    rt_put_be32(frame + 38, g_boot_tcp_send_next);
    rt_put_be32(frame + 42, g_boot_tcp_recv_next);
    frame[46] = 0x50U;
    frame[47] = flags;
    rt_put_be16(frame + 48, 4096);
    if (payload_len > 0) {
        for (spl_u64 i = 0; i < payload_len; i = i + 1) {
            frame[54 + i] = payload[i];
        }
    }
    sum = rt_checksum_add(0, frame + 14, 20);
    rt_put_be16(frame + 24, rt_checksum_finish(sum));
    sum = 0;
    sum = sum + ((0x0aU << 8) | 0x00U) + ((0x02U << 8) | 0x0fU);
    sum = sum + (spl_u16)(g_boot_tcp_peer_ip >> 16) + (spl_u16)g_boot_tcp_peer_ip;
    sum = sum + 6U + tcp_len;
    sum = rt_checksum_add(sum, frame + 34, tcp_len);
    rt_put_be16(frame + 50, rt_checksum_finish(sum));
    if (rt_send_frame(frame, 14ULL + ip_len) == 0) {
        if (flags & 0x02U) {
            g_boot_tcp_send_next = g_boot_tcp_send_next + 1U;
        }
        g_boot_tcp_send_next = g_boot_tcp_send_next + payload_len;
        if (flags & 0x01U) {
            g_boot_tcp_send_next = g_boot_tcp_send_next + 1U;
        }
    }
}

static void rt_process_tcp(const spl_u8 *frame, spl_u64 len) {
    const spl_u8 *ip = frame + 14;
    spl_u16 ip_total;
    spl_u64 ip_hlen;
    const spl_u8 *tcp;
    spl_u16 src_port;
    spl_u16 dst_port;
    spl_u32 seq;
    spl_u8 flags;
    spl_u64 tcp_hlen;
    spl_u64 payload_len;
    if (len < 54 || ip[9] != 6) {
        return;
    }
    ip_hlen = (spl_u64)(ip[0] & 0x0fU) * 4ULL;
    ip_total = rt_be16(ip + 2);
    if (ip_hlen < 20 || len < 14ULL + ip_total || ip_total < ip_hlen + 20ULL) {
        return;
    }
    tcp = ip + ip_hlen;
    src_port = rt_be16(tcp);
    dst_port = rt_be16(tcp + 2);
    if (dst_port != 8080) {
        return;
    }
    seq = rt_be32(tcp + 4);
    flags = tcp[13];
    tcp_hlen = (spl_u64)(tcp[12] >> 4) * 4ULL;
    if (tcp_hlen < 20 || ip_total < ip_hlen + tcp_hlen) {
        return;
    }
    payload_len = (spl_u64)ip_total - ip_hlen - tcp_hlen;
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        g_boot_tcp_peer_mac[i] = frame[6 + i];
    }
    g_boot_tcp_peer_ip = rt_be32(ip + 12);
    g_boot_tcp_peer_port = src_port;
    if (flags & 0x02U) {
        g_boot_tcp_recv_next = seq + 1U;
        g_boot_tcp_client_open = 1;
        rt_send_tcp_packet(0x12U, (const spl_u8 *)0, 0);
        return;
    }
    if (!g_boot_tcp_client_open) {
        return;
    }
    if (payload_len > 0) {
        g_boot_tcp_response_kind = 1;
        if (payload_len >= 6 &&
            tcp[tcp_hlen + 0] == 'G' &&
            tcp[tcp_hlen + 1] == 'E' &&
            tcp[tcp_hlen + 2] == 'T' &&
            tcp[tcp_hlen + 3] == ' ' &&
            tcp[tcp_hlen + 4] == '/' &&
            tcp[tcp_hlen + 5] == ' ') {
            g_boot_tcp_response_kind = 2;
        }
        g_boot_tcp_recv_next = seq + (spl_u32)payload_len;
        g_boot_tcp_client_ready = 1;
        rt_send_tcp_packet(0x10U, (const spl_u8 *)0, 0);
    } else if (flags & 0x01U) {
        g_boot_tcp_recv_next = seq + 1U;
        rt_send_tcp_packet(0x10U, (const spl_u8 *)0, 0);
    }
}

static void rt_process_rx_frame(const spl_u8 *frame, spl_u64 len) {
    spl_u16 ethertype;
    if (len < 14) {
        return;
    }
    ethertype = rt_be16(frame + 12);
    if (ethertype == 0x0806U && len >= 42) {
        const spl_u8 *arp = frame + 14;
        if (rt_be16(arp + 6) == 1 && rt_be32(arp + 24) == 0x0a00020fU) {
            rt_send_arp_reply(frame);
        }
    } else if (ethertype == 0x0800U) {
        rt_process_tcp(frame, len);
    }
}

static spl_i64 rt_poll_rx_once(void) {
    volatile spl_u16 *used_idxp = (volatile spl_u16 *)(g_rt_rx_used + 2ULL);
    spl_u16 used_idx;
    spl_u16 ring_idx;
    spl_u64 used_entry;
    spl_u32 desc_id;
    spl_u32 total_len;
    spl_u64 frame_len;
    spl_u64 frame;
    if (!g_rt_net_ready || !g_rt_net_rx_ready) {
        return -1;
    }
    used_idx = *used_idxp;
    if (used_idx == g_rt_rx_last_used) {
        return 0;
    }
    ring_idx = g_rt_rx_last_used % g_rt_rx_qsize;
    used_entry = g_rt_rx_used + 4ULL + (spl_u64)ring_idx * 8ULL;
    desc_id = *(volatile spl_u32 *)used_entry;
    total_len = *(volatile spl_u32 *)(used_entry + 4ULL);
    g_rt_rx_last_used = g_rt_rx_last_used + 1U;
    if (desc_id < RT_NET_RX_POST_COUNT && total_len > RT_VIRTIO_NET_HDR_SIZE) {
        frame_len = (spl_u64)total_len - RT_VIRTIO_NET_HDR_SIZE;
        frame = g_rt_rx_bufs + (spl_u64)desc_id * RT_NET_BUFFER_SIZE + RT_VIRTIO_NET_HDR_SIZE;
        rt_process_rx_frame((const spl_u8 *)frame, frame_len);
        rt_desc_write(g_rt_rx_desc, (spl_u16)desc_id, g_rt_rx_bufs + (spl_u64)desc_id * RT_NET_BUFFER_SIZE, RT_NET_BUFFER_SIZE, RT_VIRTQ_DESC_F_WRITE, 0);
        rt_avail_push(g_rt_rx_avail, g_rt_rx_qsize, (spl_u16)desc_id);
        rt_io_write16(g_rt_net_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_NET_RX_QUEUE);
        return 1;
    }
    return 0;
}

static void rt_pci_scan_qemu_virt(void) {
    g_rt_pci_count = 0;
    for (spl_u64 dev = 0; dev < 32 && g_rt_pci_count < RT_PCI_MAX_DEVICES; dev = dev + 1) {
        spl_u32 id = rt_pci_read_config32(0, dev, 0, 0);
        spl_u32 class_reg;
        spl_u32 bar0;
        RtPciDevice *out;
        if ((id & 0xffffU) == 0xffffU) {
            continue;
        }
        class_reg = rt_pci_read_config32(0, dev, 0, 8);
        bar0 = rt_pci_read_config32(0, dev, 0, 0x10);
        out = &g_rt_pci_devices[g_rt_pci_count];
        out->bus = 0;
        out->device = (spl_i64)dev;
        out->function = 0;
        out->class_code = (spl_i64)((class_reg >> 24) & 0xffU);
        out->subclass = (spl_i64)((class_reg >> 16) & 0xffU);
        out->vendor = (spl_i64)(id & 0xffffU);
        out->device_id = (spl_i64)((id >> 16) & 0xffffU);
        out->bar0 = (spl_i64)(bar0 & ~0xfU);
        out->irq = 0;
        g_rt_pci_count = g_rt_pci_count + 1;
    }
}

static spl_i64 rt_pci_is_virtio_net(spl_i64 cls, spl_i64 sub, spl_i64 vendor, spl_i64 device_id) {
    if (cls != 2 || sub != 0) {
        return 0;
    }
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_NET_LEGACY_DEVICE_ID ||
        device_id == RT_VIRTIO_NET_MODERN_DEVICE_ID) {
        return 1;
    }
    return 0;
}

static spl_i64 rt_pci_is_virtio_gpu(spl_i64 cls, spl_i64 sub, spl_i64 vendor, spl_i64 device_id) {
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_GPU_LEGACY_DEVICE_ID) {
        return 1;
    }
    if (device_id == RT_VIRTIO_GPU_MODERN_DEVICE_ID) {
        (void)cls;
        (void)sub;
        return 1;
    }
    return 0;
}

static spl_i64 rt_pci_is_virtio_blk(spl_i64 vendor, spl_i64 device_id) {
    if (vendor != RT_VIRTIO_VENDOR_ID) {
        return 0;
    }
    if (device_id == RT_VIRTIO_BLK_LEGACY_DEVICE_ID ||
        device_id == RT_VIRTIO_BLK_MODERN_DEVICE_ID) {
        return 1;
    }
    return 0;
}

static void rt_put_le32(spl_u8 *p, spl_u32 v);
static void rt_put_le64(spl_u8 *p, spl_u64 v);
static spl_u32 rt_get_le32(const spl_u8 *p);

spl_i64 rt_pci_device_count(void) {
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    return g_rt_pci_count;
}

spl_i64 rt_pci_get_field(spl_i64 index, spl_i64 field) {
    RtPciDevice *dev;
    if (g_rt_pci_count < 0) {
        rt_pci_scan_qemu_virt();
    }
    if (index < 0 || index >= g_rt_pci_count) {
        return -1;
    }
    dev = &g_rt_pci_devices[index];
    if (field == 0) return dev->bus;
    if (field == 1) return dev->device;
    if (field == 2) return dev->function;
    if (field == 3) return dev->class_code;
    if (field == 4) return dev->subclass;
    if (field == 5) return dev->vendor;
    if (field == 6) return dev->device_id;
    if (field == 7) return dev->bar0;
    if (field == 8) return dev->irq;
    return -1;
}

spl_i64 rt_net_init(void) {
    spl_i64 count = rt_pci_device_count();
    for (spl_i64 i = 0; i < count; i = i + 1) {
        spl_i64 cls = rt_pci_get_field(i, 3);
        spl_i64 sub = rt_pci_get_field(i, 4);
        spl_i64 vendor = rt_pci_get_field(i, 5);
        spl_i64 device_id = rt_pci_get_field(i, 6);
        if (rt_pci_is_virtio_net(cls, sub, vendor, device_id)) {
            RtPciDevice *dev = &g_rt_pci_devices[i];
            if (device_id != RT_VIRTIO_NET_LEGACY_DEVICE_ID) {
                g_rt_net_ready = 0;
                return -2;
            }
            rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x10, (spl_u32)(RT_PCI_LEGACY_NET_IO_PORT | 1ULL));
            rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_IO | RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
            g_rt_net_bar0 = RT_PCI_IO_BASE + RT_PCI_LEGACY_NET_IO_PORT;
            rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, 0);
            rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
            rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
            rt_io_write32(g_rt_net_bar0, RT_VIRTIO_PCI_GUEST_FEATURES, rt_io_read32(g_rt_net_bar0, RT_VIRTIO_PCI_HOST_FEATURES));
            rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
            if ((rt_io_read8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
                rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_net_ready = 0;
                return -3;
            }
            if (rt_setup_virtqueue(g_rt_net_bar0, RT_VIRTIO_NET_RX_QUEUE, &g_rt_rx_desc, &g_rt_rx_avail, &g_rt_rx_used, &g_rt_rx_qsize) < 0) {
                rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_net_ready = 0;
                return -4;
            }
            if (rt_setup_virtqueue(g_rt_net_bar0, RT_VIRTIO_NET_TX_QUEUE, &g_rt_tx_desc, &g_rt_tx_avail, &g_rt_tx_used, &g_rt_tx_qsize) < 0) {
                rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_net_ready = 0;
                return -5;
            }
            if (rt_prepost_rx(g_rt_net_bar0) < 0) {
                rt_io_write8(g_rt_net_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_net_ready = 0;
                return -6;
            }
            rt_io_write8(
                g_rt_net_bar0,
                RT_VIRTIO_PCI_STATUS,
                RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
            );
            for (spl_u64 mac_i = 0; mac_i < 6; mac_i = mac_i + 1) {
                g_rt_net_mac[mac_i] = rt_io_read8(g_rt_net_bar0, RT_VIRTIO_NET_MAC_OFFSET + mac_i);
            }
            g_rt_net_tx_probe_code = rt_submit_tx_probe(g_rt_net_bar0);
            g_rt_net_tx_ready = g_rt_net_tx_probe_code == 0 ? 1 : 0;
            g_rt_net_rx_ready = 1;
            g_rt_net_ready = 1;
            return 0;
        }
    }
    g_rt_net_ready = 0;
    return -1;
}

spl_i64 rt_net_tx_test(void) {
    if (!g_rt_net_ready || !g_rt_net_tx_ready) {
        return g_rt_net_tx_probe_code;
    }
    return 0;
}

spl_i64 rt_net_rx_ready(void) {
    if (!g_rt_net_ready || !g_rt_net_rx_ready) {
        return -1;
    }
    return 0;
}

spl_i64 rt_net_stats(void) {
    return g_rt_net_ready ? 0 : -1;
}

static spl_i64 rt_storage_sector_has_nvfs_superblock(void) {
    spl_u8 *data = (spl_u8 *)g_rt_blk_data;
    spl_u32 magic = rt_get_le32(data);
    spl_u32 version = rt_get_le32(data + 4);
    spl_u32 generation_lo = rt_get_le32(data + 32);
    spl_u32 generation_hi = rt_get_le32(data + 36);
    if (magic != RT_NVFS_MAGIC) {
        return 0;
    }
    if (version != RT_NVFS_VERSION) {
        return 0;
    }
    if (generation_lo == 0U && generation_hi == 0U) {
        return 0;
    }
    return 1;
}

static spl_i64 rt_storage_read_sector(spl_u64 lba) {
    spl_u8 *req = (spl_u8 *)g_rt_blk_req;
    volatile spl_u8 *status;
    volatile spl_u16 *used_idx;
    spl_u16 start;
    if (!g_rt_storage_ready || !g_rt_blk_req || !g_rt_blk_data || g_rt_blk_qsize < 3) {
        return -1;
    }
    rt_memzero((void *)g_rt_blk_req, 4096ULL);
    rt_memzero((void *)g_rt_blk_data, RT_VIRTIO_BLK_SECTOR_SIZE);
    rt_put_le32(req, VIRTIO_BLK_T_IN);
    rt_put_le32(req + 4, 0U);
    rt_put_le64(req + 8, lba);
    status = (volatile spl_u8 *)(g_rt_blk_req + 16ULL);
    *status = 0xffU;
    rt_desc_write(g_rt_blk_desc, 0, g_rt_blk_req, 16U, RT_VIRTQ_DESC_F_NEXT, 1);
    rt_desc_write(g_rt_blk_desc, 1, g_rt_blk_data, RT_VIRTIO_BLK_SECTOR_SIZE, RT_VIRTQ_DESC_F_NEXT | RT_VIRTQ_DESC_F_WRITE, 2);
    rt_desc_write(g_rt_blk_desc, 2, g_rt_blk_req + 16ULL, 1U, RT_VIRTQ_DESC_F_WRITE, 0);
    used_idx = (volatile spl_u16 *)(g_rt_blk_used + 2ULL);
    start = *used_idx;
    rt_avail_push(g_rt_blk_avail, g_rt_blk_qsize, 0);
    __sync_synchronize();
    rt_io_write16(g_rt_blk_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, RT_VIRTIO_BLK_QUEUE);
    for (spl_u64 polls = 0; polls < 1000000ULL; polls = polls + 1) {
        __sync_synchronize();
        if (*used_idx != start) {
            g_rt_blk_last_used = *used_idx;
            if (*status != 0U) {
                return -2;
            }
            return 0;
        }
    }
    return -4;
}

static spl_i64 rt_storage_probe_nvfs_superblock(void) {
    spl_i64 read_rc = rt_storage_read_sector(0ULL);
    if (read_rc < 0) {
        return read_rc;
    }
    if (rt_storage_sector_has_nvfs_superblock()) {
        return 0;
    }
    read_rc = rt_storage_read_sector(1ULL);
    if (read_rc < 0) {
        return read_rc - 10;
    }
    return rt_storage_sector_has_nvfs_superblock() ? 0 : -3;
}

static spl_i64 rt_storage_sector_has_nvfs_arena_payload(void) {
    static const spl_u8 magic[] = "SIMPLEOS_NVFS_ARENA_FILE";
    volatile spl_u8 *data = (volatile spl_u8 *)g_rt_blk_data;
    for (spl_u64 i = 0; i < sizeof(magic) - 1ULL; i = i + 1) {
        if (data[i] != magic[i]) {
            return 0;
        }
    }
    return 1;
}

static spl_i64 rt_storage_probe_nvfs_arena_payload(void) {
    spl_i64 read_rc = rt_storage_read_sector(65ULL);
    if (read_rc < 0) {
        return read_rc;
    }
    return rt_storage_sector_has_nvfs_arena_payload() ? 0 : -3;
}

spl_i64 rt_storage_init(void) {
    spl_i64 count = rt_pci_device_count();
    for (spl_i64 i = 0; i < count; i = i + 1) {
        spl_i64 vendor = rt_pci_get_field(i, 5);
        spl_i64 device_id = rt_pci_get_field(i, 6);
        if (rt_pci_is_virtio_blk(vendor, device_id)) {
            RtPciDevice *dev = &g_rt_pci_devices[i];
            if (device_id != RT_VIRTIO_BLK_LEGACY_DEVICE_ID) {
                g_rt_storage_ready = 0;
                return -2;
            }
            rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x10, (spl_u32)(RT_PCI_LEGACY_BLK_IO_PORT | 1ULL));
            rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_IO | RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
            g_rt_blk_bar0 = RT_PCI_IO_BASE + RT_PCI_LEGACY_BLK_IO_PORT;
            rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, 0);
            rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
            rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
            rt_io_write32(g_rt_blk_bar0, RT_VIRTIO_PCI_GUEST_FEATURES, 0);
            rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
            if ((rt_io_read8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
                rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_storage_ready = 0;
                return -3;
            }
            if (rt_setup_virtqueue(g_rt_blk_bar0, RT_VIRTIO_BLK_QUEUE, &g_rt_blk_desc, &g_rt_blk_avail, &g_rt_blk_used, &g_rt_blk_qsize) < 0) {
                rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_storage_ready = 0;
                return -4;
            }
            g_rt_blk_req = rt_riscv_noalloc_alloc_page();
            g_rt_blk_data = rt_riscv_noalloc_alloc_page();
            if (!g_rt_blk_req || !g_rt_blk_data) {
                rt_io_write8(g_rt_blk_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_FAILED);
                g_rt_storage_ready = 0;
                return -5;
            }
            g_rt_blk_capacity =
                (spl_u64)rt_io_read32(g_rt_blk_bar0, RT_VIRTIO_BLK_CONFIG_CAPACITY) |
                ((spl_u64)rt_io_read32(g_rt_blk_bar0, RT_VIRTIO_BLK_CONFIG_CAPACITY + 4ULL) << 32);
            rt_io_write8(
                g_rt_blk_bar0,
                RT_VIRTIO_PCI_STATUS,
                RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
            );
            g_rt_storage_ready = 1;
            {
                spl_i64 read_rc = rt_storage_probe_nvfs_superblock();
                g_rt_storage_probe_ready = read_rc == 0 ? 1 : 0;
                g_rt_blk_nvfs_ready = g_rt_storage_probe_ready;
                if (!g_rt_storage_probe_ready) {
                    return read_rc - 60;
                }
                read_rc = rt_storage_probe_nvfs_arena_payload();
                g_rt_blk_nvfs_arena_ready = read_rc == 0 ? 1 : 0;
                return g_rt_blk_nvfs_arena_ready ? 0 : read_rc - 80;
            }
        }
    }
    g_rt_storage_ready = 0;
    g_rt_storage_probe_ready = 0;
    return -1;
}

spl_i64 rt_storage_read_probe(void) {
    if (!g_rt_storage_ready) {
        return -1;
    }
    if (g_rt_storage_probe_ready) {
        return 0;
    }
    g_rt_storage_probe_ready = rt_storage_probe_nvfs_superblock() == 0 ? 1 : 0;
    g_rt_blk_nvfs_ready = g_rt_storage_probe_ready;
    if (!g_rt_storage_probe_ready) {
        return -2;
    }
    g_rt_blk_nvfs_arena_ready = rt_storage_probe_nvfs_arena_payload() == 0 ? 1 : 0;
    return g_rt_blk_nvfs_arena_ready ? 0 : -3;
}

spl_i64 rt_storage_capacity_sectors(void) {
    return g_rt_storage_ready ? (spl_i64)g_rt_blk_capacity : 0;
}

spl_i64 rt_storage_nvfs_ready(void) {
    return g_rt_blk_nvfs_ready ? 1 : 0;
}

spl_i64 rt_storage_nvfs_arena_ready(void) {
    return g_rt_blk_nvfs_arena_ready ? 1 : 0;
}

spl_i64 rt_entropy_hardware_ready(void) {
    /* RISC-V TLS remains blocked until SBI/hardware RNG entropy is wired.
     * cycle+time+instret jitter is boot entropy only, not production TLS
     * entropy. */
    return 0;
}

spl_i64 rt_boot_tcp_bind(spl_i64 addr) {
    (void)addr;
    if (!g_rt_net_ready || !g_rt_net_rx_ready || !g_rt_net_tx_ready) {
        return -1;
    }
    g_boot_tcp_bound = 1;
    g_boot_tcp_client_ready = 0;
    g_boot_tcp_client_open = 0;
    g_boot_tcp_send_next = 0x10203040U;
    return 100;
}

spl_i64 rt_boot_tcp_accept_timeout(spl_i64 fd, spl_i64 ms) {
    spl_u64 poll_limit = 50000ULL;
    (void)ms;
    if (fd != 100 || !g_boot_tcp_bound) {
        return -1;
    }
    for (spl_u64 polls = 0; polls < poll_limit; polls = polls + 1) {
        rt_poll_rx_once();
        if (g_boot_tcp_client_ready) {
            g_boot_tcp_client_ready = 0;
            return 200;
        }
    }
    return -1;
}

spl_i64 rt_boot_tcp_write_text(spl_i64 fd, spl_i64 data) {
    RtString *text;
    static const spl_u8 fallback_json_response[] =
        "HTTP/1.1 200 OK\r\n"
        "Content-Type: application/json\r\n"
        "Server: SimpleOS\r\n"
        "Connection: close\r\n"
        "Content-Length: 44\r\n"
        "\r\n"
        "{\"status\":\"ok\",\"server\":\"SimpleOS\"}\n";
    static const spl_u8 fallback_html_response[] =
        "HTTP/1.1 200 OK\r\n"
        "Content-Type: text/html\r\n"
        "Server: SimpleOS\r\n"
        "Connection: close\r\n"
        "Content-Length: 40\r\n"
        "\r\n"
        "<html><body>SimpleOS ready</body></html>";
    if (fd != 200 || !g_boot_tcp_client_open) {
        return -1;
    }
    text = rt_as_string(data);
    if (text) {
        rt_send_tcp_packet(0x18U, (const spl_u8 *)text->data, (spl_u16)text->len);
        rt_send_tcp_packet(0x11U, (const spl_u8 *)0, 0);
        return (spl_i64)text->len;
    }
    if (g_boot_tcp_response_kind == 2) {
        rt_send_tcp_packet(0x18U, fallback_html_response, (spl_u16)(sizeof(fallback_html_response) - 1ULL));
        rt_send_tcp_packet(0x11U, (const spl_u8 *)0, 0);
        return (spl_i64)(sizeof(fallback_html_response) - 1ULL);
    }
    rt_send_tcp_packet(0x18U, fallback_json_response, (spl_u16)(sizeof(fallback_json_response) - 1ULL));
    rt_send_tcp_packet(0x11U, (const spl_u8 *)0, 0);
    return (spl_i64)(sizeof(fallback_json_response) - 1ULL);
}

spl_i64 rt_boot_tcp_close(spl_i64 fd) {
    if (fd == 200) {
        g_boot_tcp_client_open = 0;
        return 0;
    }
    if (fd == 100) {
        g_boot_tcp_bound = 0;
        return 0;
    }
    return -1;
}

__attribute__((weak)) spl_i64 rt_io_tcp_bind(spl_i64 addr) {
    return rt_boot_tcp_bind(addr);
}

__attribute__((weak)) spl_i64 rt_io_tcp_accept_timeout(spl_i64 fd, spl_i64 ms) {
    return rt_boot_tcp_accept_timeout(fd, ms);
}

__attribute__((weak)) spl_i64 rt_io_tcp_write_text(spl_i64 fd, spl_i64 data) {
    return rt_boot_tcp_write_text(fd, data);
}

__attribute__((weak)) spl_i64 rt_io_tcp_close(spl_i64 fd) {
    return rt_boot_tcp_close(fd) == 0 ? 11 : 19;
}

static void rt_put_le32(spl_u8 *p, spl_u32 v) {
    p[0] = (spl_u8)v;
    p[1] = (spl_u8)(v >> 8);
    p[2] = (spl_u8)(v >> 16);
    p[3] = (spl_u8)(v >> 24);
}

static void rt_put_le64(spl_u8 *p, spl_u64 v) {
    for (spl_u64 i = 0; i < 8; i = i + 1) {
        p[i] = (spl_u8)(v >> (i * 8ULL));
    }
}

static spl_u32 rt_get_le32(const spl_u8 *p) {
    return ((spl_u32)p[0]) |
        ((spl_u32)p[1] << 8) |
        ((spl_u32)p[2] << 16) |
        ((spl_u32)p[3] << 24);
}

static void rt_gpu_ctrl_hdr(spl_u8 *p, spl_u32 cmd) {
    rt_memzero(p, 64);
    rt_put_le32(p, cmd);
}

static spl_i64 rt_gpu_send_command(spl_u32 cmd, spl_u32 req_len, spl_u32 resp_len) {
    volatile spl_u16 *used_idx;
    spl_u16 start;
    if ((!g_rt_gpu_modern && !g_rt_gpu_bar0) || !g_rt_gpu_cmd || !g_rt_gpu_resp || g_rt_gpu_qsize < 2) {
        return -1;
    }
    rt_desc_write(g_rt_gpu_desc, 0, g_rt_gpu_cmd, req_len, RT_VIRTQ_DESC_F_NEXT, 1);
    rt_desc_write(g_rt_gpu_desc, 1, g_rt_gpu_resp, resp_len, RT_VIRTQ_DESC_F_WRITE, 0);
    rt_memzero((void *)g_rt_gpu_resp, resp_len);
    rt_avail_push(g_rt_gpu_avail, g_rt_gpu_qsize, 0);
    used_idx = (volatile spl_u16 *)(g_rt_gpu_used + 2ULL);
    start = *used_idx;
    __sync_synchronize();
    if (g_rt_gpu_modern) {
        rt_mmio_write16_raw(g_rt_gpu_notify + ((spl_u64)g_rt_gpu_notify_off * (spl_u64)g_rt_gpu_notify_multiplier), 0);
    } else {
        rt_io_write16(g_rt_gpu_bar0, RT_VIRTIO_PCI_QUEUE_NOTIFY, 0);
    }
    for (spl_u64 polls = 0; polls < 1000000ULL; polls = polls + 1) {
        __sync_synchronize();
        if (*used_idx != start) {
            g_rt_gpu_last_used = *used_idx;
            return (spl_i64)rt_get_le32((const spl_u8 *)g_rt_gpu_resp);
        }
    }
    (void)cmd;
    return -2;
}

static spl_i64 rt_gpu_find_modern_caps(RtPciDevice *dev) {
    spl_u8 cap = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x34) & 0xfcU;
    spl_u64 bar_base[6];
    for (spl_u64 i = 0; i < 6; i = i + 1) {
        bar_base[i] = 0;
    }
    bar_base[1] = RT_PCI_MMIO_BASE + ((spl_u64)dev->device * 0x100000ULL);
    bar_base[4] = RT_PCI_MMIO_BASE + ((spl_u64)dev->device * 0x100000ULL) + 0x10000ULL;
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x14, (spl_u32)bar_base[1]);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x20, (spl_u32)bar_base[4]);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x24, 0);
    rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
    while (cap >= 0x40U && cap != 0xffU) {
        spl_u8 cap_id = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap);
        spl_u8 next = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 1U) & 0xfcU;
        if (cap_id == RT_PCI_CAP_ID_VENDOR_SPECIFIC) {
            spl_u8 cfg_type = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 3U);
            spl_u8 bar = rt_pci_read_config8((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 4U);
            spl_u32 offset = rt_pci_read_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 8U);
            if (bar < 6U && bar_base[bar] != 0) {
                if (cfg_type == RT_VIRTIO_PCI_CAP_COMMON_CFG) {
                    g_rt_gpu_common = bar_base[bar] + offset;
                } else if (cfg_type == RT_VIRTIO_PCI_CAP_NOTIFY_CFG) {
                    g_rt_gpu_notify = bar_base[bar] + offset;
                    g_rt_gpu_notify_multiplier = rt_pci_read_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, cap + 16U);
                }
            }
        }
        if (next == 0 || next == cap) {
            break;
        }
        cap = next;
    }
    if (g_rt_gpu_common == 0 || g_rt_gpu_notify == 0 || g_rt_gpu_notify_multiplier == 0) {
        return -1;
    }
    return 0;
}

static spl_i64 rt_gpu_setup_modern(RtPciDevice *dev) {
    spl_u16 max_size;
    spl_u16 size;
    spl_u64 total;
    spl_u64 pages;
    spl_u64 ring;
    spl_u64 desc_avail;
    if (rt_gpu_find_modern_caps(dev) < 0) {
        return -1;
    }
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, 0);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT, 0);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE, 0);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE_SELECT, 1);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DRIVER_FEATURE, 1);
    rt_mmio_write8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
    if ((rt_mmio_read8_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
        return -2;
    }
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SELECT, 0);
    if (rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_NUM_QUEUES) == 0) {
        return -3;
    }
    max_size = rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SIZE);
    if (max_size == 0) {
        return -4;
    }
    size = max_size > RT_GPU_QUEUE_CAP ? RT_GPU_QUEUE_CAP : max_size;
    total = rt_virtqueue_total_size(size);
    pages = (total + 4095ULL) / 4096ULL;
    ring = rt_alloc_contiguous_pages(pages);
    if (ring == 0) {
        return -5;
    }
    rt_memzero((void *)ring, pages * 4096ULL);
    desc_avail = rt_virtqueue_desc_size(size) + rt_virtqueue_avail_size(size);
    g_rt_gpu_desc = ring;
    g_rt_gpu_avail = ring + rt_virtqueue_desc_size(size);
    g_rt_gpu_used = ring + ((desc_avail + 4095ULL) & ~4095ULL);
    g_rt_gpu_qsize = size;
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_SIZE, size);
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DESC_LO, (spl_u32)(g_rt_gpu_desc & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DESC_HI, (spl_u32)(g_rt_gpu_desc >> 32));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DRIVER_LO, (spl_u32)(g_rt_gpu_avail & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DRIVER_HI, (spl_u32)(g_rt_gpu_avail >> 32));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DEVICE_LO, (spl_u32)(g_rt_gpu_used & 0xffffffffULL));
    rt_mmio_write32_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_DEVICE_HI, (spl_u32)(g_rt_gpu_used >> 32));
    g_rt_gpu_notify_off = rt_mmio_read16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_NOTIFY_OFF);
    rt_mmio_write16_raw(g_rt_gpu_common + RT_VIRTIO_MODERN_QUEUE_ENABLE, 1);
    rt_mmio_write8_raw(
        g_rt_gpu_common + RT_VIRTIO_MODERN_DEVICE_STATUS,
        RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
    );
    g_rt_gpu_modern = 1;
    return 0;
}

static spl_i64 rt_gpu_cmd_get_display_info(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    spl_i64 resp;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_GET_DISPLAY_INFO);
    resp = rt_gpu_send_command(RT_GPU_CMD_GET_DISPLAY_INFO, 24U, 408U);
    if (resp == RT_GPU_RESP_OK_DISPLAY_INFO) {
        return 0;
    }
    if (resp < 0) {
        return resp;
    }
    return -3;
}

static spl_i64 rt_gpu_cmd_resource_create(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_CREATE_2D);
    rt_put_le32(cmd + 24, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 28, RT_GPU_FORMAT_B8G8R8A8_UNORM);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_CREATE_2D, 40U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_attach_backing(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_ATTACH_BACKING);
    rt_put_le32(cmd + 24, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 28, 1U);
    rt_put_le64(cmd + 32, g_rt_gpu_fb);
    rt_put_le32(cmd + 40, RT_GPU_WIDTH * RT_GPU_HEIGHT * 4U);
    rt_put_le32(cmd + 44, 0U);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_ATTACH_BACKING, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_set_scanout(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_SET_SCANOUT);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le32(cmd + 40, 0U);
    rt_put_le32(cmd + 44, RT_GPU_RESOURCE_ID);
    return rt_gpu_send_command(RT_GPU_CMD_SET_SCANOUT, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static spl_i64 rt_gpu_cmd_transfer_flush(void) {
    spl_u8 *cmd = (spl_u8 *)g_rt_gpu_cmd;
    spl_i64 resp;
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_TRANSFER_TO_HOST_2D);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le64(cmd + 40, 0ULL);
    rt_put_le32(cmd + 48, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 52, 0U);
    resp = rt_gpu_send_command(RT_GPU_CMD_TRANSFER_TO_HOST_2D, 56U, 24U);
    if (resp != RT_GPU_RESP_OK_NODATA) {
        return -1;
    }
    rt_gpu_ctrl_hdr(cmd, RT_GPU_CMD_RESOURCE_FLUSH);
    rt_put_le32(cmd + 24, 0U);
    rt_put_le32(cmd + 28, 0U);
    rt_put_le32(cmd + 32, RT_GPU_WIDTH);
    rt_put_le32(cmd + 36, RT_GPU_HEIGHT);
    rt_put_le32(cmd + 40, RT_GPU_RESOURCE_ID);
    rt_put_le32(cmd + 44, 0U);
    return rt_gpu_send_command(RT_GPU_CMD_RESOURCE_FLUSH, 48U, 24U) == RT_GPU_RESP_OK_NODATA ? 0 : -1;
}

static void rt_gpu_fill_test_pattern(void) {
    volatile spl_u32 *fb = (volatile spl_u32 *)g_rt_gpu_fb;
    for (spl_u32 y = 0; y < RT_GPU_HEIGHT; y = y + 1U) {
        for (spl_u32 x = 0; x < RT_GPU_WIDTH; x = x + 1U) {
            spl_u8 r = (spl_u8)(x & 0xffU);
            spl_u8 g = (spl_u8)(y & 0xffU);
            spl_u8 b = (spl_u8)((x ^ y) & 0xffU);
            fb[(spl_u64)y * RT_GPU_WIDTH + x] = 0xff000000U | ((spl_u32)r << 16) | ((spl_u32)g << 8) | (spl_u32)b;
        }
    }
}

spl_i64 rt_display_init(void) {
    spl_i64 count = rt_pci_device_count();
    for (spl_i64 i = 0; i < count; i = i + 1) {
        spl_i64 cls = rt_pci_get_field(i, 3);
        spl_i64 sub = rt_pci_get_field(i, 4);
        spl_i64 vendor = rt_pci_get_field(i, 5);
        spl_i64 device_id = rt_pci_get_field(i, 6);
        if (rt_pci_is_virtio_gpu(cls, sub, vendor, device_id)) {
            RtPciDevice *dev = &g_rt_pci_devices[i];
            g_rt_gpu_modern = 0;
            if (device_id == RT_VIRTIO_GPU_MODERN_DEVICE_ID) {
                if (rt_gpu_setup_modern(dev) < 0) {
                    g_rt_display_ready = 0;
                    return -2;
                }
            } else {
                rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x10, (spl_u32)(RT_PCI_LEGACY_GPU_IO_PORT | 1ULL));
                rt_pci_write_config32((spl_u64)dev->bus, (spl_u64)dev->device, (spl_u64)dev->function, 0x04, RT_PCI_CMD_IO | RT_PCI_CMD_MEM | RT_PCI_CMD_BUS_MASTER);
                g_rt_gpu_bar0 = RT_PCI_IO_BASE + RT_PCI_LEGACY_GPU_IO_PORT;
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, 0);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER);
                rt_io_write32(g_rt_gpu_bar0, RT_VIRTIO_PCI_GUEST_FEATURES, 0);
                rt_io_write8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS, RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK);
                if ((rt_io_read8(g_rt_gpu_bar0, RT_VIRTIO_PCI_STATUS) & RT_VIRTIO_STATUS_FEATURES_OK) == 0) {
                    g_rt_display_ready = 0;
                    return -3;
                }
                if (rt_setup_virtqueue_capped(g_rt_gpu_bar0, 0, RT_GPU_QUEUE_CAP, &g_rt_gpu_desc, &g_rt_gpu_avail, &g_rt_gpu_used, &g_rt_gpu_qsize) < 0) {
                    g_rt_display_ready = 0;
                    return -4;
                }
                rt_io_write8(
                    g_rt_gpu_bar0,
                    RT_VIRTIO_PCI_STATUS,
                    RT_VIRTIO_STATUS_ACKNOWLEDGE | RT_VIRTIO_STATUS_DRIVER | RT_VIRTIO_STATUS_FEATURES_OK | RT_VIRTIO_STATUS_DRIVER_OK
                );
            }
            g_rt_gpu_cmd = rt_riscv_noalloc_alloc_page();
            g_rt_gpu_resp = rt_riscv_noalloc_alloc_page();
            g_rt_gpu_fb = rt_alloc_contiguous_pages((RT_GPU_WIDTH * RT_GPU_HEIGHT * 4ULL + 4095ULL) / 4096ULL);
            if (!g_rt_gpu_cmd || !g_rt_gpu_resp || !g_rt_gpu_fb) {
                g_rt_display_ready = 0;
                return -5;
            }
            rt_memzero((void *)g_rt_gpu_cmd, 4096ULL);
            rt_memzero((void *)g_rt_gpu_resp, 4096ULL);
            rt_memzero((void *)g_rt_gpu_fb, RT_GPU_WIDTH * RT_GPU_HEIGHT * 4ULL);
            spl_i64 display_info_rc = rt_gpu_cmd_get_display_info();
            if (display_info_rc < 0) {
                g_rt_display_ready = 0;
                return -610 + display_info_rc;
            }
            if (rt_gpu_cmd_resource_create() < 0) {
                g_rt_display_ready = 0;
                return -62;
            }
            if (rt_gpu_cmd_attach_backing() < 0) {
                g_rt_display_ready = 0;
                return -63;
            }
            if (rt_gpu_cmd_set_scanout() < 0) {
                g_rt_display_ready = 0;
                return -64;
            }
            g_rt_display_ready = 1;
            return 0;
        }
    }
    g_rt_display_ready = 0;
    return -1;
}

spl_i64 rt_display_flush_test(void) {
    if (!g_rt_display_ready || !g_rt_gpu_fb) {
        return -1;
    }
    rt_gpu_fill_test_pattern();
    return rt_gpu_cmd_transfer_flush();
}

spl_i64 rt_display_width(void) {
    return g_rt_display_ready ? RT_GPU_WIDTH : 0;
}

spl_i64 rt_display_height(void) {
    return g_rt_display_ready ? RT_GPU_HEIGHT : 0;
}
