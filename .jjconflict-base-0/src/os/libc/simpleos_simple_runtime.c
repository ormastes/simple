/*
 * Minimal Simple runtime ABI for SimpleOS user programs.
 *
 * This is intentionally small: it covers the value/string/print surface needed
 * for the first target-native SimpleOS hello-world binaries. Broader compiler
 * self-hosting must replace or extend this with the full Simple runtime ABI.
 */

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <unistd.h>

#define RT_VALUE_TAG_MASK 0x7ULL
#define RT_VALUE_TAG_INT 0x0ULL
#define RT_VALUE_TAG_HEAP 0x1ULL
#define RT_VALUE_TAG_SPECIAL 0x3ULL
#define RT_VALUE_SPECIAL_NIL 0x0ULL
#define RT_VALUE_SPECIAL_TRUE 0x1ULL
#define RT_VALUE_SPECIAL_FALSE 0x2ULL
#define RT_HEAP_STRING 0x01U

typedef int64_t spl_i64;
typedef uint64_t spl_u64;
typedef uint32_t spl_u32;
typedef uint8_t spl_u8;

typedef struct RtHeapHeader {
    spl_u8 object_type;
    spl_u8 gc_flags;
    uint16_t reserved;
    spl_u32 size;
} RtHeapHeader;

typedef struct RtString {
    RtHeapHeader header;
    spl_u64 len;
    spl_u64 hash;
    char data[];
} RtString;

static spl_i64 rt_special(spl_u64 value) {
    return (spl_i64)((value << 3) | RT_VALUE_TAG_SPECIAL);
}

static spl_i64 rt_heap(void *ptr) {
    return (spl_i64)(((spl_u64)(uintptr_t)ptr) | RT_VALUE_TAG_HEAP);
}

static RtHeapHeader *rt_as_heap(spl_i64 value) {
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) {
        return NULL;
    }
    return (RtHeapHeader *)(uintptr_t)(((spl_u64)value) & ~RT_VALUE_TAG_MASK);
}

static RtString *rt_as_string(spl_i64 value) {
    RtHeapHeader *header = rt_as_heap(value);
    if (!header || header->object_type != RT_HEAP_STRING) {
        return NULL;
    }
    return (RtString *)header;
}

void *rt_alloc(spl_i64 size) {
    if (size <= 0) {
        return NULL;
    }
    return malloc((size_t)size);
}

void rt_free(void *ptr, spl_i64 size) {
    (void)size;
    free(ptr);
}

spl_i64 rt_nil(void) {
    return rt_special(RT_VALUE_SPECIAL_NIL);
}

spl_i64 rt_value_int(spl_i64 value) {
    return value << 3;
}

spl_i64 rt_value_bool(spl_i64 value) {
    return rt_special(value ? RT_VALUE_SPECIAL_TRUE : RT_VALUE_SPECIAL_FALSE);
}

spl_i64 rt_string_new(spl_i64 bytes_value, spl_i64 len_value) {
    const spl_u8 *bytes = (const spl_u8 *)(uintptr_t)bytes_value;
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

spl_i64 rt_string_len(spl_i64 value) {
    RtString *string = rt_as_string(value);
    return string ? (spl_i64)string->len : 0;
}

spl_i64 rt_string_data(spl_i64 value) {
    RtString *string = rt_as_string(value);
    return string ? (spl_i64)(uintptr_t)string->data : 0;
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
            return rt_string_new((spl_i64)(uintptr_t)buf, (spl_i64)(len + 1));
        }
        rt_write_decimal(buf, &len, (spl_u64)signed_value);
        return rt_string_new((spl_i64)(uintptr_t)buf, (spl_i64)len);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) {
        return rt_string_new((spl_i64)(uintptr_t)"true", 4);
    }
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) {
        return rt_string_new((spl_i64)(uintptr_t)"false", 5);
    }
    if (value == rt_nil()) {
        return rt_string_new((spl_i64)(uintptr_t)"nil", 3);
    }
    return rt_string_new((spl_i64)(uintptr_t)"<value>", 7);
}

static void rt_write_value(spl_i64 value) {
    RtString *string = rt_as_string(value);
    spl_i64 rendered;
    if (!string) {
        rendered = rt_to_string(value);
        string = rt_as_string(rendered);
    }
    if (string && string->len > 0) {
        (void)write(1, string->data, (size_t)string->len);
    }
}

void rt_print_value(spl_i64 value) {
    rt_write_value(value);
}

void rt_println_value(spl_i64 value) {
    rt_write_value(value);
    (void)write(1, "\n", 1);
}

void rt_print_str(spl_i64 value) {
    rt_print_value(value);
}

void rt_println_str(spl_i64 value) {
    rt_println_value(value);
}

void rt_print(const char *value) {
    if (!value) return;
    const char *end = value;
    while (*end) end++;
    (void)write(1, value, (size_t)(end - value));
}

void rt_println(const char *value) {
    rt_print(value);
    (void)write(1, "\n", 1);
}

void rt_eprint_value(spl_i64 value) {
    RtString *string = rt_as_string(value);
    spl_i64 rendered;
    if (!string) {
        rendered = rt_to_string(value);
        string = rt_as_string(rendered);
    }
    if (string && string->len > 0) {
        (void)write(2, string->data, (size_t)string->len);
    }
}

void rt_eprintln_value(spl_i64 value) {
    rt_eprint_value(value);
    (void)write(2, "\n", 1);
}

spl_i64 rt_pool_safepoint(void) {
    return 0;
}

void __simple_runtime_init(void) {}
void __simple_runtime_shutdown(void) {}
void __simple_call_module_inits(void) {}
