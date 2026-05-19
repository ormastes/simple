/*
 * Simple Native Runtime Bridge
 *
 * Provides the rt_* symbols that the LLVM IR backend declares via
 * generate_runtime_declarations_for_target(). Each function bridges
 * to the corresponding spl_* implementation in runtime.c or to libc.
 *
 * Also provides __simple_runtime_init() and __simple_runtime_shutdown()
 * called by the entry point wrapper (entry_point.spl).
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I. -Iplatform runtime_native.c -o runtime_native.o
 */

/* Only include runtime.h for spl_* declarations — platform functions
 * (rt_dir_create, rt_sleep_ms_native, etc.) are already compiled via
 * runtime.c + platform headers. We must NOT include platform/platform.h
 * here to avoid duplicate symbol definitions. */
#include "runtime.h"
#include "runtime_simd_dispatch.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/stat.h>

#define RT_VALUE_TAG_MASK 0x7ULL
#define RT_VALUE_TAG_INT 0x0ULL
#define RT_VALUE_TAG_HEAP 0x1ULL
#define RT_VALUE_TAG_FLOAT 0x2ULL
#define RT_VALUE_TAG_SPECIAL 0x3ULL
#define RT_VALUE_SPECIAL_NIL 0x0ULL
#define RT_VALUE_SPECIAL_TRUE 0x1ULL
#define RT_VALUE_SPECIAL_FALSE 0x2ULL
#define RT_VALUE_HEAP_STRING 0x53545231U
#define RT_VALUE_HEAP_ARRAY 0x02U
#define RT_VALUE_HEAP_ENUM 0x04U
#define RT_CORE_ARRAY_FLAG_BYTES 0x08U
#define RT_CORE_ARRAY_FLAG_U64_PACKED 0x10U

typedef struct RtCoreString {
    uint32_t kind;
    uint32_t reserved;
    uint64_t len;
    char data[];
} RtCoreString;

typedef struct RtCoreArray {
    uint8_t kind;
    uint8_t flags;
    uint8_t reserved[6];
    int64_t len;
    int64_t cap;
    void* data;
} RtCoreArray;

typedef struct RtCoreEnum {
    uint8_t kind;
    uint8_t reserved[3];
    uint32_t enum_id;
    uint32_t discriminant;
    uint32_t reserved2;
    int64_t payload;
} RtCoreEnum;

static RtCoreString** rt_core_string_registry = NULL;
static size_t rt_core_string_registry_len = 0;
static size_t rt_core_string_registry_cap = 0;

static void rt_core_register_string(RtCoreString* s) {
    if (!s) return;
    if (rt_core_string_registry_len == rt_core_string_registry_cap) {
        size_t next_cap = rt_core_string_registry_cap == 0 ? 64 : rt_core_string_registry_cap * 2;
        RtCoreString** next = (RtCoreString**)realloc(rt_core_string_registry, next_cap * sizeof(RtCoreString*));
        if (!next) return;
        rt_core_string_registry = next;
        rt_core_string_registry_cap = next_cap;
    }
    rt_core_string_registry[rt_core_string_registry_len++] = s;
}

static int rt_core_is_registered_string(RtCoreString* s) {
    for (size_t i = 0; i < rt_core_string_registry_len; i++) {
        if (rt_core_string_registry[i] == s) return 1;
    }
    return 0;
}

static inline int64_t rt_core_from_special(uint64_t payload) {
    return (int64_t)((payload << 3) | RT_VALUE_TAG_SPECIAL);
}

static inline int64_t rt_core_nil(void) {
    return rt_core_from_special(RT_VALUE_SPECIAL_NIL);
}

static inline int rt_core_is_int(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT;
}

static inline int rt_core_is_heap(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP;
}

static inline int rt_core_is_float(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_FLOAT;
}

static inline int rt_core_is_special(int64_t value) {
    return (((uint64_t)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_SPECIAL;
}

static inline int64_t rt_core_as_int(int64_t value) {
    return value >> 3;
}

static inline uint64_t rt_core_special_payload(int64_t value) {
    return ((uint64_t)value) >> 3;
}

static inline int64_t rt_core_numeric_arg(int64_t value) {
    uint64_t raw = (uint64_t)value;
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT && raw >= 8) {
        return (int64_t)(raw >> 3);
    }
    return value;
}

static inline RtCoreString* rt_core_as_string(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    RtCoreString* s = (RtCoreString*)(raw & ~RT_VALUE_TAG_MASK);
    if (!rt_core_is_registered_string(s)) return NULL;
    if (!s || s->kind != RT_VALUE_HEAP_STRING) return NULL;
    return s;
}

static inline RtCoreArray* rt_core_as_array(int64_t value) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096) return NULL;
    if ((raw & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_HEAP) {
        raw &= ~RT_VALUE_TAG_MASK;
    } else if ((raw & RT_VALUE_TAG_MASK) != 0) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)raw;
    if (a->kind != RT_VALUE_HEAP_ARRAY) return NULL;
    if (a->len < 0 || a->cap < 0 || a->len > a->cap || a->cap > 100000000) return NULL;
    return a;
}

static inline RtCoreEnum* rt_core_as_enum(int64_t value) {
    if (!rt_core_is_heap(value)) return NULL;
    RtCoreEnum* e = (RtCoreEnum*)(uintptr_t)(((uint64_t)value) & ~RT_VALUE_TAG_MASK);
    if (!e || e->kind != RT_VALUE_HEAP_ENUM) return NULL;
    return e;
}

static inline RtCoreArray* rt_core_array_ptr(SplArray* value) {
    return rt_core_as_array((int64_t)(uintptr_t)value);
}

static int8_t rt_core_array_reserve(SplArray* a, int64_t min_cap);

static void rt_core_write_bytes(FILE* stream, const uint8_t* ptr, uint64_t len) {
    if (!ptr || len == 0) return;
    fwrite(ptr, 1, (size_t)len, stream);
}

static void rt_core_print_value_to(FILE* stream, int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stream, (const uint8_t*)s->data, s->len);
        return;
    }

    if (rt_core_is_int(value)) {
        fprintf(stream, "%lld", (long long)rt_core_as_int(value));
        return;
    }

    if (rt_core_is_special(value)) {
        switch (rt_core_special_payload(value)) {
            case RT_VALUE_SPECIAL_NIL:
                return;
            case RT_VALUE_SPECIAL_TRUE:
                fputs("true", stream);
                return;
            case RT_VALUE_SPECIAL_FALSE:
                fputs("false", stream);
                return;
            default:
                fprintf(stream, "<special:%llu>", (unsigned long long)rt_core_special_payload(value));
                return;
        }
    }

    fprintf(stream, "<value:0x%llx>", (unsigned long long)(uint64_t)value);
}

/* ================================================================
 * I/O Operations
 * ================================================================ */

void rt_print(const char* s) {
    spl_print(s);
}

void rt_println(const char* s) {
    spl_println(s);
}

char* rt_readline(void) {
    char buf[4096];
    if (fgets(buf, sizeof(buf), stdin)) {
        /* Strip trailing newline */
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        return spl_str_new(buf);
    }
    return spl_str_new("");
}

char* rt_stdin_read_line(void) {
    char buf[4096];
    if (fgets(buf, sizeof(buf), stdin)) {
        size_t len = strlen(buf);
        if (len > 0 && buf[len - 1] == '\n') buf[len - 1] = '\0';
        return spl_str_new(buf);
    }
    return NULL; /* EOF */
}

int64_t stdin_read_char(void) {
    int ch = fgetc(stdin);
    if (ch == EOF) {
        return rt_string_new(NULL, 0);
    }
    uint8_t byte = (uint8_t)ch;
    return rt_string_new(&byte, 1);
}

int64_t rt_stdout_write_text(const char* s) {
    if (!s) return 0;
    int64_t len = (int64_t)strlen(s);
    fputs(s, stdout);
    return len;
}

int64_t print_raw(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fflush(stdout);
    return 0;
}

int64_t rt_stdout_write(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stdout, (const uint8_t*)s->data, s->len);
        return (int64_t)s->len;
    }
    rt_core_print_value_to(stdout, value);
    return 0;
}

void rt_stdout_flush(void) {
    fflush(stdout);
}

int64_t rt_stderr_write(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) {
        rt_core_write_bytes(stderr, (const uint8_t*)s->data, s->len);
        return (int64_t)s->len;
    }
    rt_core_print_value_to(stderr, value);
    return 0;
}

void rt_stderr_flush(void) {
    fflush(stderr);
}

int64_t rt_value_int(int64_t value) {
    return (int64_t)(((uint64_t)value << 3) | RT_VALUE_TAG_INT);
}

int64_t rt_value_float(int64_t raw_bits) {
    return (int64_t)(((uint64_t)raw_bits & ~RT_VALUE_TAG_MASK) | RT_VALUE_TAG_FLOAT);
}

int64_t rt_value_bool(int64_t value) {
    return rt_core_from_special(value ? RT_VALUE_SPECIAL_TRUE : RT_VALUE_SPECIAL_FALSE);
}

int64_t rt_value_nil(void) {
    return rt_core_nil();
}

int64_t rt_function_not_found(const uint8_t* name, uint64_t len) {
    fputs("Simple runtime error: function not found", stderr);
    if (name && len > 0) {
        fputs(": ", stderr);
        fwrite(name, 1, (size_t)len, stderr);
    }
    fputc('\n', stderr);
    return rt_core_nil();
}

int64_t rt_interp_call(const uint8_t* name, uint64_t len, int64_t argc, int64_t argv) {
    (void)argc;
    (void)argv;
    return rt_function_not_found(name, len);
}

int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    if (!bytes && len > 0) return rt_core_nil();

    RtCoreString* s = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)len + 1);
    if (!s) return rt_core_nil();
    s->kind = RT_VALUE_HEAP_STRING;
    s->reserved = 0;
    s->len = len;
    if (len > 0 && bytes) {
        memcpy(s->data, bytes, (size_t)len);
    }
    s->data[len] = '\0';
    rt_core_register_string(s);
    return (int64_t)(((uint64_t)(uintptr_t)s) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_len(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    return s ? (int64_t)s->len : -1;
}

const uint8_t* rt_string_data(int64_t string) {
    RtCoreString* s = rt_core_as_string(string);
    return s ? (const uint8_t*)s->data : NULL;
}

int64_t rt_string_char_code_at(int64_t string, int64_t index) {
    RtCoreString* s = rt_core_as_string(string);
    if (!s || index < 0 || (uint64_t)index >= s->len) return 0;
    return (int64_t)(uint8_t)s->data[index];
}

int64_t rt_string_concat(int64_t left, int64_t right) {
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    int64_t left_text = left;
    int64_t right_text = right;
    if (!a) {
        left_text = rt_to_string(left);
        a = rt_core_as_string(left_text);
    }
    if (!b) {
        right_text = rt_to_string(right);
        b = rt_core_as_string(right_text);
    }
    if (!a || !b) return rt_core_nil();

    uint64_t len = a->len + b->len;
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = len;
    if (a->len > 0) memcpy(out->data, a->data, (size_t)a->len);
    if (b->len > 0) memcpy(out->data + a->len, b->data, (size_t)b->len);
    out->data[len] = '\0';
    rt_core_register_string(out);
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

/// Runtime dispatch for `any + any`: if either operand is a heap string, perform
/// string concatenation; otherwise perform integer arithmetic addition.
/// This matches the interpreter's BinOp::Add behaviour for ANY-typed operands.
int64_t rt_any_add(int64_t left, int64_t right) {
    if (rt_core_as_string(left) || rt_core_as_string(right)) {
        return rt_string_concat(left, right);
    }
    return left + right;
}

int64_t rt_len(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) return (int64_t)s->len;
    RtCoreArray* a = rt_core_as_array(value);
    return a ? a->len : 0;
}

int64_t rt_to_string(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (s) return value;

    char buf[64];
    if (rt_core_is_int(value)) {
        int64_t n = (int64_t)((uint64_t)value >> 3);
        int len = snprintf(buf, sizeof(buf), "%lld", (long long)n);
        return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
    }
    if (rt_core_is_float(value)) {
        uint64_t bits = ((uint64_t)value) & ~RT_VALUE_TAG_MASK;
        double f;
        memcpy(&f, &bits, sizeof(f));
        int len = snprintf(buf, sizeof(buf), "%.17g", f);
        return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
    }
    if (rt_core_is_special(value)) {
        switch (rt_core_special_payload(value)) {
            case RT_VALUE_SPECIAL_TRUE:
                return rt_string_new((const uint8_t*)"true", 4);
            case RT_VALUE_SPECIAL_FALSE:
                return rt_string_new((const uint8_t*)"false", 5);
            case RT_VALUE_SPECIAL_NIL:
            default:
                return rt_string_new(NULL, 0);
        }
    }
    int len = snprintf(buf, sizeof(buf), "<value:0x%llx>", (unsigned long long)(uint64_t)value);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

int64_t rt_raw_u64_to_string(int64_t raw) {
    char buf[32];
    int len = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)(uint64_t)raw);
    return rt_string_new((const uint8_t*)buf, len > 0 ? (uint64_t)len : 0);
}

int64_t rt_value_to_string(int64_t value) {
    return rt_to_string(value);
}

int64_t rt_native_eq(int64_t left, int64_t right) {
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    if (a || b) {
        if (!a || !b || a->len != b->len) return 0;
        return a->len == 0 || memcmp(a->data, b->data, (size_t)a->len) == 0;
    }
    return left == right;
}

int64_t rt_string_eq(int64_t left, int64_t right) {
    RtCoreString* a = rt_core_as_string(left);
    RtCoreString* b = rt_core_as_string(right);
    if (!a || !b || a->len != b->len) return 0;
    return a->len == 0 || memcmp(a->data, b->data, (size_t)a->len) == 0;
}

int64_t rt_text_eq_fast(int64_t left, int64_t right) {
    return rt_string_eq(left, right);
}

int64_t rt_native_neq(int64_t left, int64_t right) {
    return !rt_native_eq(left, right);
}

int64_t rt_slice(int64_t value, int64_t start, int64_t end, int64_t step) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return rt_core_nil();
    int64_t len = (int64_t)s->len;
    int64_t begin = start;
    int64_t finish = end;
    int64_t stride = step;
    if (stride == 0) stride = 1;
    if (begin < 0) begin += len;
    if (finish < 0) finish += len;
    if (begin < 0) begin = 0;
    if (finish < begin) finish = begin;
    if (begin > len) begin = len;
    if (finish > len) finish = len;
    if (stride != 1) {
        uint64_t out_len = 0;
        for (int64_t i = begin; i < finish; i += stride) out_len++;
        RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)out_len + 1);
        if (!out) return rt_core_nil();
        out->kind = RT_VALUE_HEAP_STRING;
        out->reserved = 0;
        out->len = out_len;
        uint64_t out_i = 0;
        for (int64_t i = begin; i < finish; i += stride) out->data[out_i++] = s->data[i];
        out->data[out_len] = '\0';
        rt_core_register_string(out);
        return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
    }
    return rt_string_new((const uint8_t*)s->data + begin, (uint64_t)(finish - begin));
}

int64_t rt_string_starts_with(int64_t value, int64_t prefix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(prefix);
    if (!s || !p || p->len > s->len) return 0;
    return p->len == 0 || memcmp(s->data, p->data, (size_t)p->len) == 0;
}

int64_t rt_string_ends_with(int64_t value, int64_t suffix) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* p = rt_core_as_string(suffix);
    if (!s || !p || p->len > s->len) return 0;
    return p->len == 0 || memcmp(s->data + (s->len - p->len), p->data, (size_t)p->len) == 0;
}

int64_t rt_string_replace(int64_t value, int64_t old_value, int64_t new_value) {
    RtCoreString* s = rt_core_as_string(value);
    RtCoreString* old_s = rt_core_as_string(old_value);
    RtCoreString* new_s = rt_core_as_string(new_value);
    if (!s || !old_s || !new_s) return value;
    if (old_s->len == 0) return value;

    uint64_t count = 0;
    for (uint64_t i = 0; i + old_s->len <= s->len;) {
        if (memcmp(s->data + i, old_s->data, (size_t)old_s->len) == 0) {
            count++;
            i += old_s->len;
        } else {
            i++;
        }
    }
    if (count == 0) return value;
    uint64_t out_len = s->len;
    if (new_s->len >= old_s->len) {
        out_len += count * (new_s->len - old_s->len);
    } else {
        out_len -= count * (old_s->len - new_s->len);
    }
    RtCoreString* out = (RtCoreString*)malloc(sizeof(RtCoreString) + (size_t)out_len + 1);
    if (!out) return rt_core_nil();
    out->kind = RT_VALUE_HEAP_STRING;
    out->reserved = 0;
    out->len = out_len;
    uint64_t in_i = 0;
    uint64_t out_i = 0;
    while (in_i < s->len) {
        if (in_i + old_s->len <= s->len && memcmp(s->data + in_i, old_s->data, (size_t)old_s->len) == 0) {
            if (new_s->len > 0) memcpy(out->data + out_i, new_s->data, (size_t)new_s->len);
            out_i += new_s->len;
            in_i += old_s->len;
        } else {
            out->data[out_i++] = s->data[in_i++];
        }
    }
    out->data[out_len] = '\0';
    rt_core_register_string(out);
    return (int64_t)(((uint64_t)(uintptr_t)out) | RT_VALUE_TAG_HEAP);
}

int64_t rt_string_trim(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return value;
    uint64_t begin = 0;
    uint64_t end = s->len;
    while (begin < end && (s->data[begin] == ' ' || s->data[begin] == '\t' || s->data[begin] == '\n' || s->data[begin] == '\r')) {
        begin++;
    }
    while (end > begin && (s->data[end - 1] == ' ' || s->data[end - 1] == '\t' || s->data[end - 1] == '\n' || s->data[end - 1] == '\r')) {
        end--;
    }
    return rt_string_new((const uint8_t*)s->data + begin, end - begin);
}

int64_t rt_string_to_int(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    char buf[64];
    uint64_t n = s->len < sizeof(buf) - 1 ? s->len : sizeof(buf) - 1;
    if (n > 0) memcpy(buf, s->data, (size_t)n);
    buf[n] = '\0';
    return (int64_t)strtoll(buf, NULL, 10);
}

void rt_print_str(const uint8_t* ptr, uint64_t len) {
    rt_core_write_bytes(stdout, ptr, len);
    fflush(stdout);
}

void rt_println_str(const uint8_t* ptr, uint64_t len) {
    rt_print_str(ptr, len);
    fputc('\n', stdout);
    fflush(stdout);
}

void rt_eprint_str(const uint8_t* ptr, uint64_t len) {
    rt_core_write_bytes(stderr, ptr, len);
    fflush(stderr);
}

void rt_eprintln_str(const uint8_t* ptr, uint64_t len) {
    rt_eprint_str(ptr, len);
    fputc('\n', stderr);
    fflush(stderr);
}

void rt_print_value(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fflush(stdout);
}

void rt_println_value(int64_t value) {
    rt_core_print_value_to(stdout, value);
    fputc('\n', stdout);
    fflush(stdout);
}

void rt_eprint_value(int64_t value) {
    rt_core_print_value_to(stderr, value);
    fflush(stderr);
}

void rt_eprintln_value(int64_t value) {
    rt_core_print_value_to(stderr, value);
    fputc('\n', stderr);
    fflush(stderr);
}

void rt_set_args(int argc, char** argv) {
    spl_init_args(argc, argv);
}

int32_t rt_get_argc(void) {
    return (int32_t)spl_arg_count();
}

SplArray* rt_get_args(void) {
    return rt_cli_get_args();
}

/* ================================================================
 * Memory Operations
 * ================================================================ */

void* rt_alloc(int64_t size) {
    return spl_malloc(size);
}

void* rt_realloc(void* ptr, int64_t size) {
    return realloc(ptr, (size_t)size);
}

void rt_free(void* ptr) {
    spl_free(ptr);
}

void* rt_memcpy(void* dst, const void* src, int64_t n) {
    return memcpy(dst, src, (size_t)n);
}

void* rt_memset(void* dst, int8_t val, int64_t n) {
    return memset(dst, (int)val, (size_t)n);
}

int64_t rt_memcmp(const void* a, const void* b, int64_t n) {
    return (int64_t)memcmp(a, b, (size_t)n);
}

/* ================================================================
 * DMA Operations (hosted fallback — FR-DRIVER-0005)
 * ================================================================
 *
 * Baremetal supplies rt_dma_* via src/runtime/startup/baremetal/dma.c
 * + dma_<arch>.c. The hosted path is functional-not-coherent: we
 * page-align via posix_memalign so drivers that expect page-aligned
 * DMA buffers run in unit tests, and sync ops collapse to a compiler
 * barrier because userspace talks to simulated devices via memcpy.
 */

#define RT_DMA_HOST_MAX_SLOTS 32
#define RT_DMA_HOST_PAGE_SIZE 4096

struct rt_dma_host_slot {
    void    *virt;
    int64_t  size;
    int      in_use;
};

static struct rt_dma_host_slot g_rt_dma_host_slots[RT_DMA_HOST_MAX_SLOTS];

/* posix_memalign is in POSIX-2001; declare explicitly so this file
 * compiles under strict `-std=c11` without a feature-test macro. */
extern int posix_memalign(void **memptr, size_t alignment, size_t size);

int64_t rt_dma_alloc(int64_t size, int32_t dir_raw) {
    (void)dir_raw;
    if (size <= 0) return -1;

    int slot = -1;
    for (int i = 0; i < RT_DMA_HOST_MAX_SLOTS; i++) {
        if (!g_rt_dma_host_slots[i].in_use) { slot = i; break; }
    }
    if (slot < 0) return -1;

    void *p = NULL;
    if (posix_memalign(&p, RT_DMA_HOST_PAGE_SIZE, (size_t)size) != 0 || !p) {
        return -1;
    }
    g_rt_dma_host_slots[slot].virt   = p;
    g_rt_dma_host_slots[slot].size   = size;
    g_rt_dma_host_slots[slot].in_use = 1;
    return (int64_t)slot;
}

void rt_dma_free(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_HOST_MAX_SLOTS) return;
    if (g_rt_dma_host_slots[handle].in_use) {
        free(g_rt_dma_host_slots[handle].virt);
    }
    g_rt_dma_host_slots[handle].virt   = NULL;
    g_rt_dma_host_slots[handle].size   = 0;
    g_rt_dma_host_slots[handle].in_use = 0;
}

int64_t rt_dma_virt_of(int64_t handle) {
    if (handle < 0 || handle >= RT_DMA_HOST_MAX_SLOTS) return 0;
    if (!g_rt_dma_host_slots[handle].in_use) return 0;
    return (int64_t)(uintptr_t)g_rt_dma_host_slots[handle].virt;
}

int64_t rt_dma_phys_of(int64_t handle) {
    /* Userspace has no physical addresses; return virt so drivers
     * that program a DMA-physical register at least see a stable,
     * unique address. Not safe for real hardware — by design. */
    return rt_dma_virt_of(handle);
}

void rt_dma_sync_for_device(int64_t handle, int32_t dir_raw) {
    (void)handle;
    (void)dir_raw;
    __asm__ volatile ("" ::: "memory");  /* compiler barrier only */
}

void rt_dma_sync_for_cpu(int64_t handle, int32_t dir_raw) {
    (void)handle;
    (void)dir_raw;
    __asm__ volatile ("" ::: "memory");
}

int64_t rt_dma_cache_line_size(void) {
    /* 64 B is the x86_64 / arm64 default and covers every current
     * hosted development target. Real baremetal overrides this via
     * the per-arch dma_<arch>.c. */
    return 64;
}

/* ================================================================
 * String Operations
 * ================================================================ */

int64_t rt_strlen(const char* s) {
    return spl_str_len(s);
}

char* rt_strcat(const char* a, const char* b) {
    return spl_str_concat(a, b);
}

char* rt_substr(const char* s, int64_t start, int64_t len) {
    return spl_str_slice(s, start, start + len);
}

int64_t rt_strfind(const char* s, const char* needle) {
    return spl_str_index_of(s, needle);
}

char* rt_strreplace(const char* s, const char* old_s, const char* new_s) {
    return spl_str_replace(s, old_s, new_s);
}

SplArray* rt_strsplit(const char* s, const char* delim) {
    return spl_str_split(s, delim);
}

int64_t rt_strcmp(const char* a, const char* b) {
    return (int64_t)spl_str_cmp(a, b);
}

/* ================================================================
 * Array Operations
 * ================================================================ */

static SplArray* rt_core_array_new(int64_t cap, uint8_t flags) {
    int64_t actual_cap = cap > 4 ? cap : 4;
    if (actual_cap < 0 || actual_cap > INT64_MAX / (int64_t)sizeof(int64_t)) {
        return NULL;
    }
    RtCoreArray* a = (RtCoreArray*)calloc(1, sizeof(RtCoreArray));
    if (!a) return NULL;
    a->kind = RT_VALUE_HEAP_ARRAY;
    a->flags = flags;
    a->cap = actual_cap;
    size_t elem_size = (flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t);
    a->data = calloc((size_t)actual_cap, elem_size);
    if (!a->data) {
        free(a);
        return NULL;
    }
    return (SplArray*)(((uintptr_t)a) | RT_VALUE_TAG_HEAP);
}

SplArray* rt_array_new(int64_t cap) {
    return rt_core_array_new(cap, 0);
}

SplArray* rt_array_new_with_cap_u64(int64_t cap) {
    return rt_core_array_new(cap, RT_CORE_ARRAY_FLAG_U64_PACKED);
}

SplArray* rt_byte_array_new(uint64_t cap) {
    if (cap > (uint64_t)INT64_MAX) {
        return NULL;
    }
    return rt_core_array_new((int64_t)cap, RT_CORE_ARRAY_FLAG_BYTES);
}

int64_t rt_array_len(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? array->len : 0;
}

int64_t rt_array_get(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 3;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 3;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        return (int64_t)((uint8_t*)array->data)[idx];
    }
    return ((int64_t*)array->data)[idx];
}

void rt_array_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[idx] = (uint8_t)(val & 0xff);
    } else {
        ((int64_t*)array->data)[idx] = val;
    }
}

int8_t rt_array_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    if (array->flags & RT_CORE_ARRAY_FLAG_BYTES) {
        ((uint8_t*)array->data)[array->len++] = (uint8_t)(val & 0xff);
    } else {
        ((int64_t*)array->data)[array->len++] = val;
    }
    return 1;
}

int64_t rt_array_data_ptr(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? (int64_t)(uintptr_t)array->data : 0;
}

int64_t rt_array_header_ptr(SplArray* a) {
    RtCoreArray* array = rt_core_array_ptr(a);
    return array ? (int64_t)(uintptr_t)array : 0;
}

int8_t rt_array_set_len_known(int64_t header_ptr, int64_t len) {
    RtCoreArray* array = rt_core_as_array(header_ptr);
    if (!array || len < 0 || len > array->cap) return 0;
    array->len = len;
    return 1;
}

static int8_t rt_core_array_reserve(SplArray* a, int64_t min_cap) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (array->cap >= min_cap) return 1;
    int64_t new_cap = array->cap > 0 ? array->cap : 4;
    while (new_cap < min_cap) {
        if (new_cap > INT64_MAX / 2) return 0;
        new_cap *= 2;
    }
    size_t elem_size = (array->flags & RT_CORE_ARRAY_FLAG_BYTES) ? sizeof(uint8_t) : sizeof(int64_t);
    void* data = realloc(array->data, (size_t)new_cap * elem_size);
    if (!data) {
        array->len = 0;
        array->cap = 0;
        return 0;
    }
    array->data = data;
    array->cap = new_cap;
    return 1;
}

int64_t rt_bytes_u8_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    return (int64_t)((uint8_t*)array->data)[idx];
}

int64_t rt_bytes_u32_le_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx + 4 > array->len) return 0;
    uint8_t* bytes = (uint8_t*)array->data;
    uint64_t v = (uint64_t)bytes[idx]
        | ((uint64_t)bytes[idx + 1] << 8)
        | ((uint64_t)bytes[idx + 2] << 16)
        | ((uint64_t)bytes[idx + 3] << 24);
    return (int64_t)v;
}

int64_t rt_bytes_u64_le_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx + 8 > array->len) return 0;
    uint8_t* bytes = (uint8_t*)array->data;
    uint64_t v = 0;
    for (int shift = 0; shift < 8; shift++) {
        v |= ((uint64_t)bytes[idx + shift]) << (shift * 8);
    }
    return (int64_t)v;
}

int8_t rt_bytes_u8_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    ((uint8_t*)array->data)[idx] = (uint8_t)(val & 0xff);
    return 1;
}

int8_t rt_typed_bytes_u8_push(SplArray* a, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    if (!rt_core_array_reserve(a, array->len + 1)) return 0;
    ((uint8_t*)array->data)[array->len++] = (uint8_t)(val & 0xff);
    return 1;
}

int64_t rt_typed_bytes_u8_unchecked(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    return (int64_t)((uint8_t*)array->data)[rt_core_numeric_arg(idx)];
}

int64_t rt_typed_bytes_u32_le_at(SplArray* a, int64_t idx) {
    return rt_bytes_u32_le_at(a, idx);
}

int64_t rt_typed_bytes_u64_le_at(SplArray* a, int64_t idx) {
    return rt_bytes_u64_le_at(a, idx);
}

int64_t rt_typed_bytes_u64_le_unchecked(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    uint8_t* bytes = (uint8_t*)array->data;
    uint64_t v = 0;
    for (int shift = 0; shift < 8; shift++) {
        v |= ((uint64_t)bytes[idx + shift]) << (shift * 8);
    }
    return (int64_t)v;
}

int8_t rt_typed_bytes_u32_le_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0 || idx + 4 > array->len) return 0;
    uint8_t* bytes = (uint8_t*)array->data;
    uint32_t v = (uint32_t)val;
    bytes[idx] = (uint8_t)(v & 0xff);
    bytes[idx + 1] = (uint8_t)((v >> 8) & 0xff);
    bytes[idx + 2] = (uint8_t)((v >> 16) & 0xff);
    bytes[idx + 3] = (uint8_t)((v >> 24) & 0xff);
    return 1;
}

int8_t rt_typed_bytes_u64_le_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0 || idx + 8 > array->len) return 0;
    uint8_t* bytes = (uint8_t*)array->data;
    uint64_t v = (uint64_t)val;
    for (int shift = 0; shift < 8; shift++) {
        bytes[idx + shift] = (uint8_t)((v >> (shift * 8)) & 0xff);
    }
    return 1;
}

int64_t rt_typed_words_u32_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    return ((int64_t*)array->data)[idx] & 0xffffffffLL;
}

int8_t rt_typed_words_u32_push(SplArray* a, int64_t val) {
    return rt_array_push(a, val & 0xffffffffLL);
}

int8_t rt_typed_words_u32_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] = val & 0xffffffffLL;
    return 1;
}

int64_t rt_typed_words_u64_at(SplArray* a, int64_t idx) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    return ((int64_t*)array->data)[idx];
}

int8_t rt_typed_words_u64_push(SplArray* a, int64_t val) {
    return rt_array_push(a, val);
}

int8_t rt_typed_words_u64_set(SplArray* a, int64_t idx, int64_t val) {
    RtCoreArray* array = rt_core_array_ptr(a);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0) idx = array->len + idx;
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] = val;
    return 1;
}

int64_t rt_typed_words_u64_raw_data_at(int64_t data_ptr, int64_t idx) {
    if (data_ptr == 0 || idx < 0) return 0;
    return ((int64_t*)(uintptr_t)data_ptr)[idx];
}

int8_t rt_typed_words_u64_store_known_data_at(
    int64_t header_ptr,
    int64_t data_ptr,
    int64_t idx,
    int64_t val) {
    RtCoreArray* array = rt_core_as_array(header_ptr);
    if (!array || data_ptr == 0 || idx < 0 || idx >= array->cap) return 0;
    ((int64_t*)(uintptr_t)data_ptr)[idx] = val;
    return 1;
}

int64_t rt_tuple_new(int64_t len) {
    SplArray* tuple = rt_array_new(len);
    if (!tuple) return rt_core_nil();
    RtCoreArray* array = rt_core_array_ptr(tuple);
    if (!array) return rt_core_nil();
    array->len = len < 0 ? 0 : len;
    return (int64_t)(uintptr_t)tuple;
}

int8_t rt_tuple_set(int64_t tuple, int64_t idx, int64_t value) {
    RtCoreArray* array = rt_core_as_array(tuple);
    if (!array) return 0;
    idx = rt_core_numeric_arg(idx);
    if (idx < 0 || idx >= array->len) return 0;
    ((int64_t*)array->data)[idx] = value;
    return 1;
}

int64_t rt_tuple_get(int64_t tuple, int64_t idx) {
    RtCoreArray* array = rt_core_as_array(tuple);
    if (!array) return rt_core_nil();
    idx = rt_core_numeric_arg(idx);
    if (idx < 0 || idx >= array->len) return rt_core_nil();
    return ((int64_t*)array->data)[idx];
}

int64_t rt_tuple_len(int64_t tuple) {
    RtCoreArray* array = rt_core_as_array(tuple);
    return array ? array->len : -1;
}

int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload) {
    RtCoreEnum* value = (RtCoreEnum*)calloc(1, sizeof(RtCoreEnum));
    if (!value) return rt_core_nil();
    value->kind = RT_VALUE_HEAP_ENUM;
    value->enum_id = (uint32_t)enum_id;
    value->discriminant = (uint32_t)discriminant;
    value->payload = payload;
    return (int64_t)(((uint64_t)(uintptr_t)value) | RT_VALUE_TAG_HEAP);
}

int64_t rt_enum_discriminant(int64_t value) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e ? (int64_t)e->discriminant : -1;
}

int64_t rt_enum_payload(int64_t value) {
    RtCoreEnum* e = rt_core_as_enum(value);
    return e ? e->payload : rt_core_nil();
}

int64_t rt_hash_text(int64_t value) {
    RtCoreString* s = rt_core_as_string(value);
    if (!s) return 0;
    uint64_t hash = 1469598103934665603ULL;
    for (uint64_t i = 0; i < s->len; i++) {
        hash ^= (uint8_t)s->data[i];
        hash *= 1099511628211ULL;
    }
    return (int64_t)hash;
}

SplValue* rt_array_pop(SplArray* a) {
    static SplValue tmp;
    tmp = spl_array_pop(a);
    return &tmp;
}

int64_t rt_index_get(int64_t collection, int64_t idx) {
    RtCoreArray* a = rt_core_as_array(collection);
    if (a) return rt_array_get((SplArray*)a, idx);
    return 3;
}

int8_t rt_index_set(int64_t collection, int64_t idx, int64_t val) {
    RtCoreArray* a = rt_core_as_array(collection);
    if (!a) return 0;
    rt_array_set((SplArray*)a, idx, val);
    return 1;
}

/* ================================================================
 * Dict Operations
 * ================================================================ */

SplDict* rt_dict_new(void) {
    return spl_dict_new();
}

SplValue* rt_dict_get(SplDict* d, const char* key) {
    static SplValue tmp;
    tmp = spl_dict_get(d, key);
    return &tmp;
}

void rt_dict_set(SplDict* d, const char* key, SplValue* val) {
    if (val) {
        spl_dict_set(d, key, *val);
    }
}

int rt_dict_contains(SplDict* d, const char* key) {
    return spl_dict_contains(d, key);
}

int64_t rt_dict_len(SplDict* d) {
    return spl_dict_len(d);
}

/* ================================================================
 * File I/O (wrappers around existing rt_/spl_ functions)
 * ================================================================ */

/* rt_file_read_text, rt_file_exists, rt_file_write, rt_file_delete,
 * rt_file_copy, rt_file_size, rt_file_stat, rt_file_append
 * are already defined in runtime.c */

void* rt_file_open(const char* path, const char* mode) {
    if (!path || !mode) return NULL;
    return (void*)fopen(path, mode);
}

void rt_file_close(void* handle) {
    if (handle) fclose((FILE*)handle);
}

int rt_file_move(const char* src, const char* dst) {
    if (!src || !dst) return 0;
    return rename(src, dst) == 0 ? 1 : 0;
}

char* rt_env_cwd(void) {
    return rt_getcwd();
}

const char* rt_platform_name(void) {
#if defined(_WIN32)
    return "windows";
#elif defined(__APPLE__)
    return "macos";
#elif defined(__FreeBSD__)
    return "freebsd";
#elif defined(__linux__)
    return "linux";
#else
    return "unknown";
#endif
}

int rt_file_write_text(const char* path, const char* content) {
    return rt_file_write(path, content);
}

int rt_file_append_text(const char* path, const char* content) {
    return rt_file_append(path, content);
}

static int rt_core_mkdir_one(const char* path) {
    if (!path || !*path) return 0;
    if (mkdir(path, 0777) == 0) return 1;
    return rt_is_dir(path) ? 1 : 0;
}

int rt_dir_create_all(const char* path) {
    if (!path || !*path) return 0;
    char* copy = spl_strdup(path);
    if (!copy) return 0;

    char* p = copy;
    if (p[0] == '/') p++;
    for (; *p; p++) {
        if (*p == '/') {
            *p = '\0';
            if (!rt_core_mkdir_one(copy)) {
                free(copy);
                return 0;
            }
            *p = '/';
        }
    }

    int ok = rt_core_mkdir_one(copy);
    free(copy);
    return ok;
}

int rt_mkdir_p(const char* path) {
    return rt_dir_create_all(path);
}

const char* lib__nogc_sync_mut__debug__remote__session_model__DebugExecutionMode_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "rtl_sim";
        case 2: return "qemu_stub";
        default: return "hw";
    }
}

const char* lib__nogc_sync_mut__debug__remote__session_model__DebugTransportKind_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "openocd_remote_bitbang";
        case 2: return "intel_jtagd";
        case 3: return "trace32_native";
        case 4: return "trace32_gdb";
        case 5: return "gdb_remote";
        default: return "openocd_jtag";
    }
}

const char* lib__nogc_sync_mut__debug__remote__types__Architecture_dot_to_string(int64_t value) {
    switch (value) {
        case 1: return "arm64";
        case 2: return "riscv32";
        case 3: return "riscv64";
        case 4: return "x86";
        case 5: return "x86_64";
        default: return "arm32";
    }
}

static char* rt_core_shell_quote(const char* s) {
    if (!s) return spl_strdup("''");
    size_t extra = 2;
    for (const char* p = s; *p; p++) {
        extra += (*p == '\'') ? 4 : 1;
    }
    char* out = (char*)malloc(extra + 1);
    if (!out) return spl_strdup("''");
    char* w = out;
    *w++ = '\'';
    for (const char* p = s; *p; p++) {
        if (*p == '\'') {
            memcpy(w, "'\\''", 4);
            w += 4;
        } else {
            *w++ = *p;
        }
    }
    *w++ = '\'';
    *w = '\0';
    return out;
}

SplArray* rt_process_run(const char* cmd, SplArray* args) {
    SplArray* result = spl_array_new_cap(3);
    if (!cmd || !*cmd) {
        spl_array_push(result, spl_str(""));
        spl_array_push(result, spl_str("missing command"));
        spl_array_push(result, spl_int(-1));
        return result;
    }

    char* command = rt_core_shell_quote(cmd);
    int64_t argc = spl_array_len(args);
    for (int64_t i = 0; i < argc; i++) {
        SplValue arg = spl_array_get(args, i);
        const char* arg_s = arg.tag == SPL_STRING ? spl_as_str(arg) : "";
        char* quoted = rt_core_shell_quote(arg_s);
        size_t new_len = strlen(command) + strlen(quoted) + 2;
        char* joined = (char*)malloc(new_len);
        if (!joined) {
            free(quoted);
            continue;
        }
        snprintf(joined, new_len, "%s %s", command, quoted);
        free(command);
        free(quoted);
        command = joined;
    }

    char* redirected = spl_str_concat(command, " 2>/tmp/simple_core_process_run_stderr");
    FILE* pipe = popen(redirected ? redirected : command, "r");
    free(command);
    if (redirected) free(redirected);
    if (!pipe) {
        spl_array_push(result, spl_str(""));
        spl_array_push(result, spl_str("process spawn failed"));
        spl_array_push(result, spl_int(-1));
        return result;
    }

    size_t cap = 4096;
    size_t len = 0;
    char* stdout_buf = (char*)malloc(cap);
    if (!stdout_buf) stdout_buf = spl_strdup("");
    if (stdout_buf) stdout_buf[0] = '\0';
    char chunk[512];
    while (fgets(chunk, sizeof(chunk), pipe)) {
        size_t chunk_len = strlen(chunk);
        if (len + chunk_len + 1 > cap) {
            while (len + chunk_len + 1 > cap) cap *= 2;
            stdout_buf = (char*)realloc(stdout_buf, cap);
            if (!stdout_buf) break;
        }
        memcpy(stdout_buf + len, chunk, chunk_len);
        len += chunk_len;
        stdout_buf[len] = '\0';
    }
    int status = pclose(pipe);
    int exit_code = status == -1 ? -1 : (status >> 8);

    spl_array_push(result, spl_str(stdout_buf ? stdout_buf : ""));
    spl_array_push(result, spl_str(""));
    spl_array_push(result, spl_int(exit_code));
    if (stdout_buf) free(stdout_buf);
    return result;
}

char* rt_file_read_bytes(const char* path) {
    /* Reads file into a buffer; for native linking, returns raw bytes as char* */
    return spl_file_read(path);
}

int rt_file_write_bytes(const char* path, const void* data, int64_t len) {
    if (!path || !data) return 0;
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    size_t written = fwrite(data, 1, (size_t)len, f);
    fclose(f);
    return written == (size_t)len ? 1 : 0;
}

/* IF-13 wave-4d: truncate (or zero-extend) `path` to exactly `size` bytes.
 * Used by SimpleOS disk-image bake to push the multi-MiB zero-fill into the
 * kernel rather than building a giant byte-array in the interpreter. */
int rt_file_truncate(const char* path, uint64_t size) {
    if (!path) return 0;
    int fd = open(path, O_WRONLY | O_CREAT, 0644);
    if (fd < 0) return 0;
    int rc = ftruncate(fd, (off_t)size);
    close(fd);
    return rc == 0 ? 1 : 0;
}

SplArray* rt_bytes_from_raw(int64_t ptr, int64_t len) {
    /* Create a byte array ([u8]) from a raw memory pointer.
     * Used by LLVM memory buffer emission to avoid temp file I/O. */
    if (ptr == 0 || len <= 0) return spl_array_new();
    SplArray* arr = spl_array_new_cap(len);
    const unsigned char* src = (const unsigned char*)(uintptr_t)ptr;
    for (int64_t i = 0; i < len; i++) {
        spl_array_push_i64(arr, (int64_t)src[i]);
    }
    return arr;
}

/* ================================================================
 * Directory Operations (bridge to spl_ or direct libc)
 * ================================================================ */

/* rt_dir_create is already in runtime.h (takes path + recursive) but
 * LLVM IR declares it as rt_dir_create(ptr) -> i1 (single arg).
 * Provide the single-arg version. */
int rt_dir_delete(const char* path) {
    return rt_dir_remove_all(path) ? 1 : 0;
}

int rt_dir_exists(const char* path) {
    return rt_is_dir(path) ? 1 : 0;
}

/* ================================================================
 * Process / Environment
 * ================================================================ */

void* rt_process_spawn(const char* cmd, const char** args, int64_t arg_count) {
    /* Delegate to rt_process_spawn_async which returns pid as i64 */
    int64_t pid = rt_process_spawn_async(cmd, args, arg_count);
    return (void*)(intptr_t)pid;
}

const char* rt_getenv(const char* key) {
    return spl_env_get(key);
}

int rt_setenv(const char* key, const char* value) {
    return rt_env_set(key, value) ? 1 : 0;
}

void rt_exit(int64_t code) {
    exit((int)code);
}

/* ================================================================
 * Time Operations
 * ================================================================ */

int64_t rt_time_now_unix(void) {
    return (int64_t)time(NULL);
}

int64_t rt_entropy_hardware_ready(void) {
    return 0;
}

int64_t rt_time_now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}

void rt_sleep_ms(int64_t ms) {
    rt_sleep_ms_native(ms);
}

/* ================================================================
 * Math Operations
 * ================================================================ */

double rt_sin(double x) { return sin(x); }
double rt_cos(double x) { return cos(x); }
double rt_sqrt(double x) { return sqrt(x); }
double rt_pow(double a, double b) { return pow(a, b); }

/* ================================================================
 * Pointer Read/Write Operations (for relocation patching, FFI interop)
 * ================================================================ */

int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) {
    int64_t* ptr = (int64_t*)((char*)(uintptr_t)addr + offset);
    return *ptr;
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    uint8_t* ptr = (uint8_t*)((char*)(uintptr_t)addr + offset);
    *ptr = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    int32_t* ptr = (int32_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    int64_t* ptr = (int64_t*)((char*)(uintptr_t)addr + offset);
    *ptr = value;
}

/* ================================================================
 * Error Handling
 * ================================================================ */

void rt_panic(const char* msg) {
    spl_panic(msg);
}

/* ================================================================
 * Reserved-Field Cache Helpers for RtCoreString
 *
 * Bit layout (see runtime_simd_dispatch.h for constants):
 *   Bit 31     = is-ASCII validity flag
 *   Bit 30     = cp-count validity flag
 *   Bit 29     = is-ASCII value (meaningful only when bit 31 = 1)
 *   Bits [28:0] = codepoint count (meaningful only when bit 30 = 1)
 * ================================================================ */

void rt_str_cache_cp_count(RtCoreString* s, uint64_t count) {
    if (!s) return;
    if (count > SIMD_CACHE_CPCOUNT_MASK) return;
    uint32_t r = s->reserved;
    r |= SIMD_CACHE_FLAG_CPCOUNT_VALID;
    r = (r & ~SIMD_CACHE_CPCOUNT_MASK) | ((uint32_t)count & SIMD_CACHE_CPCOUNT_MASK);
    s->reserved = r;
}

int64_t rt_str_cached_cp_count(RtCoreString* s) {
    if (!s) return -1;
    if (!(s->reserved & SIMD_CACHE_FLAG_CPCOUNT_VALID)) return -1;
    return (int64_t)(s->reserved & SIMD_CACHE_CPCOUNT_MASK);
}

void rt_str_set_ascii_flag(RtCoreString* s, int is_ascii) {
    if (!s) return;
    if (is_ascii)
        s->reserved |= SIMD_CACHE_FLAG_IS_ASCII;
    /* Non-ASCII: don't cache (positive-only flag per spec) */
}

int rt_str_is_ascii_cached(RtCoreString* s) {
    if (!s) return -1;
    if (s->reserved & SIMD_CACHE_FLAG_IS_ASCII) return 1;
    return -1; /* unknown (could be ASCII or not) */
}

/* ================================================================
 * Runtime Lifecycle (called by entry point)
 * ================================================================ */

void __simple_runtime_init(void) {
    /* Initialize SIMD text dispatch table */
    simd_text_init();
}

void __simple_runtime_shutdown(void) {
    /* Cleanup runtime resources */
    /* Flush stdout/stderr to ensure all output is visible */
    fflush(stdout);
    fflush(stderr);
}
