/*
 * baremetal_stubs.c -- RISC-V 32-bit baremetal runtime stubs (COMPLETE)
 *
 * Provides the FULL Simple runtime support needed for SimpleOS to boot
 * in QEMU with serial output.
 *
 * NOTE: On RV32, pointers are 32-bit. The heap is 4MB (not 16MB)
 * to fit in typical RV32 QEMU virt RAM (128MB at 0x80000000).
 * All pointer casts use uintptr_t (not uint64_t).
 *
 * Sections:
 *   1. Serial I/O (16550 UART at MMIO 0x10000000)
 *   2. RuntimeValue tagging system (32-bit)
 *   3. Heap allocator (4MB bump)
 *   4. String operations
 *   5. Print functions
 *   6. Memory primitives
 *   7. Framebuffer helpers
 *   8. MMIO accessors (real implementations)
 *   9. Array / comparison operations
 *  10. _start entry point
 *  11. ~200 no-op runtime stubs
 */

#include <stddef.h>
#include <stdint.h>

/* ================================================================
 * 1. Serial I/O -- 16550 UART at MMIO 0x10000000 (QEMU virt machine)
 * ================================================================ */

#define UART_BASE       0x10000000UL

#define UART_THR        (*(volatile uint8_t *)(UART_BASE + 0))  /* Transmit Holding Register */
#define UART_RBR        (*(volatile uint8_t *)(UART_BASE + 0))  /* Receive Buffer Register */
#define UART_IER        (*(volatile uint8_t *)(UART_BASE + 1))  /* Interrupt Enable Register */
#define UART_FCR        (*(volatile uint8_t *)(UART_BASE + 2))  /* FIFO Control Register */
#define UART_LCR        (*(volatile uint8_t *)(UART_BASE + 3))  /* Line Control Register */
#define UART_MCR        (*(volatile uint8_t *)(UART_BASE + 4))  /* Modem Control Register */
#define UART_LSR        (*(volatile uint8_t *)(UART_BASE + 5))  /* Line Status Register */

#define UART_LSR_THRE   0x20  /* Transmit Holding Register Empty */
#define UART_LSR_DR     0x01  /* Data Ready */
#define UART_LCR_DLAB   0x80  /* Divisor Latch Access Bit */

static int g_serial_inited = 0;

static void _uart_init(void) {
    if (g_serial_inited) return;
    *(volatile uint8_t *)(UART_BASE + 1) = 0x00;  /* Disable all interrupts */
    *(volatile uint8_t *)(UART_BASE + 3) = 0x80;  /* Enable DLAB */
    *(volatile uint8_t *)(UART_BASE + 0) = 0x01;  /* Divisor low byte (115200 baud) */
    *(volatile uint8_t *)(UART_BASE + 1) = 0x00;  /* Divisor high byte */
    *(volatile uint8_t *)(UART_BASE + 3) = 0x03;  /* 8 bits, no parity, 1 stop bit (8N1) */
    *(volatile uint8_t *)(UART_BASE + 2) = 0x07;  /* Enable FIFO, clear, 1-byte threshold */
    *(volatile uint8_t *)(UART_BASE + 4) = 0x00;  /* No modem control */
    g_serial_inited = 1;
}

static void serial_putchar(char c) {
    _uart_init();
    while (!(UART_LSR & UART_LSR_THRE)) {}
    UART_THR = (uint8_t)c;
}

static void serial_puts(const char *s) {
    while (*s) {
        if (*s == '\n') serial_putchar('\r');
        serial_putchar(*s++);
    }
}

/* ================================================================
 * 2. RuntimeValue tagging system (32-bit)
 *
 * On RV32, RuntimeValue is int32_t (4 bytes).
 * 3-bit tag in LSB, 29-bit payload for integers.
 * Pointers must be 8-byte aligned so lower 3 bits are free.
 * ================================================================ */

typedef int32_t RuntimeValue;

#define TAG_MASK     0x7U
#define TAG_INT      0x0U
#define TAG_HEAP     0x1U
#define TAG_SPECIAL  0x3U

#define ENCODE_INT(v)   ((RuntimeValue)(((uint32_t)(int32_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v)   ((int32_t)((uint32_t)(v) >> 3))
#define ENCODE_PTR(p)   ((RuntimeValue)((uint32_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)   ((void*)((uint32_t)(v) & ~TAG_MASK))
#define IS_INT(v)       (((uint32_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)      (((uint32_t)(v) & TAG_MASK) == TAG_HEAP)
#define IS_SPECIAL(v)   (((uint32_t)(v) & TAG_MASK) == TAG_SPECIAL)

#define NIL_VALUE       ((RuntimeValue)TAG_SPECIAL)
#define TRUE_VALUE      ((RuntimeValue)(0x8U | TAG_SPECIAL))
#define FALSE_VALUE     ((RuntimeValue)(0x10U | TAG_SPECIAL))

typedef struct { uint32_t type; uint32_t size; } HeapHeader;
typedef struct { HeapHeader header; uint32_t len; char data[]; } RuntimeString;
typedef struct { HeapHeader header; uint32_t len; uint32_t cap; RuntimeValue data[]; } RuntimeArray;
typedef struct { HeapHeader header; double value; } RuntimeFloat;

#define HEAP_TYPE_STRING  1
#define HEAP_TYPE_ARRAY   2
#define HEAP_TYPE_OBJECT  3
#define HEAP_TYPE_FLOAT   4
#define HEAP_TYPE_ENUM    7

#define IS_NIL(v) ((v) == NIL_VALUE)

typedef struct {
    HeapHeader   header;
    uint32_t     enum_id;
    uint32_t     discriminant;
    RuntimeValue payload;
} RuntimeEnum;

/* ================================================================
 * 3. Heap allocator -- 4MB bump allocator, 8-byte aligned
 * (Smaller than 64-bit targets to fit RV32 memory constraints)
 * ================================================================ */

static char _heap[4 * 1024 * 1024]; /* 4 MB */
static size_t _heap_offset = 0;

void *malloc(size_t size) {
    /* Align to 8 bytes to keep lower 3 bits free for tagging */
    size = (size + 7) & ~(size_t)7;
    if (_heap_offset + size > sizeof(_heap)) return 0;
    void *ptr = &_heap[_heap_offset];
    _heap_offset += size;
    return ptr;
}

void free(void *ptr) {
    (void)ptr; /* bump allocator -- no reclaim */
}

void *realloc(void *ptr, size_t new_size) {
    void *new_ptr = malloc(new_size);
    if (ptr && new_ptr) __builtin_memcpy(new_ptr, ptr, new_size);
    return new_ptr;
}

void *calloc(size_t n, size_t size) {
    size_t total = n * size;
    void *ptr = malloc(total);
    if (ptr) __builtin_memset(ptr, 0, total);
    return ptr;
}

RuntimeValue rt_alloc(RuntimeValue size) {
    /* size is raw (untagged) per the Rust runtime ABI. */
    size_t bytes = (size_t)size;
    if (bytes == 0 || bytes > 0x1000000) return NIL_VALUE;
    void *p = malloc(bytes);
    if (!p) return NIL_VALUE;
    return ENCODE_PTR(p);
}

RuntimeValue rt_box_float(double value) {
    RuntimeFloat *f = (RuntimeFloat *)malloc(sizeof(RuntimeFloat));
    if (!f) return NIL_VALUE;
    f->header.type = HEAP_TYPE_FLOAT;
    f->header.size = (uint32_t)sizeof(RuntimeFloat);
    f->value = value;
    return ENCODE_PTR(f);
}

double rt_unbox_float(RuntimeValue value) {
    if (IS_INT(value)) {
        return (double)DECODE_INT(value);
    }
    if (!IS_HEAP(value)) {
        return 0.0;
    }
    RuntimeFloat *f = (RuntimeFloat *)DECODE_PTR(value);
    if (f->header.type != HEAP_TYPE_FLOAT) {
        return 0.0;
    }
    return f->value;
}

static double _rv32_double_from_u32(uint32_t value, uint32_t sign_bit) {
    if (value == 0) return 0.0;

    int highest = 0;
    uint32_t scan = value;
    while (scan >>= 1) highest++;

    uint64_t exponent = (uint64_t)(highest + 1023);
    uint64_t mantissa = ((uint64_t)value) << (52 - highest);
    uint64_t bits = ((uint64_t)sign_bit << 32) | (exponent << 52) | (mantissa & 0x000fffffffffffffULL);
    union { uint64_t bits; double value; } out;
    out.bits = bits;
    return out.value;
}

double __floatsidf(int32_t value) {
    if (value < 0) {
        uint32_t magnitude = (uint32_t)(-(int64_t)value);
        return _rv32_double_from_u32(magnitude, 0x80000000U);
    }
    return _rv32_double_from_u32((uint32_t)value, 0);
}

double __floatunsidf(uint32_t value) {
    return _rv32_double_from_u32(value, 0);
}

/* ================================================================
 * 4. String operations
 * ================================================================ */

RuntimeValue rt_string_new(RuntimeValue data_ptr, RuntimeValue len_val) {
    /* Parameters are raw (untagged) per the Rust runtime ABI.
       len_val is the raw byte count, data_ptr is a raw pointer. */
    int32_t len = len_val;
    if (len < 0 || len > 0x100000) return NIL_VALUE;
    if (len == 0) {
        /* Empty string — allocate a valid string object (not NIL) */
        RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + 1);
        if (!s) return NIL_VALUE;
        s->header.type = HEAP_TYPE_STRING;
        s->header.size = (uint32_t)(sizeof(RuntimeString) + 1);
        s->len = 0;
        s->data[0] = 0;
        return ENCODE_PTR(s);
    }
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + (size_t)len + 1);
    if (!s) return NIL_VALUE;
    s->header.type = HEAP_TYPE_STRING;
    s->header.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    s->len = (uint32_t)len;
    /* data_ptr is a raw pointer cast to i32 */
    const char *src = (const char *)(uintptr_t)data_ptr;
    if (src) __builtin_memcpy(s->data, src, (size_t)len);
    s->data[len] = 0;
    return ENCODE_PTR(s);
}

RuntimeValue rt_string_from_cstr(const char *cstr) {
    if (!cstr) return NIL_VALUE;
    size_t len = 0;
    while (cstr[len]) len++;
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + len + 1);
    if (!s) return NIL_VALUE;
    s->header.type = HEAP_TYPE_STRING;
    s->header.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    s->len = (uint32_t)len;
    __builtin_memcpy(s->data, cstr, len);
    s->data[len] = 0;
    return ENCODE_PTR(s);
}

RuntimeValue rt_string_len(RuntimeValue str) {
    if (!IS_HEAP(str)) return ENCODE_INT(0);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (s->header.type != HEAP_TYPE_STRING) return ENCODE_INT(0);
    return ENCODE_INT(s->len);
}

RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx_val) {
    if (!IS_HEAP(str)) return ENCODE_INT(0);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int32_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int32_t)s->len) return ENCODE_INT(0);
    return ENCODE_INT((uint8_t)s->data[idx]);
}

RuntimeValue rt_string_concat(RuntimeValue a, RuntimeValue b) {
    uint32_t la = 0, lb = 0;
    const char *da = "", *db = "";
    if (IS_HEAP(a)) {
        RuntimeString *sa = (RuntimeString *)DECODE_PTR(a);
        if (sa->header.type == HEAP_TYPE_STRING) { la = sa->len; da = sa->data; }
    }
    if (IS_HEAP(b)) {
        RuntimeString *sb = (RuntimeString *)DECODE_PTR(b);
        if (sb->header.type == HEAP_TYPE_STRING) { lb = sb->len; db = sb->data; }
    }
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + la + lb + 1);
    if (!r) return NIL_VALUE;
    r->header.type = HEAP_TYPE_STRING;
    r->header.size = (uint32_t)(sizeof(RuntimeString) + la + lb + 1);
    r->len = la + lb;
    __builtin_memcpy(r->data, da, la);
    __builtin_memcpy(r->data + la, db, lb);
    r->data[la + lb] = 0;
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_slice(RuntimeValue str, RuntimeValue start_val, RuntimeValue end_val) {
    if (!IS_HEAP(str)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int32_t start = DECODE_INT(start_val);
    int32_t end = DECODE_INT(end_val);
    if (start < 0) start = 0;
    if (end > (int32_t)s->len) end = s->len;
    if (start >= end) {
        RuntimeString *empty = (RuntimeString *)malloc(sizeof(RuntimeString) + 1);
        if (!empty) return NIL_VALUE;
        empty->header.type = HEAP_TYPE_STRING;
        empty->header.size = (uint32_t)(sizeof(RuntimeString) + 1);
        empty->len = 0;
        empty->data[0] = 0;
        return ENCODE_PTR(empty);
    }
    int32_t len = end - start;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + (size_t)len + 1);
    if (!r) return NIL_VALUE;
    r->header.type = HEAP_TYPE_STRING;
    r->header.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    r->len = (uint32_t)len;
    __builtin_memcpy(r->data, s->data + start, (size_t)len);
    r->data[len] = 0;
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_eq(RuntimeValue a, RuntimeValue b) {
    if (!IS_HEAP(a) || !IS_HEAP(b)) return ENCODE_INT(a == b ? 1 : 0);
    RuntimeString *sa = (RuntimeString *)DECODE_PTR(a);
    RuntimeString *sb = (RuntimeString *)DECODE_PTR(b);
    if (sa->len != sb->len) return ENCODE_INT(0);
    for (uint32_t i = 0; i < sa->len; i++) {
        if (sa->data[i] != sb->data[i]) return ENCODE_INT(0);
    }
    return ENCODE_INT(1);
}

RuntimeValue rt_string_find(RuntimeValue str, RuntimeValue needle) {
    if (!IS_HEAP(str) || !IS_HEAP(needle)) return ENCODE_INT(-1);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(needle);
    if (n->len == 0) return ENCODE_INT(0);
    if (n->len > s->len) return ENCODE_INT(-1);
    for (uint32_t i = 0; i <= s->len - n->len; i++) {
        int found = 1;
        for (uint32_t j = 0; j < n->len; j++) {
            if (s->data[i + j] != n->data[j]) { found = 0; break; }
        }
        if (found) return ENCODE_INT(i);
    }
    return ENCODE_INT(-1);
}

/* ================================================================
 * 5. Print functions
 * ================================================================ */

void rt_print_str(RuntimeValue str) {
    if (!IS_HEAP(str)) return;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (s->header.type != HEAP_TYPE_STRING) return;
    for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
}

void rt_println_str(RuntimeValue str) {
    rt_print_str(str);
    serial_putchar('\r');
    serial_putchar('\n');
}

void rt_print_value(RuntimeValue val) {
    if (IS_INT(val)) {
        int32_t n = DECODE_INT(val);
        char buf[16];
        int i = 0;
        int neg = 0;
        if (n < 0) { neg = 1; n = -n; }
        if (n == 0) { buf[i++] = '0'; }
        else { while (n > 0) { buf[i++] = '0' + (int)(n % 10); n /= 10; } }
        if (neg) buf[i++] = '-';
        while (i > 0) serial_putchar(buf[--i]);
    } else if (val == 1) {
        /* LLVM-emitted true (raw 1, tag=TAG_HEAP, DECODE_PTR=NULL) */
        serial_puts("true");
    } else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (!h) { serial_puts("<null>"); return; }
        if (h->type == HEAP_TYPE_STRING) {
            rt_print_str(val);
        } else {
            serial_puts("<object>");
        }
    } else if (val == NIL_VALUE) {
        serial_puts("nil");
    } else if (val == TRUE_VALUE) {
        serial_puts("true");
    } else if (val == FALSE_VALUE) {
        serial_puts("false");
    }
}

void rt_println_value(RuntimeValue val) {
    rt_print_value(val);
    serial_putchar('\r');
    serial_putchar('\n');
}

/* Legacy print interface -- called by Simple's `print` statement */
void rt_print(RuntimeValue val) { rt_print_value(val); }
void rt_println(RuntimeValue val) { rt_println_value(val); }

/* serial_println -- callable from Simple via extern fn serial_println(msg: text) */
RuntimeValue serial_println(RuntimeValue val) {
    rt_print_value(val);
    serial_putchar('\r');
    serial_putchar('\n');
    return NIL_VALUE;
}

/* ================================================================
 * 6. Memory primitives
 * ================================================================ */

void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void *memset(void *s, int c, size_t n) {
    unsigned char *p = (unsigned char *)s;
    for (size_t i = 0; i < n; i++) p[i] = (unsigned char)c;
    return s;
}

void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (d < s) {
        for (size_t i = 0; i < n; i++) d[i] = s[i];
    } else {
        for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1];
    }
    return dst;
}

int memcmp(const void *s1, const void *s2, size_t n) {
    const unsigned char *a = (const unsigned char *)s1;
    const unsigned char *b = (const unsigned char *)s2;
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return (int)a[i] - (int)b[i];
    }
    return 0;
}

size_t strlen(const char *s) {
    size_t len = 0;
    while (s[len]) len++;
    return len;
}

int strcmp(const char *a, const char *b) {
    while (*a && *a == *b) { a++; b++; }
    return (int)(unsigned char)*a - (int)(unsigned char)*b;
}

char *strcpy(char *dst, const char *src) {
    char *d = dst;
    while ((*d++ = *src++)) {}
    return dst;
}

char *strncpy(char *dst, const char *src, size_t n) {
    size_t i;
    for (i = 0; i < n && src[i]; i++) dst[i] = src[i];
    for (; i < n; i++) dst[i] = 0;
    return dst;
}

/* ================================================================
 * 7. Framebuffer helpers
 * ================================================================ */

void rt_framebuffer_copy(int32_t dst_addr, int32_t *src, int32_t count) {
    volatile uint32_t *dst = (volatile uint32_t *)(uintptr_t)DECODE_INT(dst_addr);
    int32_t n = DECODE_INT(count);
    for (int32_t i = 0; i < n; i++) dst[i] = (uint32_t)DECODE_INT(src[i]);
}

void rt_fb_fill_rect(int32_t fb_addr, int32_t pitch,
                     int32_t x, int32_t y, int32_t w, int32_t h,
                     int32_t color) {
    volatile uint32_t *fb = (volatile uint32_t *)(uintptr_t)fb_addr;
    uint32_t c = (uint32_t)color;
    int32_t stride = pitch / 4;
    for (int32_t row = y; row < y + h; row++) {
        for (int32_t col = x; col < x + w; col++) {
            fb[row * stride + col] = c;
        }
    }
}

/* ================================================================
 * 8. MMIO accessors (real implementations for RISC-V 32-bit)
 * ================================================================ */

RuntimeValue rt_mmio_read_u8(RuntimeValue addr) {
    return ENCODE_INT(*(volatile uint8_t *)(uintptr_t)DECODE_INT(addr));
}
RuntimeValue rt_mmio_read_u16(RuntimeValue addr) {
    return ENCODE_INT(*(volatile uint16_t *)(uintptr_t)DECODE_INT(addr));
}
RuntimeValue rt_mmio_read_u32(RuntimeValue addr) {
    return ENCODE_INT((int32_t)*(volatile uint32_t *)(uintptr_t)DECODE_INT(addr));
}
/* 64-bit MMIO read on 32-bit: read low word only */
RuntimeValue rt_mmio_read_u64(RuntimeValue addr) {
    return ENCODE_INT((int32_t)*(volatile uint32_t *)(uintptr_t)DECODE_INT(addr));
}

RuntimeValue rt_mmio_write_u8(RuntimeValue addr, RuntimeValue val) {
    *(volatile uint8_t *)(uintptr_t)DECODE_INT(addr) = (uint8_t)DECODE_INT(val);
    return 0;
}
RuntimeValue rt_mmio_write_u16(RuntimeValue addr, RuntimeValue val) {
    *(volatile uint16_t *)(uintptr_t)DECODE_INT(addr) = (uint16_t)DECODE_INT(val);
    return 0;
}
RuntimeValue rt_mmio_write_u32(RuntimeValue addr, RuntimeValue val) {
    *(volatile uint32_t *)(uintptr_t)DECODE_INT(addr) = (uint32_t)DECODE_INT(val);
    return 0;
}
/* 64-bit MMIO write on 32-bit: write low word only */
RuntimeValue rt_mmio_write_u64(RuntimeValue addr, RuntimeValue val) {
    *(volatile uint32_t *)(uintptr_t)DECODE_INT(addr) = (uint32_t)DECODE_INT(val);
    return 0;
}

/* ================================================================
 * 9. Array / comparison / conversion operations
 * ================================================================ */

RuntimeValue rt_array_new(RuntimeValue cap_val) {
    int32_t cap = (int32_t)cap_val;  /* RAW -- not DECODE_INT */
    if (cap <= 0) cap = 64;
    if (cap < 64) cap = 64;
    if (cap > 0x100000) cap = 0x100000;
    RuntimeArray *a = (RuntimeArray *)malloc(sizeof(RuntimeArray) + (size_t)cap * sizeof(RuntimeValue));
    if (!a) return NIL_VALUE;
    a->header.type = HEAP_TYPE_ARRAY;
    a->header.size = (uint32_t)(sizeof(RuntimeArray) + cap * sizeof(RuntimeValue));
    a->len = 0;
    a->cap = (uint32_t)cap;
    return ENCODE_PTR(a);
}

void rt_array_push(RuntimeValue arr, RuntimeValue value) {
    if (!IS_HEAP(arr)) return;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (a->header.type != HEAP_TYPE_ARRAY) return;
    if (a->len >= a->cap) return; /* bump allocator can't resize in-place */
    a->data[a->len++] = value;
}

RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx_val) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int32_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int32_t)a->len) return NIL_VALUE;
    return a->data[idx];
}

RuntimeValue rt_array_set(RuntimeValue arr, RuntimeValue idx_val, RuntimeValue value) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int32_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int32_t)a->len) return NIL_VALUE;
    a->data[idx] = value;
    return value;
}

RuntimeValue rt_array_len(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return ENCODE_INT(0);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    return ENCODE_INT(a->len);
}

RuntimeValue rt_len(RuntimeValue obj) {
    if (!IS_HEAP(obj)) return ENCODE_INT(0);
    HeapHeader *h = (HeapHeader *)DECODE_PTR(obj);
    if (h->type == HEAP_TYPE_STRING) return rt_string_len(obj);
    if (h->type == HEAP_TYPE_ARRAY) return rt_array_len(obj);
    return ENCODE_INT(0);
}

/* Integer <-> String conversion */
RuntimeValue rt_int_to_string(RuntimeValue val) {
    int32_t n = DECODE_INT(val);
    char buf[16];
    int i = 0;
    int neg = 0;
    if (n < 0) { neg = 1; n = -n; }
    if (n == 0) { buf[i++] = '0'; }
    else { while (n > 0) { buf[i++] = '0' + (int)(n % 10); n /= 10; } }
    if (neg) buf[i++] = '-';
    /* reverse */
    char rev[16];
    int j = 0;
    while (i > 0) rev[j++] = buf[--i];
    rev[j] = 0;
    return rt_string_from_cstr(rev);
}

RuntimeValue rt_value_to_string(RuntimeValue val) {
    if (IS_INT(val)) return rt_int_to_string(val);
    /* LLVM backend emits bools as raw 0/1 (not tagged TRUE_VALUE/FALSE_VALUE).
     * Value 1 has tag bits 001 = TAG_HEAP, DECODE_PTR(1) = NULL -> crash.
     * Catch LLVM-style true before IS_HEAP dereference. */
    if (val == 1) return rt_string_from_cstr("true");
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (!h) return rt_string_from_cstr("<null>");
        if (h->type == HEAP_TYPE_STRING) return val;
        return rt_string_from_cstr("<object>");
    }
    if (val == NIL_VALUE) return rt_string_from_cstr("nil");
    if (val == TRUE_VALUE) return rt_string_from_cstr("true");
    if (val == FALSE_VALUE) return rt_string_from_cstr("false");
    return rt_string_from_cstr("<unknown>");
}

/* Comparison operations */
RuntimeValue rt_eq(RuntimeValue a, RuntimeValue b) {
    if (IS_INT(a) && IS_INT(b)) return ENCODE_INT(a == b ? 1 : 0);
    if (IS_HEAP(a) && IS_HEAP(b)) {
        HeapHeader *ha = (HeapHeader *)DECODE_PTR(a);
        HeapHeader *hb = (HeapHeader *)DECODE_PTR(b);
        if (ha->type == HEAP_TYPE_STRING && hb->type == HEAP_TYPE_STRING)
            return rt_string_eq(a, b);
    }
    return ENCODE_INT(a == b ? 1 : 0);
}

RuntimeValue rt_ne(RuntimeValue a, RuntimeValue b) {
    return ENCODE_INT(DECODE_INT(rt_eq(a, b)) ? 0 : 1);
}

RuntimeValue rt_lt(RuntimeValue a, RuntimeValue b) {
    return ENCODE_INT(DECODE_INT(a) < DECODE_INT(b) ? 1 : 0);
}
RuntimeValue rt_gt(RuntimeValue a, RuntimeValue b) {
    return ENCODE_INT(DECODE_INT(a) > DECODE_INT(b) ? 1 : 0);
}
RuntimeValue rt_le(RuntimeValue a, RuntimeValue b) {
    return ENCODE_INT(DECODE_INT(a) <= DECODE_INT(b) ? 1 : 0);
}
RuntimeValue rt_ge(RuntimeValue a, RuntimeValue b) {
    return ENCODE_INT(DECODE_INT(a) >= DECODE_INT(b) ? 1 : 0);
}

/* Arithmetic */
RuntimeValue rt_add(RuntimeValue a, RuntimeValue b) {
    if (IS_INT(a) && IS_INT(b)) return ENCODE_INT(DECODE_INT(a) + DECODE_INT(b));
    if (IS_HEAP(a) && IS_HEAP(b)) return rt_string_concat(a, b);
    return ENCODE_INT(0);
}
RuntimeValue rt_sub(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) - DECODE_INT(b)); }
RuntimeValue rt_mul(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) * DECODE_INT(b)); }
RuntimeValue rt_div(RuntimeValue a, RuntimeValue b) {
    int32_t bv = DECODE_INT(b);
    if (bv == 0) return ENCODE_INT(0);
    return ENCODE_INT(DECODE_INT(a) / bv);
}
RuntimeValue rt_mod(RuntimeValue a, RuntimeValue b) {
    int32_t bv = DECODE_INT(b);
    if (bv == 0) return ENCODE_INT(0);
    return ENCODE_INT(DECODE_INT(a) % bv);
}
RuntimeValue rt_neg(RuntimeValue a) { return ENCODE_INT(-DECODE_INT(a)); }

/* Bitwise */
RuntimeValue rt_bit_and(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) & DECODE_INT(b)); }
RuntimeValue rt_bit_or(RuntimeValue a, RuntimeValue b)  { return ENCODE_INT(DECODE_INT(a) | DECODE_INT(b)); }
RuntimeValue rt_bit_xor(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) ^ DECODE_INT(b)); }
RuntimeValue rt_bit_not(RuntimeValue a) { return ENCODE_INT(~DECODE_INT(a)); }
RuntimeValue rt_shl(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) << DECODE_INT(b)); }
RuntimeValue rt_shr(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) >> DECODE_INT(b)); }

/* Boolean */
RuntimeValue rt_not(RuntimeValue a) { return ENCODE_INT(DECODE_INT(a) ? 0 : 1); }
RuntimeValue rt_and(RuntimeValue a, RuntimeValue b) { return ENCODE_INT((DECODE_INT(a) && DECODE_INT(b)) ? 1 : 0); }
RuntimeValue rt_or(RuntimeValue a, RuntimeValue b)  { return ENCODE_INT((DECODE_INT(a) || DECODE_INT(b)) ? 1 : 0); }

/* Type checks */
RuntimeValue rt_type_of(RuntimeValue v) {
    if (IS_INT(v)) return rt_string_from_cstr("int");
    if (IS_HEAP(v)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
        if (h->type == HEAP_TYPE_STRING) return rt_string_from_cstr("string");
        if (h->type == HEAP_TYPE_ARRAY) return rt_string_from_cstr("array");
        return rt_string_from_cstr("object");
    }
    if (v == NIL_VALUE) return rt_string_from_cstr("nil");
    if (v == TRUE_VALUE || v == FALSE_VALUE) return rt_string_from_cstr("bool");
    return rt_string_from_cstr("unknown");
}

RuntimeValue rt_is_nil(RuntimeValue v) { return ENCODE_INT(v == NIL_VALUE ? 1 : 0); }
RuntimeValue rt_is_int(RuntimeValue v) { return ENCODE_INT(IS_INT(v) ? 1 : 0); }
RuntimeValue rt_is_string(RuntimeValue v) {
    if (!IS_HEAP(v)) return ENCODE_INT(0);
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    return ENCODE_INT(h->type == HEAP_TYPE_STRING ? 1 : 0);
}
RuntimeValue rt_is_array(RuntimeValue v) {
    if (!IS_HEAP(v)) return ENCODE_INT(0);
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    return ENCODE_INT(h->type == HEAP_TYPE_ARRAY ? 1 : 0);
}

RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(a == b ? 1 : 0); }
RuntimeValue rt_native_neq(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(a != b ? 1 : 0); }

/* ================================================================
 * 10. Serial decimal output helper
 * ================================================================ */

static void serial_put_dec(int32_t v) {
    if (v < 0) { serial_putchar('-'); v = -v; }
    if (v == 0) { serial_putchar('0'); return; }
    char buf[12];
    int i = 0;
    while (v > 0) { buf[i++] = '0' + (v % 10); v /= 10; }
    while (i > 0) serial_putchar(buf[--i]);
}

/* ================================================================
 * 11. PCI enumeration via ECAM MMIO (QEMU virt: 0x30000000)
 * ================================================================ */

#define ECAM_BASE 0x30000000UL
#define MAX_PCI_CACHED 32

static struct {
    uint8_t bus, dev, func, class_code, subclass, progif, htype, irq;
    uint16_t vendor, device;
    uint32_t bar0;
} _pci_cache[MAX_PCI_CACHED];
static int _pci_cache_count = 0;

static void _pci_scan(void) {
    _pci_cache_count = 0;
    for (int dev = 0; dev < 32 && _pci_cache_count < MAX_PCI_CACHED; dev++) {
        volatile uint32_t *cfg = (volatile uint32_t *)(ECAM_BASE + ((uint32_t)dev << 15));
        uint32_t reg0 = cfg[0];
        uint16_t vendor = (uint16_t)(reg0 & 0xFFFF);
        uint16_t devid = (uint16_t)(reg0 >> 16);
        if (vendor == 0xFFFF || vendor == 0) continue;
        uint32_t class_reg = cfg[2];
        uint32_t bar0_reg = cfg[4];
        uint32_t irq_reg = cfg[15];
        int i = _pci_cache_count++;
        _pci_cache[i].bus = 0;
        _pci_cache[i].dev = (uint8_t)dev;
        _pci_cache[i].func = 0;
        _pci_cache[i].vendor = vendor;
        _pci_cache[i].device = devid;
        _pci_cache[i].class_code = (class_reg >> 24) & 0xFF;
        _pci_cache[i].subclass = (class_reg >> 16) & 0xFF;
        _pci_cache[i].progif = (class_reg >> 8) & 0xFF;
        _pci_cache[i].htype = (cfg[3] >> 16) & 0xFF;
        _pci_cache[i].irq = (uint8_t)(irq_reg & 0xFF);
        _pci_cache[i].bar0 = bar0_reg & 0xFFFFFFF0;
    }
}

static int32_t _pci_enumerate(uint32_t mode, uint32_t index, uint32_t buf_addr) {
    if (_pci_cache_count == 0) _pci_scan();
    if (mode == 0) return (int32_t)_pci_cache_count;
    if (mode == 1) {
        if ((int)index >= _pci_cache_count) return -22;
        uint8_t *buf = (uint8_t *)(uintptr_t)buf_addr;
        int i = (int)index;
        buf[0] = _pci_cache[i].bus; buf[1] = _pci_cache[i].dev; buf[2] = _pci_cache[i].func; buf[3] = 0;
        *(uint16_t *)(buf + 4) = _pci_cache[i].vendor; *(uint16_t *)(buf + 6) = _pci_cache[i].device;
        buf[8] = _pci_cache[i].class_code; buf[9] = _pci_cache[i].subclass;
        buf[10] = _pci_cache[i].progif; buf[11] = _pci_cache[i].htype; buf[12] = _pci_cache[i].irq;
        return 0;
    }
    if (mode == 5) {
        if ((int)index >= _pci_cache_count) return -22;
        return (int32_t)_pci_cache[(int)index].bar0;
    }
    return -38; /* ENOSYS */
}

/* ================================================================
 * 12. Syscall dispatcher (32-bit trap handler)
 *
 * Called from crt0.S M-mode trap handler when mcause=11 (ecall).
 * All args are 32-bit (RV32 registers).
 * ================================================================ */

int32_t _trap_syscall(uint32_t id, uint32_t a0, uint32_t a1,
                      uint32_t a2, uint32_t a3, uint32_t a4) {
    (void)a3; (void)a4;
    switch (id) {
        case 0: /* Exit: halt with WFI loop */
            serial_puts("[HALT] exit syscall\r\n");
            for (;;) __asm__ volatile("wfi");
            return 0;
        case 4: return 1; /* GetPid */
        case 60: serial_putchar((char)(a0 & 0xFF)); return 0; /* DebugWrite */
        case 80: return _pci_enumerate(a0, a1, a2); /* DevEnumerate */
        case 82: return _pci_enumerate(5, a0, 0); /* DeviceGrant: return BAR0 */
        case 83: return (int32_t)a0; /* MapBar: identity mapped */
        case 84: { /* AllocDMA */
            void *p = malloc(a0 > 0 ? a0 : 4096);
            return (int32_t)(uintptr_t)p;
        }
        case 85: return 0; /* NvmeReadSector: stub success */
        case 86: return 0; /* NvmeInit: stub success */
        case 90: return 0; /* VirtioNetInit: stub */
        case 93: return 0; /* NetStats: stub */
        default: return -38; /* ENOSYS */
    }
}

/* ================================================================
 * 13. c_pcimgr_init — extern C wrapper for PCI scan
 *
 * Called from vfs_init.spl to avoid --no-mangle symbol collision
 * where pcimgr_init() resolves to CNvmeBlockAdapter.init().
 * ================================================================ */

void c_pcimgr_init(void) {
    serial_puts("[c_pcimgr_init] ENTERED\r\n");
    _pci_scan();
    serial_puts("[c_pcimgr_init] PCI scan: ");
    serial_put_dec(_pci_cache_count);
    serial_puts(" devices\r\n");
}

/* ================================================================
 * 14. _start entry point / _boot_init
 * ================================================================ */

/* _boot_init: called from crt0.S before spl_start.
 * crt0.S provides the real _start (sets stack, zeros BSS, installs mtvec). */
void _boot_init(void) {
    /* Direct UART write for earliest diagnostic */
    volatile uint8_t *uart = (volatile uint8_t *)0x10000000UL;
    while (!(uart[5] & 0x20)) {}
    uart[0] = 'B';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '1';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '\r';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '\n';

    _uart_init();
    serial_puts("SimpleOS RISC-V32 boot\r\n");
    serial_puts("[BOOT] 16550 UART initialized at 0x10000000\r\n");
    serial_puts("[BOOT] Heap: 4 MB bump allocator\r\n");
    serial_puts("[BOOT] RuntimeValue: tagged 32-bit (LLVM i32)\r\n");

    _pci_scan();
    serial_puts("[BOOT] PCI: ");
    serial_put_dec(_pci_cache_count);
    serial_puts(" devices found\r\n");

    serial_puts("[BOOT] Calling spl_start()...\r\n");
}

/* ================================================================
 * 14b. Enum / Optional / Result operations
 * ================================================================ */

RuntimeValue rt_enum_new(RuntimeValue enum_id_rv, RuntimeValue disc_rv, RuntimeValue payload)
{
    RuntimeEnum *e = (RuntimeEnum *)malloc(sizeof(RuntimeEnum));
    if (!e) return NIL_VALUE;
    e->header.type = HEAP_TYPE_ENUM;
    e->header.size = (uint32_t)sizeof(RuntimeEnum);
    e->enum_id = (uint32_t)(int32_t)enum_id_rv;
    e->discriminant = (uint32_t)(int32_t)disc_rv;
    e->payload = payload;
    return ENCODE_PTR(e);
}

RuntimeValue rt_enum_discriminant(RuntimeValue value)
{
    if (!IS_HEAP(value)) return -1;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->header.type != HEAP_TYPE_ENUM) return -1;
    return (RuntimeValue)(int32_t)e->discriminant;
}

RuntimeValue rt_enum_payload(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->header.type != HEAP_TYPE_ENUM) return value;
    return e->payload;
}

RuntimeValue rt_enum_check_discriminant(RuntimeValue value, RuntimeValue expected)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->header.type != HEAP_TYPE_ENUM) return 0;
    return (e->discriminant == (uint32_t)(int32_t)expected) ? 1 : 0;
}

RuntimeValue rt_is_none(RuntimeValue value)
{
    if (IS_NIL(value)) return 1;
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->header.type != HEAP_TYPE_ENUM) return 0;
    return IS_NIL(e->payload) ? 1 : 0;
}

RuntimeValue rt_is_some(RuntimeValue value)
{
    return rt_is_none(value) ? 0 : 1;
}

/* ================================================================
 * 15. No-op runtime stubs (~200 functions)
 *
 * These satisfy unresolved symbols from the Simple compiler's
 * generated code. They return 0/NIL_VALUE and do nothing.
 * ================================================================ */

#define STUB0(name) RuntimeValue name(void) { return 0; }
#define STUB1(name) RuntimeValue name(RuntimeValue a) { (void)a; return 0; }
#define STUB2(name) RuntimeValue name(RuntimeValue a, RuntimeValue b) { (void)a; (void)b; return 0; }
#define STUB3(name) RuntimeValue name(RuntimeValue a, RuntimeValue b, RuntimeValue c) { (void)a; (void)b; (void)c; return 0; }
#define STUB4(name) RuntimeValue name(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { (void)a; (void)b; (void)c; (void)d; return 0; }
#define STUB5(name) RuntimeValue name(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d, RuntimeValue e) { (void)a; (void)b; (void)c; (void)d; (void)e; return 0; }
#define STUB6(name) RuntimeValue name(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d, RuntimeValue e, RuntimeValue f) { (void)a; (void)b; (void)c; (void)d; (void)e; (void)f; return 0; }
#define VSTUB0(name) void name(void) {}
#define VSTUB1(name) void name(RuntimeValue a) { (void)a; }
#define VSTUB2(name) void name(RuntimeValue a, RuntimeValue b) { (void)a; (void)b; }
#define VSTUB3(name) void name(RuntimeValue a, RuntimeValue b, RuntimeValue c) { (void)a; (void)b; (void)c; }
#define VSTUB4(name) void name(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { (void)a; (void)b; (void)c; (void)d; }

/* --- Error / panic / abort --- */
VSTUB1(rt_panic)
VSTUB1(rt_abort)
VSTUB2(rt_assert)
VSTUB1(rt_unreachable)

/* rt_exit — matches hosted signature `extern "C" fn rt_exit(code: i32) -> !`
 * (src/compiler_rust/runtime/src/value/ffi/env_process.rs). Simple code
 * passes a raw i32 (not a tagged RuntimeValue). On RV32 bare-metal there is
 * no parent process; disable interrupts and spin on WFI to halt cleanly. */
__attribute__((noreturn))
void rt_exit(int32_t code) {
    serial_puts("[exit] rt_exit(");
    serial_put_dec(code);
    serial_puts(") -- halting\r\n");
    __asm__ volatile("csrci mstatus, 8"); /* clear MIE bit -- disable M-mode interrupts */
    for (;;) { __asm__ volatile("wfi"); }
}

/* rt_exit_code — no parent process yet; always reports 0 (no prior exit). */
RuntimeValue rt_exit_code(void) { return ENCODE_INT(0); }

/* --- GC / memory management --- */
VSTUB0(rt_gc_init)
VSTUB0(rt_gc_collect)
VSTUB0(rt_gc_disable)
VSTUB0(rt_gc_enable)
STUB0(rt_gc_stats)
VSTUB1(rt_gc_add_root)
VSTUB1(rt_gc_remove_root)
STUB1(rt_gc_is_managed)
STUB0(rt_gc_heap_size)
VSTUB1(rt_free)
STUB2(rt_realloc)
STUB1(rt_alloc_zeroed)
STUB2(rt_alloc_array)

/* --- Object / class system --- */
STUB1(rt_class_of)
STUB2(rt_instance_of)
STUB2(rt_cast)
STUB1(rt_object_hash)
STUB1(rt_object_to_string)
STUB2(rt_object_eq)
STUB1(rt_clone)
STUB1(rt_freeze)
STUB1(rt_is_frozen)

/* --- Dynamic dispatch / reflection --- */
STUB2(rt_get_field)
STUB3(rt_set_field)
STUB2(rt_has_field)
STUB2(rt_call_method)
STUB3(rt_call_method_1)
STUB4(rt_call_method_2)
STUB5(rt_call_method_3)
STUB2(rt_respond_to)
STUB1(rt_methods)
STUB1(rt_fields)

/* --- String extended ops --- */
STUB2(rt_string_contains)
STUB2(rt_string_starts_with)
STUB2(rt_string_ends_with)
STUB2(rt_string_split)
STUB2(rt_string_replace)
STUB3(rt_string_replace_all)
STUB1(rt_string_to_upper)
STUB1(rt_string_to_lower)
STUB1(rt_string_trim)
STUB1(rt_string_trim_start)
STUB1(rt_string_trim_end)
STUB1(rt_string_reverse)
STUB1(rt_string_chars)
STUB1(rt_string_bytes)
STUB2(rt_string_repeat)
STUB2(rt_string_pad_left)
STUB2(rt_string_pad_right)
STUB1(rt_string_is_empty)
STUB2(rt_string_compare)
STUB1(rt_string_hash)
STUB1(rt_string_to_int)
STUB1(rt_string_to_float)
STUB2(rt_string_format)
STUB2(rt_string_join)

/* --- Array extended ops --- */
STUB2(rt_array_pop)
STUB3(rt_array_insert)
STUB2(rt_array_remove)
STUB2(rt_array_contains)
STUB2(rt_array_index_of)
STUB1(rt_array_reverse)
STUB1(rt_array_sort)
STUB2(rt_array_sort_by)
STUB2(rt_array_map)
STUB2(rt_array_filter)
STUB3(rt_array_reduce)
STUB2(rt_array_each)
STUB2(rt_array_flat_map)
STUB3(rt_array_slice)
STUB3(rt_array_fill)
STUB1(rt_array_clear)
STUB1(rt_array_clone)
STUB2(rt_array_concat)
STUB2(rt_array_zip)
STUB2(rt_array_any)
STUB2(rt_array_all)
STUB2(rt_array_find_val)
STUB1(rt_array_min)
STUB1(rt_array_max)
STUB1(rt_array_sum)
STUB1(rt_array_first)
STUB1(rt_array_last)
STUB1(rt_array_unique)
STUB2(rt_array_join)
STUB2(rt_array_count)
STUB2(rt_array_group_by)

/* --- Map / dict --- */
STUB0(rt_map_new)
STUB3(rt_map_set)
STUB2(rt_map_get)
STUB2(rt_map_has)
STUB2(rt_map_remove)
STUB1(rt_map_keys)
STUB1(rt_map_values)
STUB1(rt_map_entries)
STUB1(rt_map_len)
STUB1(rt_map_clear)
STUB2(rt_map_merge)
STUB1(rt_map_clone)
STUB2(rt_map_each)

/* --- Set --- */
STUB0(rt_set_new)
STUB2(rt_set_add)
STUB2(rt_set_has)
STUB2(rt_set_remove)
STUB1(rt_set_len)
STUB2(rt_set_union)
STUB2(rt_set_intersect)
STUB2(rt_set_diff)

/* --- std.sys.args FFI: present-but-empty on SimpleOS until Phase 2 wires
 * argv through the SBI/syscall path. Returning 0 / "" / [] keeps
 * std.sys.args.args() callable from baremetal code without link errors.
 * Signatures match the Simple-side extern declarations at
 *   src/compiler_rust/lib/std/src/sys/args.spl:6-8
 *   rt_args_count() -> i32       (raw i32, not RuntimeValue)
 *   rt_args_get(i32) -> text     (raw i32 index, heap-tagged text)
 *   rt_args_all()  -> List<text> (heap-tagged array). */
extern RuntimeValue rt_array_new(RuntimeValue cap_val);
extern RuntimeValue rt_string_from_cstr(const char *cstr);
int32_t      rt_args_count(void)            { return 0; }
RuntimeValue rt_args_get(int32_t index)     { (void)index; return rt_string_from_cstr(""); }
RuntimeValue rt_args_all(void)              { return rt_array_new((RuntimeValue)0); }

/* rt_stdout_write / rt_stderr_write — emit Simple-string bytes to the
 * 16550 UART (shared stdout/stderr on SimpleOS; no tty layer yet).
 * Replaces the absent stub so std.io.Stdout / std.io.Stderr callers
 * actually produce serial output. */
static RuntimeValue rt_serial_write_value(RuntimeValue data) {
    if (IS_HEAP(data)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(data);
        if (h && h->type == HEAP_TYPE_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            if (s->len < 0x100000U) {
                for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
                return ENCODE_INT((int32_t)s->len);
            }
        }
    }
    return ENCODE_INT(0);
}
RuntimeValue rt_stdout_write(RuntimeValue data) { return rt_serial_write_value(data); }
RuntimeValue rt_stderr_write(RuntimeValue data) { return rt_serial_write_value(data); }

/* --- I/O / filesystem --- */
STUB1(rt_file_read_text)
STUB2(rt_file_write_text)
STUB2(rt_file_append_text)
STUB1(rt_file_exists)
STUB1(rt_file_delete)
STUB1(rt_dir_create)
STUB1(rt_dir_list)
STUB1(rt_file_size)
STUB1(rt_file_read_bytes)
STUB2(rt_file_write_bytes)
STUB0(rt_stdin_read_line)
STUB1(rt_stdin_read_bytes)

/* --- Process / system --- */
STUB1(rt_system)
STUB1(rt_exec)
STUB2(rt_exec_with_args)
STUB0(rt_env_vars)
STUB1(rt_env_get)
STUB2(rt_env_set)
STUB0(rt_pid)
STUB0(rt_timestamp)
STUB0(rt_timestamp_ms)
STUB0(rt_clock_ns)
STUB1(rt_sleep_ms)

/* --- Math --- */
STUB1(rt_abs)
STUB2(rt_min)
STUB2(rt_max)
STUB2(rt_pow)
STUB1(rt_sqrt)
STUB1(rt_floor)
STUB1(rt_ceil)
STUB1(rt_round)
STUB1(rt_log)
STUB1(rt_log2)
STUB1(rt_log10)
STUB1(rt_sin)
STUB1(rt_cos)
STUB1(rt_tan)
STUB1(rt_asin)
STUB1(rt_acos)
STUB1(rt_atan)
STUB2(rt_atan2)
STUB0(rt_random)
STUB2(rt_random_range)
STUB1(rt_random_seed)

/* --- Networking --- */
STUB2(rt_tcp_connect)
STUB1(rt_tcp_listen)
STUB1(rt_tcp_accept)
STUB2(rt_tcp_send)
STUB2(rt_tcp_recv)
STUB1(rt_tcp_close)
STUB2(rt_udp_bind)
STUB3(rt_udp_send)
STUB2(rt_udp_recv)
STUB2(rt_http_get)
STUB3(rt_http_post)
STUB1(rt_dns_resolve)

/* --- Threading / concurrency --- */
STUB1(rt_thread_spawn)
STUB1(rt_thread_join)
STUB0(rt_thread_id)
STUB1(rt_thread_sleep)
STUB0(rt_mutex_new)
STUB1(rt_mutex_lock)
STUB1(rt_mutex_unlock)
STUB0(rt_channel_new)
STUB2(rt_channel_send)
STUB1(rt_channel_recv)
STUB0(rt_atomic_new)
STUB1(rt_atomic_load)
STUB2(rt_atomic_store)
STUB2(rt_atomic_add)
STUB3(rt_atomic_cas)

/* --- Closure / function --- */
STUB2(rt_closure_new)
STUB1(rt_closure_call)
STUB2(rt_closure_call_1)
STUB3(rt_closure_call_2)
STUB2(rt_closure_bind)
STUB1(rt_closure_arity)

/* --- Trait / interface --- */
STUB2(rt_trait_impl)
STUB2(rt_trait_check)
STUB2(rt_dyn_dispatch)
STUB3(rt_dyn_dispatch_1)
STUB4(rt_dyn_dispatch_2)
STUB1(rt_vtable_lookup)

/* --- Error / Result / Option --- */
STUB1(rt_result_ok)
STUB1(rt_result_err)
STUB1(rt_result_is_ok)
STUB1(rt_result_is_err)
STUB1(rt_result_unwrap)
STUB1(rt_result_unwrap_err)
STUB2(rt_result_unwrap_or)
STUB1(rt_option_some)
STUB0(rt_option_none)
STUB1(rt_option_is_some)
STUB1(rt_option_is_none)
STUB1(rt_option_unwrap)
STUB2(rt_option_unwrap_or)

/* --- Iterator protocol --- */
STUB1(rt_iter_new)
STUB1(rt_iter_next)
STUB1(rt_iter_has_next)
STUB1(rt_iter_collect)
STUB2(rt_iter_map)
STUB2(rt_iter_filter)
STUB3(rt_iter_fold)
STUB2(rt_iter_take)
STUB2(rt_iter_skip)
STUB2(rt_iter_chain)
STUB1(rt_iter_enumerate)
STUB2(rt_iter_zip)

/* --- Range --- */
STUB2(rt_range_new)
STUB3(rt_range_new_step)
STUB1(rt_range_iter)
STUB1(rt_range_len)
STUB2(rt_range_contains)

/* --- Regex --- */
STUB1(rt_regex_new)
STUB2(rt_regex_match)
STUB2(rt_regex_find_all)
STUB3(rt_regex_replace)
STUB2(rt_regex_split)

/* --- JSON --- */
STUB1(rt_json_parse)
STUB1(rt_json_stringify)
STUB2(rt_json_get)
STUB3(rt_json_set)

/* --- Formatting / debug --- */
STUB1(rt_debug_repr)
STUB2(rt_format)
STUB1(rt_inspect)
STUB1(rt_type_name)
STUB1(rt_size_of)
STUB1(rt_address_of)

/* --- Weak references / ref counting --- */
STUB1(rt_weak_ref)
STUB1(rt_weak_deref)
STUB1(rt_rc_new)
STUB1(rt_rc_clone)
STUB1(rt_rc_strong_count)

/* --- Async / await --- */
STUB1(rt_async_spawn)
STUB1(rt_await)
STUB0(rt_async_yield)
STUB1(rt_future_poll)
STUB2(rt_future_then)
STUB0(rt_event_loop_run)
STUB0(rt_event_loop_stop)

/* --- Casting / conversion --- */
STUB1(rt_to_int)
STUB1(rt_to_float)
STUB1(rt_to_string)
STUB1(rt_to_bool)
STUB1(rt_to_bytes)
STUB1(rt_parse_int)
STUB1(rt_parse_float)
STUB2(rt_int_to_bytes)
STUB2(rt_bytes_to_int)
STUB1(rt_char_to_string)

/* --- Platform / arch-specific baremetal --- */
STUB0(rt_cpu_id)
STUB0(rt_arch_name)
STUB0(rt_page_size)

/* RISC-V has no port I/O -- provide stubs for compatibility */
VSTUB2(rt_port_out_u8)
STUB1(rt_port_in_u8)
VSTUB2(rt_port_out_u16)
STUB1(rt_port_in_u16)
VSTUB2(rt_port_out_u32)
STUB1(rt_port_in_u32)

/* RISC-V CSR access stubs */
VSTUB0(rt_cli)
VSTUB0(rt_sti)
VSTUB0(rt_hlt)
STUB1(rt_cr_read)
VSTUB2(rt_cr_write)
STUB0(rt_rdtsc)
VSTUB1(rt_invlpg)
VSTUB1(rt_lidt)
VSTUB1(rt_lgdt)
VSTUB1(rt_ltr)
STUB0(rt_flags)
VSTUB0(rt_enable_sse)
VSTUB0(rt_enable_avx)

/* --- Interrupt / exception stubs --- */
VSTUB1(rt_register_isr)
VSTUB2(rt_register_irq)
VSTUB0(rt_pic_init)
VSTUB0(rt_pic_eoi)
VSTUB1(rt_pic_eoi_irq)
VSTUB0(rt_apic_init)
VSTUB0(rt_apic_eoi)
VSTUB0(rt_ioapic_init)

/* --- RISC-V PLIC stubs (platform-level interrupt controller) --- */
VSTUB0(rt_plic_init)
VSTUB2(rt_plic_set_priority)
VSTUB1(rt_plic_enable)
VSTUB1(rt_plic_disable)
STUB0(rt_plic_claim)
VSTUB1(rt_plic_complete)

/* --- Paging / virtual memory --- */
STUB0(rt_page_alloc)
VSTUB1(rt_page_free)
VSTUB3(rt_page_map)
VSTUB1(rt_page_unmap)
STUB1(rt_virt_to_phys)
STUB0(rt_kernel_page_table)
VSTUB0(rt_tlb_flush_all)
VSTUB1(rt_tlb_flush_page)

/* --- Timer --- */
VSTUB0(rt_pit_init)
VSTUB1(rt_pit_set_freq)
STUB0(rt_pit_ticks)
VSTUB0(rt_hpet_init)
STUB0(rt_hpet_ticks)
VSTUB0(rt_tsc_init)

/* --- RISC-V timer (mtime/mtimecmp) --- */
STUB0(rt_riscv_mtime)
VSTUB1(rt_riscv_mtimecmp_set)

/* --- Keyboard / PS2 --- */
STUB0(rt_kbd_read)
STUB0(rt_kbd_poll)
VSTUB0(rt_kbd_init)

/* --- Disk / block device --- */
STUB3(rt_disk_read)
STUB3(rt_disk_write)
STUB0(rt_disk_size)
VSTUB0(rt_disk_init)
STUB1(rt_disk_identify)

/* --- Virtio --- */
VSTUB0(rt_virtio_init)
STUB1(rt_virtio_probe)
STUB2(rt_virtio_read)
STUB3(rt_virtio_write)

/* --- Power management --- */
VSTUB0(rt_acpi_init)
VSTUB0(rt_acpi_shutdown)
VSTUB0(rt_acpi_reboot)
STUB0(rt_acpi_get_pm_timer)

/* --- BDD / test framework stubs --- */
VSTUB1(rt_bdd_describe_start)
VSTUB1(rt_bdd_describe_end)
VSTUB2(rt_bdd_it_start)
VSTUB1(rt_bdd_it_end)
STUB1(rt_expect)
STUB2(rt_expect_eq)
STUB2(rt_expect_ne)

/* --- Hash / debug / misc --- */
STUB1(rt_hash)
VSTUB1(rt_debug_print)

/* --- Regex FFI stubs --- */
STUB2(ffi_regex_is_match)
STUB2(ffi_regex_find)
STUB2(ffi_regex_find_all)
STUB2(ffi_regex_replace)

/* ===================================================================
 * Crypto — shared portable implementation
 * =================================================================== */
#if !defined(__riscv_xlen) || __riscv_xlen >= 64
#define RV_INT int32_t
#define CRYPTO_ARRAY_HDR_TYPE(arr) ((arr)->header.type)
#define CRYPTO_ARRAY_ITEMS(arr) ((arr)->data)
#include "../../shared/crypto_common.h"
#endif

/* End of riscv32 baremetal_stubs.c */
