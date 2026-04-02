/*
 * baremetal_stubs.c -- RISC-V 64 baremetal runtime stubs (COMPLETE)
 *
 * Provides the FULL Simple runtime support needed for SimpleOS to boot
 * in QEMU with serial output.
 *
 * Sections:
 *   1. Serial I/O (16550 UART at MMIO 0x10000000)
 *   2. RuntimeValue tagging system
 *   3. Heap allocator (16MB bump)
 *   4. String operations
 *   5. Print functions
 *   6. Memory primitives
 *   7. Framebuffer helpers
 *   8. MMIO accessors
 *   9. Array / comparison operations
 *  10. _start entry point
 *  11. ~200 no-op runtime stubs
 */

#include <stddef.h>
#include <stdint.h>

/* ================================================================
 * 1. Serial I/O -- 16550 UART at MMIO 0x10000000 (QEMU virt)
 * ================================================================ */

#define UART_BASE  0x10000000ULL

/* 16550 register offsets */
#define UART_THR   0x00  /* Transmit Holding Register */
#define UART_RBR   0x00  /* Receive Buffer Register */
#define UART_IER   0x01  /* Interrupt Enable Register */
#define UART_FCR   0x02  /* FIFO Control Register */
#define UART_LCR   0x03  /* Line Control Register */
#define UART_MCR   0x04  /* Modem Control Register */
#define UART_LSR   0x05  /* Line Status Register */
#define UART_DLL   0x00  /* Divisor Latch Low (DLAB=1) */
#define UART_DLH   0x01  /* Divisor Latch High (DLAB=1) */

/* LSR bits */
#define UART_LSR_THRE  0x20  /* Transmit Holding Register Empty */
#define UART_LSR_DR    0x01  /* Data Ready */

static inline void uart_write(uint64_t offset, uint8_t val) {
    *(volatile uint8_t *)(uintptr_t)(UART_BASE + offset) = val;
}

static inline uint8_t uart_read(uint64_t offset) {
    return *(volatile uint8_t *)(uintptr_t)(UART_BASE + offset);
}

static int g_serial_inited = 0;

static void _serial_init(void) {
    if (g_serial_inited) return;
    /* Disable interrupts */
    uart_write(UART_IER, 0x00);
    /* Enable DLAB to set baud rate */
    uart_write(UART_LCR, 0x80);
    /* Set divisor to 1 (115200 baud at 1.8432 MHz) */
    uart_write(UART_DLL, 0x01);
    uart_write(UART_DLH, 0x00);
    /* 8 bits, no parity, 1 stop bit, DLAB off */
    uart_write(UART_LCR, 0x03);
    /* Enable FIFO, clear, 14-byte threshold */
    uart_write(UART_FCR, 0xC7);
    /* RTS/DSR set */
    uart_write(UART_MCR, 0x0B);
    g_serial_inited = 1;
}

static void serial_putchar(char c) {
    _serial_init();
    while (!(uart_read(UART_LSR) & UART_LSR_THRE)) {}
    uart_write(UART_THR, (uint8_t)c);
}

static void serial_puts(const char *s) {
    while (*s) {
        if (*s == '\n') serial_putchar('\r');
        serial_putchar(*s++);
    }
}

/* ================================================================
 * 2. RuntimeValue tagging system
 * ================================================================ */

typedef int64_t RuntimeValue;

#define TAG_MASK     0x7ULL
#define TAG_INT      0x0ULL
#define TAG_HEAP     0x1ULL
#define TAG_SPECIAL  0x3ULL

#define ENCODE_INT(v)   ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v)   ((int64_t)((uint64_t)(v) >> 3))
#define ENCODE_PTR(p)   ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)   ((void*)((uint64_t)(v) & ~TAG_MASK))
#define IS_INT(v)       (((uint64_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)      (((uint64_t)(v) & TAG_MASK) == TAG_HEAP)
#define IS_SPECIAL(v)   (((uint64_t)(v) & TAG_MASK) == TAG_SPECIAL)

#define NIL_VALUE       ((RuntimeValue)TAG_SPECIAL)
#define TRUE_VALUE      ((RuntimeValue)(0x8ULL | TAG_SPECIAL))
#define FALSE_VALUE     ((RuntimeValue)(0x10ULL | TAG_SPECIAL))

typedef struct { uint32_t type; uint32_t size; } HeapHeader;
typedef struct { HeapHeader header; uint32_t len; char data[]; } RuntimeString;
typedef struct { HeapHeader header; uint32_t len; uint32_t cap; RuntimeValue data[]; } RuntimeArray;

#define HEAP_TYPE_STRING  1
#define HEAP_TYPE_ARRAY   2
#define HEAP_TYPE_OBJECT  3

/* ================================================================
 * 3. Heap allocator -- 16MB bump allocator, 16-byte aligned
 * ================================================================ */

static char _heap[16 * 1024 * 1024]; /* 16 MB */
static size_t _heap_offset = 0;

void *malloc(size_t size) {
    size = (size + 15) & ~(size_t)15;
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
    return ENCODE_PTR(malloc((size_t)DECODE_INT(size)));
}

/* ================================================================
 * 4. String operations
 * ================================================================ */

RuntimeValue rt_string_new(RuntimeValue data_ptr, RuntimeValue len_val) {
    int64_t len = DECODE_INT(len_val);
    if (len < 0) len = 0;
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + (size_t)len + 1);
    if (!s) return NIL_VALUE;
    s->header.type = HEAP_TYPE_STRING;
    s->header.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    s->len = (uint32_t)len;
    if (IS_HEAP(data_ptr)) {
        __builtin_memcpy(s->data, DECODE_PTR(data_ptr), (size_t)len);
    } else if (data_ptr) {
        __builtin_memcpy(s->data, (const void *)(uintptr_t)data_ptr, (size_t)len);
    }
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
    int64_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int64_t)s->len) return ENCODE_INT(0);
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
    int64_t start = DECODE_INT(start_val);
    int64_t end = DECODE_INT(end_val);
    if (start < 0) start = 0;
    if (end > (int64_t)s->len) end = s->len;
    if (start >= end) {
        RuntimeString *empty = (RuntimeString *)malloc(sizeof(RuntimeString) + 1);
        if (!empty) return NIL_VALUE;
        empty->header.type = HEAP_TYPE_STRING;
        empty->header.size = (uint32_t)(sizeof(RuntimeString) + 1);
        empty->len = 0;
        empty->data[0] = 0;
        return ENCODE_PTR(empty);
    }
    int64_t len = end - start;
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
        int64_t n = DECODE_INT(val);
        char buf[32];
        int i = 0;
        int neg = 0;
        if (n < 0) { neg = 1; n = -n; }
        if (n == 0) { buf[i++] = '0'; }
        else { while (n > 0) { buf[i++] = '0' + (int)(n % 10); n /= 10; } }
        if (neg) buf[i++] = '-';
        while (i > 0) serial_putchar(buf[--i]);
    } else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
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

void rt_print(RuntimeValue val) { rt_print_value(val); }
void rt_println(RuntimeValue val) { rt_println_value(val); }

void serial_println(const char *s) {
    if (s) serial_puts(s);
    serial_putchar('\r');
    serial_putchar('\n');
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

void rt_framebuffer_copy(int64_t dst_addr, int64_t *src, int64_t count) {
    volatile uint32_t *dst = (volatile uint32_t *)(uintptr_t)DECODE_INT(dst_addr);
    int64_t n = DECODE_INT(count);
    for (int64_t i = 0; i < n; i++) dst[i] = (uint32_t)DECODE_INT(src[i]);
}

void rt_fb_fill_rect(int64_t fb_addr, int64_t pitch,
                     int64_t x, int64_t y, int64_t w, int64_t h,
                     int64_t color) {
    volatile uint32_t *fb = (volatile uint32_t *)(uintptr_t)fb_addr;
    uint32_t c = (uint32_t)color;
    int64_t stride = pitch / 4;
    for (int64_t row = y; row < y + h; row++) {
        for (int64_t col = x; col < x + w; col++) {
            fb[row * stride + col] = c;
        }
    }
}

/* ================================================================
 * 8. MMIO accessors
 * ================================================================ */

void rt_mmio_write_u8(uint64_t addr, uint64_t val) {
    *(volatile uint8_t *)(uintptr_t)addr = (uint8_t)val;
}
uint64_t rt_mmio_read_u8(uint64_t addr) {
    return *(volatile uint8_t *)(uintptr_t)addr;
}
void rt_mmio_write_u16(uint64_t addr, uint64_t val) {
    *(volatile uint16_t *)(uintptr_t)addr = (uint16_t)val;
}
uint64_t rt_mmio_read_u16(uint64_t addr) {
    return *(volatile uint16_t *)(uintptr_t)addr;
}
void rt_mmio_write_u32(uint64_t addr, uint64_t val) {
    *(volatile uint32_t *)(uintptr_t)addr = (uint32_t)val;
}
uint64_t rt_mmio_read_u32(uint64_t addr) {
    return *(volatile uint32_t *)(uintptr_t)addr;
}
void rt_mmio_write_u64(uint64_t addr, uint64_t val) {
    *(volatile uint64_t *)(uintptr_t)addr = val;
}
uint64_t rt_mmio_read_u64(uint64_t addr) {
    return *(volatile uint64_t *)(uintptr_t)addr;
}

/* ================================================================
 * 9. Array / comparison / conversion operations
 * ================================================================ */

RuntimeValue rt_array_new(RuntimeValue cap_val) {
    int64_t cap = DECODE_INT(cap_val);
    if (cap < 4) cap = 4;
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
    if (a->len >= a->cap) return;
    a->data[a->len++] = value;
}

RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx_val) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int64_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int64_t)a->len) return NIL_VALUE;
    return a->data[idx];
}

RuntimeValue rt_array_set(RuntimeValue arr, RuntimeValue idx_val, RuntimeValue value) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int64_t idx = DECODE_INT(idx_val);
    if (idx < 0 || idx >= (int64_t)a->len) return NIL_VALUE;
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

RuntimeValue rt_int_to_string(RuntimeValue val) {
    int64_t n = DECODE_INT(val);
    char buf[32];
    int i = 0;
    int neg = 0;
    if (n < 0) { neg = 1; n = -n; }
    if (n == 0) { buf[i++] = '0'; }
    else { while (n > 0) { buf[i++] = '0' + (int)(n % 10); n /= 10; } }
    if (neg) buf[i++] = '-';
    char rev[32];
    int j = 0;
    while (i > 0) rev[j++] = buf[--i];
    rev[j] = 0;
    return rt_string_from_cstr(rev);
}

RuntimeValue rt_value_to_string(RuntimeValue val) {
    if (IS_INT(val)) return rt_int_to_string(val);
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
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
RuntimeValue rt_ne(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(rt_eq(a, b)) ? 0 : 1); }
RuntimeValue rt_lt(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) < DECODE_INT(b) ? 1 : 0); }
RuntimeValue rt_gt(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) > DECODE_INT(b) ? 1 : 0); }
RuntimeValue rt_le(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) <= DECODE_INT(b) ? 1 : 0); }
RuntimeValue rt_ge(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) >= DECODE_INT(b) ? 1 : 0); }

/* Arithmetic */
RuntimeValue rt_add(RuntimeValue a, RuntimeValue b) {
    if (IS_INT(a) && IS_INT(b)) return ENCODE_INT(DECODE_INT(a) + DECODE_INT(b));
    if (IS_HEAP(a) && IS_HEAP(b)) return rt_string_concat(a, b);
    return ENCODE_INT(0);
}
RuntimeValue rt_sub(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) - DECODE_INT(b)); }
RuntimeValue rt_mul(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) * DECODE_INT(b)); }
RuntimeValue rt_div(RuntimeValue a, RuntimeValue b) {
    int64_t bv = DECODE_INT(b);
    if (bv == 0) return ENCODE_INT(0);
    return ENCODE_INT(DECODE_INT(a) / bv);
}
RuntimeValue rt_mod(RuntimeValue a, RuntimeValue b) {
    int64_t bv = DECODE_INT(b);
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
 * 10. _start entry point
 * ================================================================ */

/* SBI ecall for shutdown */
static void sbi_shutdown(void) {
    register unsigned long a7 __asm__("a7") = 0x08; /* SBI_SHUTDOWN */
    register unsigned long a0 __asm__("a0") = 0;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a7));
}

void _start(void) {
    _serial_init();
    serial_puts("SimpleOS riscv64 boot\r\n");
    serial_puts("[BOOT] 16550 UART initialized\r\n");

    extern void spl_start(void) __attribute__((weak));
    if (spl_start) {
        serial_puts("[BOOT] Calling spl_start...\r\n");
        spl_start();
    } else {
        serial_puts("[BOOT] No spl_start found\r\n");
    }

    serial_puts("[BOOT] riscv64 boot complete\r\n");
    sbi_shutdown();
    for (;;) __asm__ volatile("wfi");
}

/* ================================================================
 * 11. No-op runtime stubs (~200 functions)
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
VSTUB0(rt_exit)
VSTUB1(rt_exit_code)

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
VSTUB0(rt_cli)
VSTUB0(rt_sti)
VSTUB0(rt_hlt)
STUB0(rt_flags)

/* --- RISC-V specific CSR access --- */
STUB1(rt_csrr)
VSTUB2(rt_csrw)
VSTUB2(rt_csrs)
VSTUB2(rt_csrc)
STUB0(rt_mhartid)
STUB0(rt_mstatus)
STUB0(rt_mtvec)
VSTUB1(rt_set_mtvec)
STUB0(rt_stvec)
VSTUB1(rt_set_stvec)
STUB0(rt_satp)
VSTUB1(rt_set_satp)
VSTUB0(rt_sfence_vma)
STUB0(rt_rdtime)
STUB0(rt_rdcycle)
STUB0(rt_rdinstret)

/* --- Interrupt / exception stubs --- */
VSTUB1(rt_register_isr)
VSTUB2(rt_register_irq)
VSTUB0(rt_plic_init)
STUB1(rt_plic_claim)
VSTUB1(rt_plic_complete)
VSTUB2(rt_plic_set_priority)
VSTUB2(rt_plic_enable)

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
VSTUB0(rt_timer_init)
STUB0(rt_timer_ticks)
VSTUB1(rt_timer_set_freq)
VSTUB1(rt_clint_set_timer)
STUB0(rt_clint_get_time)

/* --- Keyboard / input --- */
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

/* --- Power management (via SBI) --- */
VSTUB0(rt_sbi_shutdown)
VSTUB0(rt_sbi_reboot)
STUB0(rt_sbi_get_spec_version)
STUB1(rt_sbi_hart_start)
STUB0(rt_sbi_hart_stop)
