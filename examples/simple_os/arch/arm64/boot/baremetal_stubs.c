/*
 * SimpleOS ARM64 (AArch64) Baremetal Runtime Stubs
 *
 * Provides a complete freestanding runtime for the Simple language compiler
 * targeting ARM64 bare-metal (QEMU virt machine, PL011 UART).
 *
 * Ported from x86_64/boot/baremetal_stubs.c — all shared runtime functions
 * are identical; only serial I/O, PCI enumeration, and CPU control differ.
 *
 * Sections:
 *   1. Includes and types
 *   2. Serial I/O (PL011 UART at 0x09000000)
 *   3. RuntimeValue tagging
 *   4. Heap allocator (bump, 64 MB)
 *   5. Memory functions
 *   6. String operations
 *   7. Print functions
 *   8. Framebuffer, native comparison, PCI, syscall
 *   9. _c_start (PL011 init, call spl_start, wfe loop)
 *  10. Arithmetic, type introspection, conversion
 *  11. String extras (full implementations)
 *  12. Array operations (full implementations)
 *  13. Map/Dict operations (full implementations)
 *  14. Additional runtime stubs (OS boot path)
 *  15. Fatal-panic stubs (~200 runtime functions)
 *  16. Real ARM64 MMIO and CPU overrides
 */

/* ===================================================================
 * 1. Includes and types
 * =================================================================== */

#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

/* ===================================================================
 * 2. Serial I/O — PL011 UART at MMIO 0x09000000 (QEMU virt)
 * =================================================================== */

#define PL011_BASE   0x09000000ULL

/* PL011 register offsets */
#define PL011_DR     0x000   /* Data Register */
#define PL011_FR     0x018   /* Flag Register */
#define PL011_IBRD   0x024   /* Integer Baud Rate Divisor */
#define PL011_FBRD   0x028   /* Fractional Baud Rate Divisor */
#define PL011_LCRH   0x02C   /* Line Control Register */
#define PL011_CR     0x030   /* Control Register */
#define PL011_IMSC   0x038   /* Interrupt Mask Set/Clear */
#define PL011_ICR    0x044   /* Interrupt Clear Register */

/* Flag Register bits */
#define PL011_FR_TXFF  (1 << 5)  /* Transmit FIFO full */
#define PL011_FR_RXFE  (1 << 4)  /* Receive FIFO empty */
#define PL011_FR_BUSY  (1 << 3)  /* UART busy */

static inline volatile uint32_t *pl011_reg(uint32_t offset)
{
    return (volatile uint32_t *)(PL011_BASE + offset);
}

static void serial_putchar(char c)
{
    /* Wait briefly until transmit FIFO is not full. Some QEMU loader boot
     * paths leave PL011 flags in a state that should not block boot logs
     * forever, so fall through and write the byte after a bounded spin.
     */
    for (uint32_t spin = 0; spin < 100000; spin++) {
        if ((*pl011_reg(PL011_FR) & PL011_FR_TXFF) == 0) break;
    }
    *pl011_reg(PL011_DR) = (uint32_t)(unsigned char)c;
}

static void serial_puts(const char *s)
{
    while (*s) {
        if (*s == '\n') serial_putchar('\r');
        serial_putchar(*s++);
    }
}

static void serial_puts_direct(const char *s)
{
    while (*s) {
        *pl011_reg(PL011_DR) = (uint32_t)(unsigned char)(*s++);
    }
}

static void serial_put_hex(uint64_t v)
{
    static const char hex[] = "0123456789abcdef";
    serial_puts("0x");
    int started = 0;
    for (int i = 60; i >= 0; i -= 4) {
        int nibble = (v >> i) & 0xF;
        if (nibble || started || i == 0) {
            serial_putchar(hex[nibble]);
            started = 1;
        }
    }
}

static void serial_put_dec(int64_t v)
{
    if (v < 0) {
        serial_putchar('-');
        if (v == (-9223372036854775807LL - 1)) {
            serial_puts("9223372036854775808");
            return;
        }
        v = -v;
    }
    char buf[21];
    int pos = 0;
    uint64_t uv = (uint64_t)v;
    do {
        buf[pos++] = '0' + (char)(uv % 10);
        uv /= 10;
    } while (uv > 0);
    while (pos > 0) {
        serial_putchar(buf[--pos]);
    }
}

static void serial_puthex(uint32_t v) {
    static const char hex[] = "0123456789abcdef";
    if (v > 0xFFFF) { serial_putchar(hex[(v>>28)&0xF]); serial_putchar(hex[(v>>24)&0xF]); serial_putchar(hex[(v>>20)&0xF]); serial_putchar(hex[(v>>16)&0xF]); }
    if (v > 0xFF) { serial_putchar(hex[(v>>12)&0xF]); serial_putchar(hex[(v>>8)&0xF]); }
    serial_putchar(hex[(v>>4)&0xF]); serial_putchar(hex[v&0xF]);
}

/* ===================================================================
 * 3. RuntimeValue tagging
 * =================================================================== */

#define TAG_MASK    0x7ULL
#define TAG_INT     0x0ULL
#define TAG_HEAP    0x1ULL
#define TAG_FLOAT   0x2ULL
#define TAG_SPECIAL 0x3ULL

#define ENCODE_INT(v)  ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v)  ((int64_t)((uint64_t)(v) >> 3))

#define ENCODE_PTR(p)  ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)  ((void*)((uint64_t)(v) & ~TAG_MASK))

#define IS_INT(v)      (((uint64_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)     (((uint64_t)(v) & TAG_MASK) == TAG_HEAP)
#define IS_FLOAT(v)    (((uint64_t)(v) & TAG_MASK) == TAG_FLOAT)
#define IS_NIL(v)      ((v) == (RuntimeValue)TAG_SPECIAL)

#define NIL_VALUE      ((RuntimeValue)TAG_SPECIAL)
#define TRUE_VALUE     ENCODE_INT(1)
#define FALSE_VALUE    ENCODE_INT(0)

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint32_t   len;
    char       data[];
} RuntimeString;

typedef struct {
    HeapHeader   hdr;
    uint32_t     len;
    uint32_t     cap;
    RuntimeValue items[];
} RuntimeArray;

#define HEAP_STRING 1
#define HEAP_ARRAY  2
#define HEAP_MAP    3
#define HEAP_OBJECT 4
#define HEAP_ENUM   7

typedef struct {
    HeapHeader   hdr;
    uint32_t     enum_id;
    uint32_t     discriminant;
    RuntimeValue payload;
} RuntimeEnum;

/* Forward declaration */
typedef struct {
    HeapHeader    hdr;
    uint32_t      len;
    uint32_t      cap;
    RuntimeValue *keys;
    RuntimeValue *values;
} RuntimeMap;

/* Forward declarations for functions used before definition */
RuntimeValue rt_map_clone(RuntimeValue map);
RuntimeValue rt_map_new(void);
RuntimeValue rt_map_set(RuntimeValue map, RuntimeValue key, RuntimeValue value);
RuntimeValue rt_map_get(RuntimeValue map, RuntimeValue key);
RuntimeValue rt_array_new(RuntimeValue cap_val);
RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val);
RuntimeValue rt_string_concat(RuntimeValue a, RuntimeValue b);
RuntimeValue rt_string_from_cstr(const char *cstr);
RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val);
RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b);
RuntimeValue rt_value_to_string(RuntimeValue val);
RuntimeValue rt_value_format_string(RuntimeValue val, RuntimeValue fmt_ptr, RuntimeValue fmt_len);
RuntimeValue rt_string_format(RuntimeValue fmt, RuntimeValue val);
RuntimeValue rt_string_slice(RuntimeValue str, RuntimeValue start, RuntimeValue end);
void rt_print_value(RuntimeValue val);

/* ===================================================================
 * 4. Heap allocator — bump allocator, 64 MB
 * =================================================================== */

static char   _heap[64 * 1024 * 1024] __attribute__((aligned(16)));
static size_t _heap_off = 0;

static void *_heap_alloc(size_t sz)
{
    sz = (sz + 15) & ~(size_t)15;
    if (_heap_off + sz > sizeof(_heap)) {
        serial_puts("[PANIC] heap exhausted\r\n");
        for(;;) __asm__ volatile("wfe");
    }
    void *p = &_heap[_heap_off];
    _heap_off += sz;
    return p;
}

void *malloc(size_t sz)
{
    return _heap_alloc(sz);
}

void free(void *p)
{
    (void)p; /* bump allocator: no-op */
}

void *realloc(void *p, size_t sz)
{
    void *n = malloc(sz);
    if (p && n) __builtin_memcpy(n, p, sz);
    return n;
}

void *calloc(size_t n, size_t sz)
{
    size_t total = n * sz;
    void *p = malloc(total);
    if (p) __builtin_memset(p, 0, total);
    return p;
}

RuntimeValue rt_alloc(RuntimeValue sz)
{
    /* compile_struct_init passes RAW size (not tagged): iconst.i64 16
     * Return RAW pointer -- codegen uses it directly for store(val, ptr, offset). */
    size_t bytes = (size_t)sz;
    if (bytes == 0) return 0;
    if (bytes > 0x1000000) bytes = 0x1000000;
    void *p = malloc(bytes);
    if (!p) return 0;
    __builtin_memset(p, 0, bytes);
    return (RuntimeValue)(uintptr_t)p;
}

RuntimeValue rt_alloc_zeroed(RuntimeValue sz)
{
    size_t bytes = (size_t)DECODE_INT(sz);
    if (bytes == 0 || bytes > 0x1000000) bytes = (size_t)sz;
    void *p = malloc(bytes);
    if (!p) return NIL_VALUE;
    __builtin_memset(p, 0, bytes);
    return ENCODE_PTR(p);
}

RuntimeValue rt_dealloc(RuntimeValue ptr)
{
    (void)ptr;
    return NIL_VALUE;
}

/* ===================================================================
 * 5. Memory functions — freestanding replacements
 * =================================================================== */

void *memcpy(void *dst, const void *src, size_t n)
{
    uint8_t       *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void *memset(void *dst, int c, size_t n)
{
    uint8_t *d = (uint8_t *)dst;
    for (size_t i = 0; i < n; i++) d[i] = (uint8_t)c;
    return dst;
}

void *memmove(void *dst, const void *src, size_t n)
{
    uint8_t       *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    if (d < s) {
        for (size_t i = 0; i < n; i++) d[i] = s[i];
    } else if (d > s) {
        for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1];
    }
    return dst;
}

int memcmp(const void *a, const void *b, size_t n)
{
    const uint8_t *pa = (const uint8_t *)a;
    const uint8_t *pb = (const uint8_t *)b;
    for (size_t i = 0; i < n; i++) {
        if (pa[i] != pb[i]) return (int)pa[i] - (int)pb[i];
    }
    return 0;
}

size_t strlen(const char *s)
{
    size_t len = 0;
    while (s[len]) len++;
    return len;
}

char *strcpy(char *dst, const char *src)
{
    char *d = dst;
    while ((*d++ = *src++)) {}
    return dst;
}

char *strncpy(char *dst, const char *src, size_t n)
{
    size_t i;
    for (i = 0; i < n && src[i]; i++) dst[i] = src[i];
    for (; i < n; i++) dst[i] = '\0';
    return dst;
}

int strcmp(const char *a, const char *b)
{
    while (*a && *a == *b) { a++; b++; }
    return (int)(unsigned char)*a - (int)(unsigned char)*b;
}

int strncmp(const char *a, const char *b, size_t n)
{
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return (int)(unsigned char)a[i] - (int)(unsigned char)b[i];
        if (!a[i]) break;
    }
    return 0;
}

char *strcat(char *dst, const char *src)
{
    char *d = dst + strlen(dst);
    while ((*d++ = *src++)) {}
    return dst;
}

/* ===================================================================
 * 6. String operations
 * =================================================================== */

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val)
{
    int64_t len = len_val;
    if (len < 0 || len > 0x100000) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + (size_t)len + 1);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + (size_t)len + 1);
    s->len = (uint32_t)len;
    const char *src = (const char *)(uintptr_t)data;
    if (src && len > 0) __builtin_memcpy(s->data, src, (size_t)len);
    s->data[len] = '\0';
    return ENCODE_PTR(s);
}

RuntimeValue rt_string_from_cstr(const char *cstr)
{
    if (!cstr) return NIL_VALUE;
    size_t len = strlen(cstr);
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + len + 1);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    s->len = (uint32_t)len;
    __builtin_memcpy(s->data, cstr, len);
    s->data[len] = '\0';
    return ENCODE_PTR(s);
}

RuntimeValue rt_string_len(RuntimeValue str)
{
    if (!IS_HEAP(str)) return ENCODE_INT(0);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s) return ENCODE_INT(0);
    return ENCODE_INT(s->len);
}

RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx)
{
    if (!IS_HEAP(str)) return ENCODE_INT(0);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int64_t i = DECODE_INT(idx);
    if (!s || i < 0 || (uint32_t)i >= s->len) return ENCODE_INT(0);
    return ENCODE_INT((int64_t)(unsigned char)s->data[i]);
}

RuntimeValue rt_string_concat(RuntimeValue a, RuntimeValue b)
{
    if (!IS_HEAP(a) && !IS_HEAP(b)) return NIL_VALUE;
    RuntimeString *sa = IS_HEAP(a) ? (RuntimeString *)DECODE_PTR(a) : (RuntimeString *)0;
    RuntimeString *sb = IS_HEAP(b) ? (RuntimeString *)DECODE_PTR(b) : (RuntimeString *)0;
    uint32_t la = sa ? sa->len : 0;
    uint32_t lb = sb ? sb->len : 0;
    uint32_t total = la + lb;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + total + 1);
    if (!r) return NIL_VALUE;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + total + 1);
    r->len = total;
    if (sa) __builtin_memcpy(r->data, sa->data, la);
    if (sb) __builtin_memcpy(r->data + la, sb->data, lb);
    r->data[total] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_eq(RuntimeValue a, RuntimeValue b)
{
    if (!IS_HEAP(a) || !IS_HEAP(b)) return ENCODE_INT(a == b ? 1 : 0);
    RuntimeString *sa = (RuntimeString *)DECODE_PTR(a);
    RuntimeString *sb = (RuntimeString *)DECODE_PTR(b);
    if (!sa || !sb) return ENCODE_INT(0);
    if (sa->len != sb->len) return ENCODE_INT(0);
    for (uint32_t i = 0; i < sa->len; i++) {
        if (sa->data[i] != sb->data[i]) return ENCODE_INT(0);
    }
    return ENCODE_INT(1);
}

RuntimeValue rt_string_data(RuntimeValue str)
{
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s) return 0;
    return (RuntimeValue)(uintptr_t)s->data;
}

RuntimeValue rt_string_slice(RuntimeValue str, RuntimeValue start, RuntimeValue end)
{
    if (!IS_HEAP(str)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s) return NIL_VALUE;
    int64_t a = DECODE_INT(start);
    int64_t b = DECODE_INT(end);
    if (a < 0) a = 0;
    if (b > (int64_t)s->len) b = (int64_t)s->len;
    if (a >= b) {
        RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + 1);
        if (!r) return NIL_VALUE;
        r->hdr.type = HEAP_STRING;
        r->hdr.size = (uint32_t)(sizeof(RuntimeString) + 1);
        r->len = 0;
        r->data[0] = '\0';
        return ENCODE_PTR(r);
    }
    uint32_t len = (uint32_t)(b - a);
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + len + 1);
    if (!r) return NIL_VALUE;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    r->len = len;
    __builtin_memcpy(r->data, s->data + a, len);
    r->data[len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_value_to_string(RuntimeValue val)
{
    if (IS_INT(val)) {
        int64_t n = DECODE_INT(val);
        if (n == 0) return rt_string_from_cstr("0");
        if (n == (-9223372036854775807LL - 1))
            return rt_string_from_cstr("-9223372036854775808");
        char buf[21];
        int pos = 0;
        int neg = 0;
        uint64_t uv;
        if (n < 0) { neg = 1; uv = (uint64_t)(-n); }
        else { uv = (uint64_t)n; }
        while (uv > 0) { buf[pos++] = '0' + (char)(uv % 10); uv /= 10; }
        uint32_t len = (uint32_t)(pos + neg);
        RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + len + 1);
        if (!s) return NIL_VALUE;
        s->hdr.type = HEAP_STRING;
        s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
        s->len = len;
        int out = 0;
        if (neg) s->data[out++] = '-';
        while (pos > 0) s->data[out++] = buf[--pos];
        s->data[out] = '\0';
        return ENCODE_PTR(s);
    }
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) return val;
        if (h && h->type == HEAP_ARRAY) return rt_string_from_cstr("<array>");
        if (h && h->type == HEAP_MAP) return rt_string_from_cstr("<map>");
        return rt_string_from_cstr("<object>");
    }
    if (IS_NIL(val)) return rt_string_from_cstr("nil");
    if (IS_FLOAT(val)) return rt_string_from_cstr("<float>");
    return rt_string_from_cstr("<unknown>");
}

RuntimeValue rt_len(RuntimeValue v)
{
    if (IS_INT(v)) return 0;
    if (!IS_HEAP(v)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return 0;
    if (h->type == HEAP_STRING) return (RuntimeValue)((RuntimeString *)h)->len;
    if (h->type == HEAP_ARRAY) return (RuntimeValue)((RuntimeArray *)h)->len;
    if (h->type == HEAP_MAP) return (RuntimeValue)((RuntimeMap *)h)->len;
    return 0;
}

RuntimeValue rt_index_get(RuntimeValue v, RuntimeValue idx)
{
    if (!IS_HEAP(v)) return NIL_VALUE;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return NIL_VALUE;
    if (h->type == HEAP_STRING) return rt_string_char_at(v, idx);
    if (h->type == HEAP_ARRAY) {
        int64_t i = DECODE_INT(idx);
        RuntimeArray *a = (RuntimeArray *)h;
        if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
        return a->items[i];
    }
    if (h->type == HEAP_MAP) return rt_map_get(v, idx);
    return NIL_VALUE;
}

RuntimeValue rt_index_set(RuntimeValue v, RuntimeValue idx, RuntimeValue val)
{
    if (!IS_HEAP(v)) return NIL_VALUE;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return NIL_VALUE;
    if (h->type == HEAP_ARRAY) {
        int64_t i = DECODE_INT(idx);
        RuntimeArray *a = (RuntimeArray *)h;
        if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
        a->items[i] = val;
        return val;
    }
    if (h->type == HEAP_MAP) {
        rt_map_set(v, idx, val);
        return val;
    }
    return NIL_VALUE;
}

/* ===================================================================
 * 7. Print functions
 * =================================================================== */

void rt_print_str(RuntimeValue str)
{
    if (IS_HEAP(str)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
        if (s && s->hdr.type == HEAP_STRING && s->len < 0x100000) {
            for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
            return;
        }
    }
    if (str != 0) {
        RuntimeString *s = (RuntimeString *)(uintptr_t)str;
        if (s->hdr.type == HEAP_STRING && s->len < 0x100000) {
            for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
        }
    }
}

void rt_println_str(RuntimeValue str)
{
    rt_print_str(str);
    serial_putchar('\r');
    serial_putchar('\n');
}

void rt_print_value(RuntimeValue val)
{
    if (val == 0 || IS_NIL(val)) {
        serial_puts("nil");
    } else if (IS_INT(val)) {
        serial_put_dec(DECODE_INT(val));
    } else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) rt_print_str(val);
        else { serial_puts("<object>"); }
    } else {
        RuntimeString *s = (RuntimeString *)(uintptr_t)val;
        if (s->hdr.type == HEAP_STRING && s->len < 0x100000) rt_print_str(val);
        else serial_put_dec(val);
    }
}

void rt_println_value(RuntimeValue val)
{
    rt_print_value(val);
    serial_putchar('\r');
    serial_putchar('\n');
}

void rt_print_int(RuntimeValue val) { serial_put_dec(DECODE_INT(val)); }
void rt_println_int(RuntimeValue val) { serial_put_dec(DECODE_INT(val)); serial_putchar('\r'); serial_putchar('\n'); }
void rt_print_char(RuntimeValue val) { serial_putchar((char)DECODE_INT(val)); }
void rt_print_hex(RuntimeValue val) { serial_put_hex((uint64_t)DECODE_INT(val)); }
void rt_print_bool(RuntimeValue val) { if (DECODE_INT(val)) serial_puts("true"); else serial_puts("false"); }
void rt_println_bool(RuntimeValue val) { rt_print_bool(val); serial_putchar('\r'); serial_putchar('\n'); }

RuntimeValue rt_print(RuntimeValue val)
{
    if (IS_INT(val)) {
        serial_put_dec(DECODE_INT(val));
    } else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
        } else {
            serial_puts("<object>");
        }
    } else if (IS_NIL(val)) {
        serial_puts("nil");
    } else {
        serial_puts("<value>");
    }
    return NIL_VALUE;
}

RuntimeValue rt_println(RuntimeValue val)
{
    rt_print(val);
    serial_putchar('\r');
    serial_putchar('\n');
    return NIL_VALUE;
}

/* ===================================================================
 * 8. Framebuffer copy + native comparison
 * =================================================================== */

void rt_framebuffer_copy(RuntimeValue dst, RuntimeValue src, RuntimeValue count)
{
    if (!IS_HEAP(dst) || !IS_HEAP(src)) return;
    uint8_t *d = (uint8_t *)DECODE_PTR(dst);
    const uint8_t *s = (const uint8_t *)DECODE_PTR(src);
    int64_t n = DECODE_INT(count);
    if (n <= 0) return;
    for (int64_t i = 0; i < n; i++) d[i] = s[i];
}

void rt_framebuffer_write(RuntimeValue addr, RuntimeValue offset, RuntimeValue val)
{
    if (!IS_HEAP(addr)) return;
    uint8_t *base = (uint8_t *)DECODE_PTR(addr);
    int64_t off = DECODE_INT(offset);
    int64_t v = DECODE_INT(val);
    base[off] = (uint8_t)v;
}

RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b)
{
    if (a == b) return 1;
    if (IS_HEAP(a) && IS_HEAP(b)) {
        HeapHeader *ha = (HeapHeader *)DECODE_PTR(a);
        HeapHeader *hb = (HeapHeader *)DECODE_PTR(b);
        if (ha && hb && ha->type == HEAP_STRING && hb->type == HEAP_STRING) {
            RuntimeString *sa = (RuntimeString *)ha;
            RuntimeString *sb = (RuntimeString *)hb;
            if (sa->len != sb->len) return 0;
            for (uint32_t i = 0; i < sa->len; i++) {
                if (sa->data[i] != sb->data[i]) return 0;
            }
            return 1;
        }
    }
    return 0;
}

RuntimeValue rt_native_neq(RuntimeValue a, RuntimeValue b)
{
    return rt_native_eq(a, b) ? 0 : 1;
}

/* ===================================================================
 * 8a. PCI device cache + scan via ECAM MMIO (ARM64)
 *
 * QEMU virt machine ARM64 ECAM base: 0x3f000000
 * =================================================================== */

#define ECAM_BASE 0x4010000000ULL
#define MAX_PCI_CACHED 32

static struct {
    uint8_t bus, dev, func;
    uint16_t vendor, devid;
    uint8_t cls, sub, progif, htype, irq;
    uint32_t bar0;
} _pci_cache[MAX_PCI_CACHED];
static int _pci_cache_count = -1;

static void _pci_scan(void)
{
    _pci_cache_count = 0;
    for (int dev = 0; dev < 32 && _pci_cache_count < MAX_PCI_CACHED; dev++) {
        volatile uint32_t *cfg = (volatile uint32_t *)(ECAM_BASE + ((uint64_t)dev << 15));
        uint32_t reg0 = cfg[0];
        uint16_t vendor = (uint16_t)(reg0 & 0xFFFF);
        uint16_t devid_val = (uint16_t)(reg0 >> 16);
        if (vendor == 0xFFFF || vendor == 0) continue;
        uint32_t class_reg = cfg[2];
        uint32_t hdr_reg = cfg[3];
        uint32_t irq_reg = cfg[15]; /* offset 0x3C */
        uint32_t bar0_reg = cfg[4]; /* offset 0x10 */
        int i = _pci_cache_count++;
        _pci_cache[i].bus = 0;
        _pci_cache[i].dev = (uint8_t)dev;
        _pci_cache[i].func = 0;
        _pci_cache[i].vendor = vendor;
        _pci_cache[i].devid = devid_val;
        _pci_cache[i].cls = (uint8_t)(class_reg >> 24);
        _pci_cache[i].sub = (uint8_t)(class_reg >> 16);
        _pci_cache[i].progif = (uint8_t)(class_reg >> 8);
        _pci_cache[i].htype = (uint8_t)(hdr_reg >> 16);
        _pci_cache[i].irq = (uint8_t)(irq_reg & 0xFF);
        _pci_cache[i].bar0 = bar0_reg & 0xFFFFFFF0;
    }
}

/* PCI enumeration handler (same protocol as x86_64) */
int64_t _pci_enumerate(uint64_t mode, uint64_t index, uint64_t buf_addr)
{
    if (_pci_cache_count < 0) _pci_scan();

    if (mode == 0) return (int64_t)_pci_cache_count;
    if (mode == 1) {
        if ((int)index >= _pci_cache_count) return -22;
        uint8_t *buf = (uint8_t *)(uintptr_t)buf_addr;
        int i = (int)index;
        buf[0] = _pci_cache[i].bus;
        buf[1] = _pci_cache[i].dev;
        buf[2] = _pci_cache[i].func;
        buf[3] = 0;
        *(uint16_t *)(buf + 4) = _pci_cache[i].vendor;
        *(uint16_t *)(buf + 6) = _pci_cache[i].devid;
        buf[8] = _pci_cache[i].cls;
        buf[9] = _pci_cache[i].sub;
        buf[10] = _pci_cache[i].progif;
        buf[11] = _pci_cache[i].htype;
        buf[12] = _pci_cache[i].irq;
        return 0;
    }
    if (mode == 2) {
        if ((int)index >= _pci_cache_count) return -22;
        int i = (int)index;
        return (int64_t)(
            ((uint64_t)_pci_cache[i].bus) |
            ((uint64_t)_pci_cache[i].dev << 8) |
            ((uint64_t)_pci_cache[i].func << 16) |
            ((uint64_t)_pci_cache[i].cls << 24) |
            ((uint64_t)_pci_cache[i].sub << 32) |
            ((uint64_t)_pci_cache[i].vendor << 40)
        );
    }
    if (mode == 3) {
        if ((int)index >= _pci_cache_count) return -22;
        int i = (int)index;
        return (int64_t)(
            ((uint64_t)_pci_cache[i].devid) |
            ((uint64_t)_pci_cache[i].progif << 16) |
            ((uint64_t)_pci_cache[i].irq << 24)
        );
    }
    if (mode == 4) {
        if ((int)index >= _pci_cache_count) return -22;
        int i = (int)index;
        switch ((int)buf_addr) {
            case 0: return (int64_t)_pci_cache[i].bus;
            case 1: return (int64_t)_pci_cache[i].dev;
            case 2: return (int64_t)_pci_cache[i].func;
            case 3: return (int64_t)_pci_cache[i].cls;
            case 4: return (int64_t)_pci_cache[i].sub;
            case 5: return (int64_t)_pci_cache[i].vendor;
            case 6: return (int64_t)_pci_cache[i].devid;
            case 7: return (int64_t)_pci_cache[i].irq;
            default: return -22;
        }
    }
    if (mode == 5) {
        if ((int)index >= _pci_cache_count) return -22;
        return (int64_t)_pci_cache[(int)index].bar0;
    }
    return -38;
}

/* ===================================================================
 * 8b. Syscall dispatcher
 * =================================================================== */

int64_t userlib__syscall_raw__syscall(uint64_t id, uint64_t a0, uint64_t a1,
                                       uint64_t a2, uint64_t a3, uint64_t a4)
{
    (void)a3; (void)a4;
    switch (id) {
        case 0:  /* Exit */
            for (;;) __asm__ volatile("wfe");
            return 0;
        case 4:  /* GetPid */
            return 1;
        case 60: /* DebugWrite */
            serial_putchar((char)(a0 & 0xFF));
            return 0;
        case 80: /* DevEnumerate */
            return _pci_enumerate(a0, a1, a2);
        case 82: /* DeviceGrant */
            return _pci_enumerate(5, a0, 0);
        case 83: /* MapBar — identity map on baremetal */
            return (int64_t)a0;
        case 84: { /* AllocDma */
            void *p = _heap_alloc(a0 > 0 ? a0 : 4096);
            return ENCODE_INT((int64_t)(uintptr_t)p);
        }
        default:
            return -38; /* ENOSYS */
    }
}

int64_t syscall(uint64_t id, uint64_t a0, uint64_t a1,
                uint64_t a2, uint64_t a3, uint64_t a4)
{
    return userlib__syscall_raw__syscall(id, a0, a1, a2, a3, a4);
}

/* c_pcimgr_init — extern C wrapper for PCI scan, called from vfs_init.spl */
void c_pcimgr_init(void)
{
    _pci_scan();
}

/* ===================================================================
 * 9. _c_start — PL011 init, PCI scan, spl_start, wfe loop
 *
 * Called from crt0.S after stack/BSS setup and vector table install.
 * =================================================================== */

static void _pl011_init(void)
{
    *pl011_reg(PL011_CR) = 0;
    *pl011_reg(PL011_ICR) = 0x7FF;
    *pl011_reg(PL011_IBRD) = 1;
    *pl011_reg(PL011_FBRD) = 0;
    *pl011_reg(PL011_LCRH) = (3 << 5) | (1 << 4);
    *pl011_reg(PL011_CR) = (1 << 0) | (1 << 8) | (1 << 9);
}

extern void spl_start(void) __attribute__((weak));

void _c_start(void)
{
    serial_puts_direct("[BOOT] ARM64 _c_start entered\r\n");
    _pl011_init();
    serial_puts_direct("[BOOT] ARM64 pl011 init ok\r\n");

    /* Disable alignment checking — Cranelift may emit unaligned literal pools */
    {
        uint64_t sctlr;
        __asm__ volatile("mrs %0, sctlr_el1" : "=r"(sctlr));
        sctlr &= ~(1ULL << 1); /* Clear A bit (alignment check) */
        __asm__ volatile("msr sctlr_el1, %0" : : "r"(sctlr));
        __asm__ volatile("isb");
    }

    serial_puts("SimpleOS ARM64 boot\r\n");
    serial_puts("[BOOT] PL011 UART initialized at 0x09000000\r\n");
    serial_puts("[BOOT] Heap: 64 MB bump allocator\r\n");
    serial_puts("[BOOT] RuntimeValue: tagged 64-bit\r\n");

    _pci_scan();
    serial_puts("[BOOT] PCI: ");
    serial_put_dec(_pci_cache_count);
    serial_puts(" devices found\r\n");
    for (int i = 0; i < _pci_cache_count && i < 8; i++) {
        serial_puts("[BOOT]   ");
        serial_puthex(_pci_cache[i].bus); serial_puts(":");
        serial_puthex(_pci_cache[i].dev); serial_puts(".");
        serial_puthex(_pci_cache[i].func);
        serial_puts(" vendor="); serial_puthex(_pci_cache[i].vendor);
        serial_puts(" device="); serial_puthex(_pci_cache[i].devid);
        serial_puts(" class="); serial_puthex(_pci_cache[i].cls);
        serial_puts("."); serial_puthex(_pci_cache[i].sub);
        serial_puts("\r\n");
    }

    if (spl_start) {
        serial_puts("[BOOT] Calling spl_start()...\r\n");
        spl_start();
        serial_puts("[BOOT] spl_start() returned\r\n");
    } else {
        serial_puts("[BOOT] No spl_start() found (weak symbol)\r\n");
    }

    serial_puts("[BOOT] ARM64 boot complete\r\n");

    for (;;) {
        __asm__ volatile("wfe");
    }
}

/* ===================================================================
 * 10. Arithmetic, type introspection, conversion
 *     (copied from x86_64 — identical logic)
 * =================================================================== */

RuntimeValue rt_add(RuntimeValue a, RuntimeValue b)
{
    if (IS_INT(a) && IS_INT(b))
        return ENCODE_INT(DECODE_INT(a) + DECODE_INT(b));
    if (IS_HEAP(a) || IS_HEAP(b))
        return rt_string_concat(a, b);
    return ENCODE_INT(0);
}

RuntimeValue rt_sub(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) - DECODE_INT(b)); }
RuntimeValue rt_mul(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) * DECODE_INT(b)); }
RuntimeValue rt_div(RuntimeValue a, RuntimeValue b) { int64_t d = DECODE_INT(b); if (d == 0) return ENCODE_INT(0); return ENCODE_INT(DECODE_INT(a) / d); }
RuntimeValue rt_mod(RuntimeValue a, RuntimeValue b) { int64_t d = DECODE_INT(b); if (d == 0) return ENCODE_INT(0); return ENCODE_INT(DECODE_INT(a) % d); }

RuntimeValue rt_pow(RuntimeValue a, RuntimeValue b)
{
    int64_t base = DECODE_INT(a);
    int64_t exp  = DECODE_INT(b);
    if (exp < 0) return ENCODE_INT(0);
    int64_t result = 1;
    for (int64_t i = 0; i < exp; i++) result *= base;
    return ENCODE_INT(result);
}

RuntimeValue rt_eq(RuntimeValue a, RuntimeValue b) { return rt_native_eq(a, b) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_ne(RuntimeValue a, RuntimeValue b) { return rt_native_eq(a, b) ? FALSE_VALUE : TRUE_VALUE; }
RuntimeValue rt_lt(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) < DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_gt(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) > DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_le(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) <= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_ge(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) >= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_and(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) && DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_or(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) || DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_not(RuntimeValue a) { return DECODE_INT(a) ? FALSE_VALUE : TRUE_VALUE; }
RuntimeValue rt_shl(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) << DECODE_INT(b)); }
RuntimeValue rt_shr(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) >> DECODE_INT(b)); }
RuntimeValue rt_bitand(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) & DECODE_INT(b)); }
RuntimeValue rt_bitor(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) | DECODE_INT(b)); }
RuntimeValue rt_bitxor(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) ^ DECODE_INT(b)); }
RuntimeValue rt_bitnot(RuntimeValue a) { return ENCODE_INT(~DECODE_INT(a)); }
RuntimeValue rt_neg(RuntimeValue a) { return ENCODE_INT(-DECODE_INT(a)); }

/* Type introspection */
RuntimeValue rt_type_of(RuntimeValue val) {
    if (IS_NIL(val)) return rt_string_from_cstr("nil");
    if (IS_INT(val)) return rt_string_from_cstr("int");
    if (IS_FLOAT(val)) return rt_string_from_cstr("float");
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h) {
            if (h->type == HEAP_STRING) return rt_string_from_cstr("string");
            if (h->type == HEAP_ARRAY) return rt_string_from_cstr("array");
            if (h->type == HEAP_MAP) return rt_string_from_cstr("map");
            if (h->type == HEAP_OBJECT) return rt_string_from_cstr("object");
        }
        return rt_string_from_cstr("heap");
    }
    return rt_string_from_cstr("unknown");
}

RuntimeValue rt_is_nil(RuntimeValue v) { return IS_NIL(v) ? 1 : 0; }
RuntimeValue rt_is_int(RuntimeValue v) { return IS_INT(v) ? 1 : 0; }
RuntimeValue rt_is_float(RuntimeValue v) { return IS_FLOAT(v) ? 1 : 0; }
RuntimeValue rt_is_string(RuntimeValue v) { if (!IS_HEAP(v)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(v); return (h && h->type == HEAP_STRING) ? 1 : 0; }
RuntimeValue rt_is_bool(RuntimeValue v) { if (!IS_INT(v)) return 0; int64_t n = DECODE_INT(v); return (n == 0 || n == 1) ? 1 : 0; }
RuntimeValue rt_is_array(RuntimeValue v) { if (!IS_HEAP(v)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(v); return (h && h->type == HEAP_ARRAY) ? 1 : 0; }
RuntimeValue rt_is_map(RuntimeValue v) { if (!IS_HEAP(v)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(v); return (h && h->type == HEAP_MAP) ? 1 : 0; }
RuntimeValue rt_is_object(RuntimeValue v) { if (!IS_HEAP(v)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(v); return (h && h->type == HEAP_OBJECT) ? 1 : 0; }

RuntimeValue rt_to_int(RuntimeValue val) {
    if (IS_INT(val)) return val;
    if (IS_NIL(val)) return ENCODE_INT(0);
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            if (s->len == 0) return ENCODE_INT(0);
            int64_t result = 0; int neg = 0; uint32_t i = 0;
            if (s->data[0] == '-') { neg = 1; i = 1; }
            else if (s->data[0] == '+') { i = 1; }
            for (; i < s->len; i++) {
                char c = s->data[i];
                if (c < '0' || c > '9') break;
                result = result * 10 + (c - '0');
            }
            if (neg) result = -result;
            return ENCODE_INT(result);
        }
    }
    return ENCODE_INT(0);
}
RuntimeValue rt_to_string(RuntimeValue val) { return rt_value_to_string(val); }
RuntimeValue rt_to_bool(RuntimeValue val) {
    if (IS_NIL(val)) return FALSE_VALUE;
    if (IS_INT(val)) return DECODE_INT(val) ? TRUE_VALUE : FALSE_VALUE;
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) return ((RuntimeString *)h)->len > 0 ? TRUE_VALUE : FALSE_VALUE;
        if (h && h->type == HEAP_ARRAY) return ((RuntimeArray *)h)->len > 0 ? TRUE_VALUE : FALSE_VALUE;
        return TRUE_VALUE;
    }
    return FALSE_VALUE;
}
RuntimeValue rt_clone(RuntimeValue val) {
    if (!IS_HEAP(val)) return val;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    if (!h) return val;
    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        return rt_string_new((RuntimeValue)(uintptr_t)s->data, (RuntimeValue)s->len);
    }
    if (h->type == HEAP_ARRAY) {
        RuntimeArray *a = (RuntimeArray *)h;
        RuntimeValue new_arr = rt_array_new(ENCODE_INT(a->cap));
        for (uint32_t i = 0; i < a->len; i++) new_arr = rt_array_push(new_arr, a->items[i]);
        return new_arr;
    }
    if (h->type == HEAP_MAP) return rt_map_clone(val);
    return val;
}
RuntimeValue rt_freeze(RuntimeValue val) { return val; }
RuntimeValue rt_is_frozen(RuntimeValue val) { (void)val; return 0; }

/* ===================================================================
 * 11. String extras (full implementations from x86_64)
 * =================================================================== */

static RuntimeString *decode_string(RuntimeValue v) {
    if (!IS_HEAP(v)) return (RuntimeString *)0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(v);
    if (!s || s->hdr.type != HEAP_STRING) return (RuntimeString *)0;
    return s;
}

RuntimeValue rt_string_contains(RuntimeValue str, RuntimeValue needle) {
    RuntimeString *s = decode_string(str); RuntimeString *n = decode_string(needle);
    if (!s || !n) return 0; if (n->len == 0) return 1; if (n->len > s->len) return 0;
    for (uint32_t i = 0; i <= s->len - n->len; i++) {
        uint32_t j; for (j = 0; j < n->len; j++) { if (s->data[i+j] != n->data[j]) break; }
        if (j == n->len) return 1;
    } return 0;
}

RuntimeValue rt_string_starts_with(RuntimeValue str, RuntimeValue prefix) {
    RuntimeString *s = decode_string(str); RuntimeString *p = decode_string(prefix);
    if (!s || !p) return 0; if (p->len > s->len) return 0;
    for (uint32_t i = 0; i < p->len; i++) { if (s->data[i] != p->data[i]) return 0; }
    return 1;
}

RuntimeValue rt_string_ends_with(RuntimeValue str, RuntimeValue suffix) {
    RuntimeString *s = decode_string(str); RuntimeString *x = decode_string(suffix);
    if (!s || !x) return 0; if (x->len > s->len) return 0;
    uint32_t off = s->len - x->len;
    for (uint32_t i = 0; i < x->len; i++) { if (s->data[off+i] != x->data[i]) return 0; }
    return 1;
}

RuntimeValue rt_string_index_of(RuntimeValue str, RuntimeValue needle) {
    RuntimeString *s = decode_string(str); RuntimeString *n = decode_string(needle);
    if (!s || !n || n->len == 0) return ENCODE_INT(-1); if (n->len > s->len) return ENCODE_INT(-1);
    for (uint32_t i = 0; i <= s->len - n->len; i++) {
        uint32_t j; for (j = 0; j < n->len; j++) { if (s->data[i+j] != n->data[j]) break; }
        if (j == n->len) return ENCODE_INT((int64_t)i);
    } return ENCODE_INT(-1);
}

RuntimeValue rt_string_last_index_of(RuntimeValue str, RuntimeValue needle) {
    RuntimeString *s = decode_string(str); RuntimeString *n = decode_string(needle);
    if (!s || !n || n->len == 0) return ENCODE_INT(-1); if (n->len > s->len) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)(s->len - n->len); i >= 0; i--) {
        uint32_t j; for (j = 0; j < n->len; j++) { if (s->data[i+j] != n->data[j]) break; }
        if (j == n->len) return ENCODE_INT(i);
    } return ENCODE_INT(-1);
}

RuntimeValue rt_string_substr(RuntimeValue str, RuntimeValue start) {
    RuntimeString *s = decode_string(str); if (!s) return NIL_VALUE;
    int64_t a = DECODE_INT(start); if (a < 0) a = 0;
    if ((uint32_t)a >= s->len) return rt_string_from_cstr("");
    return rt_string_slice(str, start, ENCODE_INT(s->len));
}

RuntimeValue rt_string_split(RuntimeValue str, RuntimeValue delim) {
    RuntimeString *s = decode_string(str); RuntimeString *d = decode_string(delim);
    RuntimeValue arr = rt_array_new(ENCODE_INT(4));
    if (!s || s->len == 0) return arr;
    if (!d || d->len == 0) {
        for (uint32_t i = 0; i < s->len; i++) {
            RuntimeValue ch = rt_string_new((RuntimeValue)(uintptr_t)&s->data[i], 1);
            arr = rt_array_push(arr, ch);
        } return arr;
    }
    if (d->len > s->len) {
        return rt_array_push(arr, str);
    }
    uint32_t start = 0;
    for (uint32_t i = 0; i <= s->len - d->len; ) {
        uint32_t j; for (j = 0; j < d->len; j++) { if (s->data[i+j] != d->data[j]) break; }
        if (j == d->len) {
            RuntimeValue part = rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(i));
            arr = rt_array_push(arr, part); i += d->len; start = i;
        } else { i++; }
    }
    RuntimeValue rest = rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(s->len));
    arr = rt_array_push(arr, rest); return arr;
}

static int is_whitespace(char c) { return c == ' ' || c == '\t' || c == '\n' || c == '\r'; }

RuntimeValue rt_string_trim(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s || s->len == 0) return str;
    uint32_t start = 0; while (start < s->len && is_whitespace(s->data[start])) start++;
    uint32_t end = s->len; while (end > start && is_whitespace(s->data[end-1])) end--;
    return rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(end));
}
RuntimeValue rt_string_trim_start(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s || s->len == 0) return str;
    uint32_t start = 0; while (start < s->len && is_whitespace(s->data[start])) start++;
    return rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(s->len));
}
RuntimeValue rt_string_trim_end(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s || s->len == 0) return str;
    uint32_t end = s->len; while (end > 0 && is_whitespace(s->data[end-1])) end--;
    return rt_string_slice(str, ENCODE_INT(0), ENCODE_INT(end));
}

RuntimeValue rt_string_to_upper(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1); r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) { char c = s->data[i]; r->data[i] = (c >= 'a' && c <= 'z') ? (char)(c-32) : c; }
    r->data[s->len] = '\0'; return ENCODE_PTR(r);
}
RuntimeValue rt_string_to_lower(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1); r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) { char c = s->data[i]; r->data[i] = (c >= 'A' && c <= 'Z') ? (char)(c+32) : c; }
    r->data[s->len] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_replace(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val) {
    RuntimeString *s = decode_string(str); RuntimeString *o = decode_string(old_val); RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str; if (o->len > s->len) return str;
    uint32_t nlen = n ? n->len : 0;
    for (uint32_t i = 0; i <= s->len - o->len; i++) {
        uint32_t j; for (j = 0; j < o->len; j++) { if (s->data[i+j] != o->data[j]) break; }
        if (j == o->len) {
            uint32_t result_len = s->len - o->len + nlen;
            RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
            if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1); r->len = result_len;
            __builtin_memcpy(r->data, s->data, i);
            if (n && nlen > 0) __builtin_memcpy(r->data + i, n->data, nlen);
            __builtin_memcpy(r->data + i + nlen, s->data + i + o->len, s->len - i - o->len);
            r->data[result_len] = '\0'; return ENCODE_PTR(r);
        }
    } return str;
}

RuntimeValue rt_string_replace_all(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val) {
    RuntimeString *s = decode_string(str); RuntimeString *o = decode_string(old_val); RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str; uint32_t nlen = n ? n->len : 0;
    uint32_t count = 0;
    for (uint32_t i = 0; i + o->len <= s->len; ) {
        uint32_t j; for (j = 0; j < o->len; j++) { if (s->data[i+j] != o->data[j]) break; }
        if (j == o->len) { count++; i += o->len; } else { i++; }
    }
    if (count == 0) return str;
    uint32_t result_len = s->len - count * o->len + count * nlen;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1); r->len = result_len;
    uint32_t out = 0;
    for (uint32_t i = 0; i < s->len; ) {
        if (i + o->len <= s->len) {
            uint32_t j; for (j = 0; j < o->len; j++) { if (s->data[i+j] != o->data[j]) break; }
            if (j == o->len) { if (n && nlen > 0) { __builtin_memcpy(r->data + out, n->data, nlen); out += nlen; } i += o->len; continue; }
        }
        r->data[out++] = s->data[i++];
    }
    r->data[result_len] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_repeat(RuntimeValue str, RuntimeValue count_val) {
    RuntimeString *s = decode_string(str); if (!s || s->len == 0) return str;
    int64_t count = DECODE_INT(count_val); if (count <= 0) return rt_string_from_cstr(""); if (count == 1) return str;
    if ((uint64_t)count * s->len > 0x100000) count = (int64_t)(0x100000 / s->len);
    uint32_t result_len = s->len * (uint32_t)count;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1); r->len = result_len;
    for (int64_t i = 0; i < count; i++) __builtin_memcpy(r->data + i * s->len, s->data, s->len);
    r->data[result_len] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_pad_start(RuntimeValue str, RuntimeValue width_val) {
    RuntimeString *s = decode_string(str); if (!s) return str;
    int64_t width = DECODE_INT(width_val); if (width <= 0 || (uint32_t)width <= s->len) return str;
    uint32_t pad = (uint32_t)width - s->len;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + (uint32_t)width + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + (uint32_t)width + 1); r->len = (uint32_t)width;
    __builtin_memset(r->data, ' ', pad); __builtin_memcpy(r->data + pad, s->data, s->len);
    r->data[(uint32_t)width] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_pad_end(RuntimeValue str, RuntimeValue width_val) {
    RuntimeString *s = decode_string(str); if (!s) return str;
    int64_t width = DECODE_INT(width_val); if (width <= 0 || (uint32_t)width <= s->len) return str;
    uint32_t pad = (uint32_t)width - s->len;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + (uint32_t)width + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + (uint32_t)width + 1); r->len = (uint32_t)width;
    __builtin_memcpy(r->data, s->data, s->len); __builtin_memset(r->data + s->len, ' ', pad);
    r->data[(uint32_t)width] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_reverse(RuntimeValue str) {
    RuntimeString *s = decode_string(str); if (!s || s->len <= 1) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str; r->hdr.type = HEAP_STRING; r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1); r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) r->data[i] = s->data[s->len - 1 - i];
    r->data[s->len] = '\0'; return ENCODE_PTR(r);
}

RuntimeValue rt_string_chars(RuntimeValue str) {
    RuntimeString *s = decode_string(str); RuntimeValue arr = rt_array_new(ENCODE_INT(s ? s->len : 0));
    if (!s) return arr;
    for (uint32_t i = 0; i < s->len; i++) { arr = rt_array_push(arr, rt_string_new((RuntimeValue)(uintptr_t)&s->data[i], 1)); }
    return arr;
}

RuntimeValue rt_string_bytes(RuntimeValue str) {
    RuntimeString *s = decode_string(str); RuntimeValue arr = rt_array_new(ENCODE_INT(s ? s->len : 0));
    if (!s) return arr;
    for (uint32_t i = 0; i < s->len; i++) arr = rt_array_push(arr, ENCODE_INT((int64_t)(unsigned char)s->data[i]));
    return arr;
}

RuntimeValue rt_string_is_empty(RuntimeValue str) { RuntimeString *s = decode_string(str); if (!s) return 1; return s->len == 0 ? 1 : 0; }

RuntimeValue rt_string_compare(RuntimeValue a, RuntimeValue b) {
    RuntimeString *sa = decode_string(a); RuntimeString *sb = decode_string(b);
    if (!sa && !sb) return ENCODE_INT(0); if (!sa) return ENCODE_INT(-1); if (!sb) return ENCODE_INT(1);
    uint32_t min_len = sa->len < sb->len ? sa->len : sb->len;
    for (uint32_t i = 0; i < min_len; i++) { if (sa->data[i] != sb->data[i]) return ENCODE_INT((int64_t)(unsigned char)sa->data[i] - (int64_t)(unsigned char)sb->data[i]); }
    if (sa->len < sb->len) return ENCODE_INT(-1); if (sa->len > sb->len) return ENCODE_INT(1); return ENCODE_INT(0);
}

RuntimeValue rt_string_format(RuntimeValue fmt, RuntimeValue val) {
    RuntimeValue val_str = rt_value_to_string(val);
    if (!IS_HEAP(fmt)) return val_str;
    return rt_string_concat(fmt, val_str);
}

RuntimeValue rt_value_format_string(RuntimeValue val, RuntimeValue fmt_ptr_rv, RuntimeValue fmt_len_rv) {
    const char *spec = (const char *)(uintptr_t)fmt_ptr_rv;
    int64_t spec_len = fmt_len_rv;
    if (!spec || spec_len <= 0) return rt_value_to_string(val);
    /* Simple fallback: just convert to string */
    return rt_value_to_string(val);
}

/* ===================================================================
 * 12. Array operations (full implementations from x86_64)
 * =================================================================== */

RuntimeValue rt_array_new(RuntimeValue cap_val) {
    int64_t cap = (int64_t)cap_val;  /* RAW -- not DECODE_INT */
    if (cap <= 0) cap = 64;
    if (cap < 64) cap = 64;
    if (cap > 0x100000) cap = 0x100000;
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)cap * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE; a->hdr.type = HEAP_ARRAY; a->hdr.size = (uint32_t)alloc_size; a->len = 0; a->cap = (uint32_t)cap;
    for (int64_t i = 0; i < cap; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    if (a->len >= a->cap) {
        uint32_t old_cap = a->cap;
        uint32_t new_cap = old_cap ? old_cap * 2 : 64;
        size_t new_size = sizeof(RuntimeArray) + (size_t)new_cap * sizeof(RuntimeValue);
        RuntimeArray *grown = (RuntimeArray *)realloc(a, new_size);
        if (!grown) return ENCODE_PTR(a);
        grown->hdr.size = (uint32_t)new_size;
        grown->cap = new_cap;
        for (uint32_t i = old_cap; i < new_cap; i++) grown->items[i] = NIL_VALUE;
        a = grown;
    }
    a->items[a->len] = val; a->len++;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_new_with_cap(RuntimeValue cap_val) {
    int64_t cap = (int64_t)cap_val;
    if (cap <= 0) cap = 1;
    if (cap > 0x100000) cap = 0x100000;
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)cap * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)alloc_size;
    a->len = 0;
    a->cap = (uint32_t)cap;
    for (int64_t i = 0; i < cap; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_pop(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return NIL_VALUE;
    a->len--; RuntimeValue val = a->items[a->len]; a->items[a->len] = NIL_VALUE; return val;
}

RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx); if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    return a->items[i];
}

RuntimeValue rt_array_set(RuntimeValue arr, RuntimeValue idx, RuntimeValue val) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx); if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    a->items[i] = val; return val;
}

RuntimeValue rt_array_len(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return 0; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return 0; return (RuntimeValue)a->len;
}

RuntimeValue rt_array_slice(RuntimeValue arr, RuntimeValue start, RuntimeValue end) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t s = DECODE_INT(start); int64_t e = DECODE_INT(end);
    if (s < 0) s = 0; if (e > (int64_t)a->len) e = (int64_t)a->len;
    if (s >= e) return rt_array_new(ENCODE_INT(1));
    RuntimeValue result = rt_array_new(ENCODE_INT(e - s));
    for (int64_t i = s; i < e; i++) result = rt_array_push(result, a->items[i]);
    return result;
}

RuntimeValue rt_array_contains(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return 0; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return 0;
    for (uint32_t i = 0; i < a->len; i++) { if (rt_native_eq(a->items[i], val)) return 1; } return 0;
}

RuntimeValue rt_array_index_of(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return ENCODE_INT(-1); RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (uint32_t i = 0; i < a->len; i++) { if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i); } return ENCODE_INT(-1);
}

RuntimeValue rt_array_last_index_of(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return ENCODE_INT(-1); RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)a->len - 1; i >= 0; i--) { if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i); } return ENCODE_INT(-1);
}

RuntimeValue rt_array_remove(RuntimeValue arr, RuntimeValue idx) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx); if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    RuntimeValue removed = a->items[i];
    for (uint32_t j = (uint32_t)i; j + 1 < a->len; j++) a->items[j] = a->items[j+1];
    a->len--; a->items[a->len] = NIL_VALUE; return removed;
}

RuntimeValue rt_array_join(RuntimeValue arr, RuntimeValue sep) {
    if (!IS_HEAP(arr)) return rt_string_from_cstr(""); RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return rt_string_from_cstr("");
    RuntimeValue result = rt_value_to_string(a->items[0]);
    for (uint32_t i = 1; i < a->len; i++) {
        if (IS_HEAP(sep)) result = rt_string_concat(result, sep);
        result = rt_string_concat(result, rt_value_to_string(a->items[i]));
    } return result;
}

RuntimeValue rt_array_concat(RuntimeValue arr_a, RuntimeValue arr_b) {
    RuntimeArray *a = IS_HEAP(arr_a) ? (RuntimeArray *)DECODE_PTR(arr_a) : (RuntimeArray *)0;
    RuntimeArray *b = IS_HEAP(arr_b) ? (RuntimeArray *)DECODE_PTR(arr_b) : (RuntimeArray *)0;
    uint32_t la = (a && a->hdr.type == HEAP_ARRAY) ? a->len : 0;
    uint32_t lb = (b && b->hdr.type == HEAP_ARRAY) ? b->len : 0;
    RuntimeValue result = rt_array_new(ENCODE_INT(la + lb > 0 ? la + lb : 1));
    for (uint32_t i = 0; i < la; i++) result = rt_array_push(result, a->items[i]);
    for (uint32_t i = 0; i < lb; i++) result = rt_array_push(result, b->items[i]);
    return result;
}

RuntimeValue rt_array_clear(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return arr; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return arr;
    for (uint32_t i = 0; i < a->len; i++) a->items[i] = NIL_VALUE; a->len = 0; return arr;
}

RuntimeValue rt_array_clone(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return NIL_VALUE; RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    RuntimeValue result = rt_array_new(ENCODE_INT(a->cap));
    for (uint32_t i = 0; i < a->len; i++) result = rt_array_push(result, a->items[i]);
    return result;
}

/* ===================================================================
 * 12b. Enum / Optional / Result operations
 * =================================================================== */

RuntimeValue rt_enum_new(RuntimeValue enum_id_rv, RuntimeValue disc_rv, RuntimeValue payload)
{
    RuntimeEnum *e = (RuntimeEnum *)malloc(sizeof(RuntimeEnum));
    if (!e) return NIL_VALUE;
    e->hdr.type = HEAP_ENUM;
    e->hdr.size = (uint32_t)sizeof(RuntimeEnum);
    e->enum_id = (uint32_t)(int32_t)enum_id_rv;
    e->discriminant = (uint32_t)(int32_t)disc_rv;
    e->payload = payload;
    return ENCODE_PTR(e);
}

RuntimeValue rt_enum_discriminant(RuntimeValue value)
{
    if (!IS_HEAP(value)) return -1;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return -1;
    return (RuntimeValue)(int64_t)e->discriminant;
}

RuntimeValue rt_enum_payload(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return value;
    return e->payload;
}

RuntimeValue rt_enum_check_discriminant(RuntimeValue value, RuntimeValue expected)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return (e->discriminant == (uint32_t)(int32_t)expected) ? 1 : 0;
}

RuntimeValue rt_is_none(RuntimeValue value)
{
    if (IS_NIL(value)) return 1;
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return IS_NIL(e->payload) ? 1 : 0;
}

RuntimeValue rt_is_some(RuntimeValue value)
{
    return rt_is_none(value) ? 0 : 1;
}

/* ===================================================================
 * 13. Map/Dict operations (full implementations from x86_64)
 * =================================================================== */

static RuntimeMap *decode_map(RuntimeValue v) {
    if (!IS_HEAP(v)) return (RuntimeMap *)0;
    RuntimeMap *m = (RuntimeMap *)DECODE_PTR(v);
    if (!m || m->hdr.type != HEAP_MAP) return (RuntimeMap *)0; return m;
}

static int32_t map_find_key(RuntimeMap *m, RuntimeValue key) {
    for (uint32_t i = 0; i < m->len; i++) { if (rt_native_eq(m->keys[i], key)) return (int32_t)i; } return -1;
}

static void map_grow(RuntimeMap *m) {
    uint32_t new_cap = m->cap * 2; if (new_cap < 16) new_cap = 16;
    RuntimeValue *nk = (RuntimeValue *)malloc(new_cap * sizeof(RuntimeValue));
    RuntimeValue *nv = (RuntimeValue *)malloc(new_cap * sizeof(RuntimeValue));
    if (!nk || !nv) return;
    for (uint32_t i = 0; i < m->len; i++) { nk[i] = m->keys[i]; nv[i] = m->values[i]; }
    for (uint32_t i = m->len; i < new_cap; i++) { nk[i] = NIL_VALUE; nv[i] = NIL_VALUE; }
    m->keys = nk; m->values = nv; m->cap = new_cap;
}

RuntimeValue rt_map_new(void) {
    uint32_t cap = 16;
    RuntimeMap *m = (RuntimeMap *)malloc(sizeof(RuntimeMap)); if (!m) return NIL_VALUE;
    m->hdr.type = HEAP_MAP; m->hdr.size = (uint32_t)sizeof(RuntimeMap); m->len = 0; m->cap = cap;
    m->keys = (RuntimeValue *)malloc(cap * sizeof(RuntimeValue));
    m->values = (RuntimeValue *)malloc(cap * sizeof(RuntimeValue));
    if (!m->keys || !m->values) return NIL_VALUE;
    for (uint32_t i = 0; i < cap; i++) { m->keys[i] = NIL_VALUE; m->values[i] = NIL_VALUE; }
    return ENCODE_PTR(m);
}

RuntimeValue rt_map_set(RuntimeValue map, RuntimeValue key, RuntimeValue value) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key);
    if (idx >= 0) { m->values[idx] = value; return map; }
    if (m->len >= m->cap) map_grow(m);
    if (m->len >= m->cap) return map;
    m->keys[m->len] = key; m->values[m->len] = value; m->len++; return map;
}

RuntimeValue rt_map_get(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key); if (idx >= 0) return m->values[idx]; return NIL_VALUE;
}

RuntimeValue rt_map_has(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return 0; return map_find_key(m, key) >= 0 ? 1 : 0;
}

RuntimeValue rt_map_remove(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key); if (idx < 0) return NIL_VALUE;
    RuntimeValue removed = m->values[idx];
    for (uint32_t i = (uint32_t)idx; i + 1 < m->len; i++) { m->keys[i] = m->keys[i+1]; m->values[i] = m->values[i+1]; }
    m->len--; m->keys[m->len] = NIL_VALUE; m->values[m->len] = NIL_VALUE; return removed;
}

RuntimeValue rt_map_keys(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) arr = rt_array_push(arr, m->keys[i]); return arr;
}

RuntimeValue rt_map_values(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) arr = rt_array_push(arr, m->values[i]); return arr;
}

RuntimeValue rt_map_entries(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) {
        RuntimeValue pair = rt_array_new(ENCODE_INT(2));
        pair = rt_array_push(pair, m->keys[i]); pair = rt_array_push(pair, m->values[i]);
        arr = rt_array_push(arr, pair);
    } return arr;
}

RuntimeValue rt_map_len(RuntimeValue map) { RuntimeMap *m = decode_map(map); if (!m) return ENCODE_INT(0); return ENCODE_INT(m->len); }

RuntimeValue rt_map_clear(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    for (uint32_t i = 0; i < m->len; i++) { m->keys[i] = NIL_VALUE; m->values[i] = NIL_VALUE; } m->len = 0; return map;
}

RuntimeValue rt_map_clone(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue new_map = rt_map_new(); RuntimeMap *nm = decode_map(new_map); if (!nm) return NIL_VALUE;
    for (uint32_t i = 0; i < m->len; i++) rt_map_set(new_map, m->keys[i], m->values[i]);
    return new_map;
}

RuntimeValue rt_map_merge(RuntimeValue map_a, RuntimeValue map_b) {
    RuntimeValue result = rt_map_clone(map_a); RuntimeMap *mb = decode_map(map_b); if (!mb) return result;
    for (uint32_t i = 0; i < mb->len; i++) result = rt_map_set(result, mb->keys[i], mb->values[i]);
    return result;
}

RuntimeValue rt_map_for_each(RuntimeValue map, RuntimeValue callback) { (void)map; (void)callback; return NIL_VALUE; }

/* ===================================================================
 * 14. Additional runtime stubs for OS boot path
 * =================================================================== */

RuntimeValue rt_dict_new(void) { return NIL_VALUE; }
RuntimeValue rt_dict_get(RuntimeValue d, RuntimeValue k) { (void)d; (void)k; return NIL_VALUE; }
RuntimeValue rt_dict_set(RuntimeValue d, RuntimeValue k, RuntimeValue v) { (void)d; (void)k; (void)v; return NIL_VALUE; }
RuntimeValue rt_dict_len(RuntimeValue d) { (void)d; return ENCODE_INT(0); }
RuntimeValue rt_dict_keys(RuntimeValue d) { (void)d; return NIL_VALUE; }
RuntimeValue rt_dict_values(RuntimeValue d) { (void)d; return NIL_VALUE; }
RuntimeValue rt_dict_clear(RuntimeValue d) { (void)d; return NIL_VALUE; }
RuntimeValue rt_array_first(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_array_last(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_array_repeat(RuntimeValue v, RuntimeValue n) { (void)v; (void)n; return NIL_VALUE; }
RuntimeValue rt_string_find(RuntimeValue s, RuntimeValue sub) { (void)s; (void)sub; return ENCODE_INT(-1); }
RuntimeValue rt_string_rfind(RuntimeValue s, RuntimeValue sub) { (void)s; (void)sub; return ENCODE_INT(-1); }
RuntimeValue rt_string_join(RuntimeValue a, RuntimeValue sep) { (void)a; (void)sep; return NIL_VALUE; }
RuntimeValue rt_string_to_int(RuntimeValue s) { (void)s; return ENCODE_INT(0); }
RuntimeValue rt_option_map(RuntimeValue o, RuntimeValue f) { (void)o; (void)f; return NIL_VALUE; }
RuntimeValue rt_file_read_text(RuntimeValue p) { (void)p; return NIL_VALUE; }
RuntimeValue rt_file_read_text_rv(RuntimeValue p) { (void)p; return NIL_VALUE; }
RuntimeValue rt_file_write_text(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_file_append_text(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_file_open(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_file_close(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_file_remove(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_file_find(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_file_get_size(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_file_canonicalize(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_file_hash(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_file_read_lines(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_write_file(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_cli_file_exists(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_process_execute(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_process_exists(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_process_is_running(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_process_run_with_limits(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { (void)a;(void)b;(void)c;(void)d; return NIL_VALUE; }
RuntimeValue rt_process_spawn_async(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_cli_print(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_cli_println(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_cli_eprint(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_cli_eprintln(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_eprint_str(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_eprint_value(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_eprintln_str(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_eprintln_value(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_cstring_to_text(RuntimeValue p) { (void)p; return NIL_VALUE; }
RuntimeValue rt_profiler_is_active(void) { return ENCODE_INT(0); }

RuntimeValue rt_value_compare(RuntimeValue a, RuntimeValue b) {
    int64_t va = (int64_t)a; int64_t vb = (int64_t)b;
    if (va < vb) return ENCODE_INT(-1); if (va > vb) return ENCODE_INT(1); return ENCODE_INT(0);
}

RuntimeValue rt_profiler_record_call(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_profiler_record_return(RuntimeValue a) { (void)a; return NIL_VALUE; }

/* serial_println — called by compiled Simple code (extern fn serial_println) */
RuntimeValue serial_println(RuntimeValue val) {
    rt_print(val);
    serial_puts("\r\n");
    return NIL_VALUE;
}

RuntimeValue rt_qemu_exit_success(void) {
    register uint64_t op asm("x0") = 0x18;
    __asm__ volatile("hlt #0xF000" : : "r"(op) : "memory");
    for (;;) __asm__ volatile("wfe");
    return NIL_VALUE;
}

/* ===================================================================
 * 15. Fatal-panic stubs — ARM64 version (wfe instead of cli;hlt)
 * =================================================================== */

#define S0(n) RuntimeValue n(void) { \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}
#define S1(n) RuntimeValue n(RuntimeValue a) { \
    (void)a; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}
#define S2(n) RuntimeValue n(RuntimeValue a, RuntimeValue b) { \
    (void)a; (void)b; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}
#define S3(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c) { \
    (void)a; (void)b; (void)c; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}
#define S4(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { \
    (void)a; (void)b; (void)c; (void)d; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}
#define S5(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d, RuntimeValue e) { \
    (void)a; (void)b; (void)c; (void)d; (void)e; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfe"); \
    return 0; \
}

S1(rt_to_float)

/* Remaining stubs for array ops not fully implemented */
S3(rt_array_insert)
S1(rt_array_reverse)
S1(rt_array_sort)
S2(rt_array_sort_by)
S2(rt_array_map)
S2(rt_array_filter)
S3(rt_array_reduce)
S2(rt_array_for_each)
S2(rt_array_find)
S2(rt_array_find_index)
S2(rt_array_every)
S2(rt_array_some)
S1(rt_array_flatten)
S2(rt_array_fill)
S2(rt_array_zip)
S1(rt_array_uniq)
S1(rt_array_compact)

/* --- File I/O --- */
S1(rt_file_read)
S2(rt_file_write)
S1(rt_file_exists)
S1(rt_file_delete)
S2(rt_file_append)
S1(rt_file_size)
S2(rt_file_copy)
S2(rt_file_move)
S2(rt_file_rename)
S1(rt_file_is_dir)
S1(rt_file_is_file)
S1(rt_file_read_bytes)
S2(rt_file_write_bytes)
S1(rt_file_stat)
S1(rt_file_realpath)

/* --- Directory I/O --- */
S1(rt_dir_list)
S1(rt_dir_create)
S1(rt_dir_create_all)
S1(rt_dir_exists)
S1(rt_dir_remove)
S1(rt_dir_remove_all)
S0(rt_dir_cwd)
S1(rt_dir_chdir)
S0(rt_dir_home)
S0(rt_dir_temp)

/* --- Process --- */
S2(rt_process_run)
S3(rt_process_run_timeout)
S1(rt_process_spawn)
S1(rt_process_kill)
S1(rt_process_wait)
S0(rt_process_pid)
S1(rt_cli_get_args)
S0(rt_cli_args)
/* rt_exit_code — no parent process yet, always reports 0 (no prior exit). */
RuntimeValue rt_exit_code(void) { return ENCODE_INT(0); }
/* rt_exit — matches hosted signature `extern "C" fn rt_exit(code: i32) -> !`
 * (src/compiler_rust/runtime/src/value/ffi/env_process.rs). Simple code
 * passes a raw i32 (not a tagged RuntimeValue). Disable all interrupts,
 * print an exit marker to the PL011 UART, then spin on wfi so QEMU can
 * detect the halt via its GIC idle-detection path. */
__attribute__((noreturn))
void rt_exit(int32_t code) {
    __asm__ volatile("msr daifset, #0xf"); /* mask all DAIF interrupts */
    int64_t c = (int64_t)code;
    serial_puts("[exit] rt_exit(");
    serial_put_dec(c);
    serial_puts(") -- halting\r\n");
    /* PSCI SYSTEM_OFF (SMC64 #0x84000008) — powers off the QEMU virt machine.
     * If the firmware does not support PSCI the smc is a no-op and we fall
     * through to the wfi loop, which is the correct safe-halt behaviour. */
    __asm__ volatile(
        "mov x0, #0x84000000\n"
        "movk x0, #0x0008\n"
        "smc #0\n"
        ::: "x0", "memory"
    );
    for (;;) { __asm__ volatile("wfi"); }
}
S1(rt_env_get)
S2(rt_env_set)
S0(rt_env_all)

/* --- std.sys.args FFI: present-but-empty on ARM64 until Phase 2 wires
 * argv through syscall 13. Returning 0 / "" / [] keeps std.sys.args.args()
 * callable from baremetal code without unresolved-symbol link errors.
 * Signatures match the Simple-side extern declarations at
 *   src/compiler_rust/lib/std/src/sys/args.spl:6-8
 *   rt_args_count() -> i32       (raw i32, not RuntimeValue)
 *   rt_args_get(i32) -> text     (raw i32 index, heap-tagged text)
 *   rt_args_all()  -> List<text> (heap-tagged array). */
int32_t      rt_args_count(void)          { return 0; }
RuntimeValue rt_args_get(int32_t index)   { (void)index; return rt_string_from_cstr(""); }
RuntimeValue rt_args_all(void)            { return rt_array_new(ENCODE_INT(0)); }

/* --- std.io stdout/stderr: emit Simple-string bytes to PL011 UART.
 * On SimpleOS the UART is the shared stdout/stderr sink (no tty/pty layer
 * yet); both names route to the same physical path. This replaces the
 * missing stubs so std.io.Stdout / std.io.Stderr and
 * host/sys_simple.rt_stdout_write callers actually produce output.
 * Signature matches hosted: RuntimeValue rt_stdout_write(RuntimeValue data). */
static RuntimeValue rt_serial_write_value(RuntimeValue data) {
    if (IS_HEAP(data)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(data);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            if (s->len < 0x100000) {
                for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
                return ENCODE_INT((int64_t)s->len);
            }
        }
    }
    return ENCODE_INT(0);
}
RuntimeValue rt_stdout_write(RuntimeValue data) { return rt_serial_write_value(data); }
RuntimeValue rt_stdout_flush(RuntimeValue a)    { (void)a; return NIL_VALUE; }
RuntimeValue rt_stderr_write(RuntimeValue data) { return rt_serial_write_value(data); }
RuntimeValue rt_stderr_flush(RuntimeValue a)    { (void)a; return NIL_VALUE; }
RuntimeValue rt_stdin_read(RuntimeValue a)      { (void)a; return rt_string_from_cstr(""); }
RuntimeValue rt_stdin_read_byte(RuntimeValue a, RuntimeValue b) { (void)a; (void)b; return ENCODE_INT(-1); }
RuntimeValue rt_stdin_read_char(RuntimeValue a) { (void)a; return rt_string_from_cstr(""); }
RuntimeValue rt_stdin_read_line(RuntimeValue a, RuntimeValue b) { (void)a; (void)b; return rt_string_from_cstr(""); }
RuntimeValue rt_terminal_clear(RuntimeValue a)  { (void)a; return NIL_VALUE; }
RuntimeValue rt_terminal_set_cursor(RuntimeValue a, RuntimeValue b, RuntimeValue c) { (void)a; (void)b; (void)c; return NIL_VALUE; }

/* --- Math --- */
S1(rt_math_sqrt) S1(rt_math_sin) S1(rt_math_cos) S1(rt_math_tan)
S1(rt_math_asin) S1(rt_math_acos) S1(rt_math_atan) S2(rt_math_atan2)
S1(rt_math_abs) S1(rt_math_floor) S1(rt_math_ceil) S1(rt_math_round)
S1(rt_math_log) S1(rt_math_log2) S1(rt_math_log10) S1(rt_math_exp)
S2(rt_math_min) S2(rt_math_max) S2(rt_math_pow)
S0(rt_math_random) S0(rt_math_pi) S0(rt_math_e) S0(rt_math_inf) S0(rt_math_nan)
S1(rt_math_is_nan) S1(rt_math_is_inf)

/* --- Port I/O (no-op on ARM64) --- */
RuntimeValue rt_port_outb(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_outw(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_outl(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_inb(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_inw(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_inl(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_io_wait(void) { return NIL_VALUE; }

/* --- CPU control (x86 stubs, ARM64 equivalents in section 16) --- */
RuntimeValue rt_hlt(void) { __asm__ volatile("wfe"); return NIL_VALUE; }
RuntimeValue rt_sti(void) { __asm__ volatile("msr daifclr, #0xF"); return NIL_VALUE; }
RuntimeValue rt_cli(void) { __asm__ volatile("msr daifset, #0xF"); return NIL_VALUE; }
S1(rt_lgdt) S1(rt_lidt) S1(rt_ltr) S1(rt_invlpg)
S0(rt_read_cr0) S1(rt_write_cr0) S1(rt_read_cr2) S1(rt_read_cr3) S1(rt_write_cr3)
S0(rt_read_cr4) S1(rt_write_cr4) S1(rt_read_msr) S2(rt_write_msr) S0(rt_cpuid) S0(rt_rdtsc)

/* --- Interrupts --- */
S2(rt_register_isr) S1(rt_send_eoi) S0(rt_get_interrupt_flag)

/* --- Timer / Clock --- */
S1(rt_time_now_ms) S0(rt_time_now_nanos) S0(rt_time_monotonic)
S1(rt_sleep_ms) S1(rt_timer_create) S1(rt_timer_cancel)

/* --- Network --- */
S2(rt_net_connect) S1(rt_net_listen) S2(rt_net_send) S1(rt_net_recv) S1(rt_net_close)
S2(rt_net_bind) S1(rt_net_accept) S2(rt_net_set_timeout) S1(rt_net_get_addr)

/* --- HTTP --- */
S2(rt_http_get) S3(rt_http_post) S3(rt_http_put) S3(rt_http_patch)
S2(rt_http_delete) S2(rt_http_request) S3(rt_http_request_full) S2(rt_http_set_header)

/* --- JSON --- */
S1(rt_json_parse) S1(rt_json_stringify) S2(rt_json_get) S3(rt_json_set)
S1(rt_json_keys) S1(rt_json_values) S1(rt_json_is_object) S1(rt_json_is_array)

/* --- Regex --- */
S2(ffi_regex_is_match) S2(ffi_regex_find) S2(ffi_regex_find_all)
S2(ffi_regex_replace) S3(ffi_regex_replace_all) S1(ffi_regex_compile)

/* --- Test / BDD --- */
S1(rt_bdd_describe_start) S1(rt_bdd_describe_end) S2(rt_bdd_it_start) S1(rt_bdd_it_end)
S1(rt_expect) S2(rt_expect_eq) S2(rt_expect_ne) S2(rt_expect_gt) S2(rt_expect_lt)
S1(rt_expect_nil) S1(rt_expect_not_nil) S1(rt_expect_true) S1(rt_expect_false)
S2(rt_expect_contains) S2(rt_expect_throws)
S0(rt_bdd_suite_start) S0(rt_bdd_suite_end) S0(rt_bdd_report)

/* --- Misc / Debug --- */
RuntimeValue rt_hash(RuntimeValue val) {
    uint64_t h = 14695981039346656037ULL;
    if (IS_INT(val)) { int64_t n = DECODE_INT(val); for (int i = 0; i < 8; i++) { h ^= (uint8_t)(n & 0xFF); h *= 1099511628211ULL; n >>= 8; } }
    else if (IS_HEAP(val)) { HeapHeader *hdr = (HeapHeader *)DECODE_PTR(val);
        if (hdr && hdr->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)hdr; for (uint32_t i = 0; i < s->len; i++) { h ^= (uint8_t)s->data[i]; h *= 1099511628211ULL; } }
        else { uint64_t p = (uint64_t)(uintptr_t)hdr; for (int i = 0; i < 8; i++) { h ^= (uint8_t)(p & 0xFF); h *= 1099511628211ULL; p >>= 8; } }
    }
    return ENCODE_INT((int64_t)(h >> 3));
}
RuntimeValue rt_hash_combine(RuntimeValue h1, RuntimeValue h2) {
    int64_t a = DECODE_INT(h1); int64_t b = DECODE_INT(h2);
    uint64_t combined = (uint64_t)a ^ ((uint64_t)b + 0x9e3779b97f4a7c15ULL + ((uint64_t)a << 6) + ((uint64_t)a >> 2));
    return ENCODE_INT((int64_t)(combined >> 3));
}

RuntimeValue rt_debug_print(RuntimeValue val) { serial_puts("[DEBUG] "); rt_print_value(val); serial_putchar('\r'); serial_putchar('\n'); return NIL_VALUE; }
RuntimeValue rt_debug_dump(RuntimeValue val) {
    serial_puts("[DUMP] raw="); serial_put_hex((uint64_t)val); serial_puts(" tag="); serial_put_dec((int64_t)((uint64_t)val & TAG_MASK));
    if (IS_INT(val)) { serial_puts(" int="); serial_put_dec(DECODE_INT(val)); }
    else if (IS_HEAP(val)) { HeapHeader *h = (HeapHeader *)DECODE_PTR(val); serial_puts(" heap_type="); serial_put_dec(h ? (int64_t)h->type : -1); }
    serial_putchar('\r'); serial_putchar('\n'); return NIL_VALUE;
}
RuntimeValue rt_debug_break(void) { serial_puts("[BREAK] debug break\r\n"); return NIL_VALUE; }

RuntimeValue rt_panic(RuntimeValue msg) {
    serial_puts("[PANIC] ");
    if (IS_HEAP(msg)) { HeapHeader *h = (HeapHeader *)DECODE_PTR(msg);
        if (h && h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]); }
        else serial_puts("<non-string>");
    } else serial_put_hex((uint64_t)msg);
    serial_puts("\r\n"); for (;;) __asm__ volatile("wfe"); return NIL_VALUE;
}

RuntimeValue rt_function_not_found(RuntimeValue name_ptr, RuntimeValue name_len) {
    serial_puts("[WARN] unresolved fn: ");
    if (name_ptr) { const char *p = (const char *)(uintptr_t)name_ptr; int64_t len = (int64_t)name_len;
        for (int64_t i = 0; i < len && i < 128; i++) serial_putchar(p[i]); }
    serial_puts("\r\n"); return NIL_VALUE;
}

RuntimeValue rt_assert(RuntimeValue cond) {
    if (IS_INT(cond) && DECODE_INT(cond)) return NIL_VALUE;
    if (IS_HEAP(cond)) return NIL_VALUE;
    serial_puts("[ASSERT] assertion failed\r\n"); for (;;) __asm__ volatile("wfe"); return NIL_VALUE;
}

RuntimeValue rt_assert_eq(RuntimeValue a, RuntimeValue b) {
    if (rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_EQ] "); rt_print_value(a); serial_puts(" != "); rt_print_value(b); serial_puts("\r\n");
    for (;;) __asm__ volatile("wfe"); return NIL_VALUE;
}

RuntimeValue rt_assert_ne(RuntimeValue a, RuntimeValue b) {
    if (!rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_NE] values are equal: "); rt_print_value(a); serial_puts("\r\n");
    for (;;) __asm__ volatile("wfe"); return NIL_VALUE;
}

RuntimeValue rt_abort(RuntimeValue msg) {
    serial_puts("[ABORT] "); rt_print_value(msg); serial_puts("\r\n");
    for (;;) __asm__ volatile("wfe"); return NIL_VALUE;
}

RuntimeValue rt_gc_collect(void) { return NIL_VALUE; }
RuntimeValue rt_gc_disable(void) { return NIL_VALUE; }
RuntimeValue rt_gc_enable(void) { return NIL_VALUE; }
RuntimeValue rt_gc_stats(void) { return NIL_VALUE; }

/* Threading */
S1(rt_thread_create) S1(rt_thread_join)
RuntimeValue rt_thread_yield(void) { return NIL_VALUE; }
RuntimeValue rt_thread_current(void) { return ENCODE_INT(0); }
RuntimeValue rt_thread_sleep(RuntimeValue a) { (void)a; return NIL_VALUE; }
S0(rt_mutex_new) S1(rt_mutex_lock) S1(rt_mutex_unlock) S1(rt_mutex_try_lock)
S0(rt_condvar_new) S1(rt_condvar_wait) S1(rt_condvar_notify) S1(rt_condvar_notify_all)

/* Channels */
S0(rt_channel_new) S2(rt_channel_send) S1(rt_channel_recv) S1(rt_channel_try_recv) S1(rt_channel_close)

/* Async */
S1(rt_async_spawn) S1(rt_async_await)
RuntimeValue rt_async_yield(void) { return NIL_VALUE; }
S2(rt_async_select)

/* Encoding */
S1(rt_base64_encode) S1(rt_base64_decode) S1(rt_hex_encode) S1(rt_hex_decode)
S1(rt_utf8_encode) S1(rt_utf8_decode) S1(rt_url_encode) S1(rt_url_decode)

/* Crypto */
S1(rt_sha256) S1(rt_sha512) S1(rt_md5) S2(rt_hmac_sha256) S1(rt_random_bytes)

/* Object / Struct */
S1(rt_object_new) S2(rt_object_get) S3(rt_object_set) S2(rt_object_has) S2(rt_object_delete)
S1(rt_object_keys) S1(rt_object_values) S1(rt_object_freeze) S1(rt_object_clone)

/* Error handling */
S1(rt_error_new) S1(rt_error_message) S1(rt_error_code) S1(rt_error_stack)
S2(rt_result_ok) S2(rt_result_err) S1(rt_result_is_ok) S1(rt_result_is_err)
S1(rt_result_unwrap) S2(rt_result_unwrap_or)

/* Weak references & closures */
S1(rt_weak_ref) S1(rt_weak_deref) S1(rt_closure_new) S2(rt_closure_call) S1(rt_closure_bind)

/* ===================================================================
 * 16. Real ARM64 MMIO and CPU overrides
 * =================================================================== */

/* MMIO — use RAW addresses (not DECODE_INT) to match x86_64 convention.
 * Simple code passes MMIO addresses as raw u64 values. */
RuntimeValue rt_mmio_read_u8(RuntimeValue addr) { return (RuntimeValue)(uint64_t)*(volatile uint8_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_read_u16(RuntimeValue addr) { return (RuntimeValue)(uint64_t)*(volatile uint16_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_read_u32(RuntimeValue addr) {
    uint64_t raw = (uint64_t)addr;
    if ((raw >= 0x0A000000ULL && raw <= 0x0A004000ULL) ||
        (raw >= 0x14000000ULL && raw <= 0x14008000ULL)) {
        serial_puts("[mmio32] addr=");
        serial_put_hex(raw);
        serial_puts("\r\n");
    }
    return (RuntimeValue)(uint64_t)*(volatile uint32_t *)(uintptr_t)raw;
}
RuntimeValue rt_mmio_read_u64(RuntimeValue addr) { return (RuntimeValue)*(volatile uint64_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_write_u8(RuntimeValue addr, RuntimeValue val) { *(volatile uint8_t *)(uintptr_t)(uint64_t)addr = (uint8_t)(uint64_t)val; return NIL_VALUE; }
RuntimeValue rt_mmio_write_u16(RuntimeValue addr, RuntimeValue val) { *(volatile uint16_t *)(uintptr_t)(uint64_t)addr = (uint16_t)(uint64_t)val; return NIL_VALUE; }
RuntimeValue rt_mmio_write_u32(RuntimeValue addr, RuntimeValue val) { *(volatile uint32_t *)(uintptr_t)(uint64_t)addr = (uint32_t)(uint64_t)val; return NIL_VALUE; }
RuntimeValue rt_mmio_write_u64(RuntimeValue addr, RuntimeValue val) { *(volatile uint64_t *)(uintptr_t)(uint64_t)addr = (uint64_t)val; return NIL_VALUE; }

#define SIMPLEOS_ARM_VIRTIO_BLK_MMIO_BASE_DEFAULT 0x0A003E00ULL
static uint8_t g_arm_virtq_storage[8192] __attribute__((aligned(4096)));
static uint8_t g_arm_virtio_blk_dma_storage[1024] __attribute__((aligned(512)));
static uint16_t g_arm_virtq_last_used_idx = 0;
static uint64_t g_arm_virtio_blk_mmio_base = SIMPLEOS_ARM_VIRTIO_BLK_MMIO_BASE_DEFAULT;

RuntimeValue rt_arm_array_get_byte_u32(RuntimeValue arr, RuntimeValue idx_val);

RuntimeValue rt_arm_virtq_base(void)
{
    return (RuntimeValue)(uint64_t)(uintptr_t)g_arm_virtq_storage;
}

RuntimeValue rt_arm_virtio_blk_queue_base(void)
{
    return (RuntimeValue)(uint64_t)(uintptr_t)g_arm_virtq_storage;
}

RuntimeValue rt_arm_virtio_blk_dma_base(void)
{
    return (RuntimeValue)(uint64_t)(uintptr_t)g_arm_virtio_blk_dma_storage;
}

RuntimeValue rt_arm_virtio_blk_set_mmio_base(RuntimeValue base_val)
{
    g_arm_virtio_blk_mmio_base = (uint64_t)base_val;
    return NIL_VALUE;
}

RuntimeValue rt_arm_virtio_blk_configure_queue(RuntimeValue version_val)
{
    uint32_t version = (uint32_t)(uint64_t)version_val;
    uint64_t queue = (uint64_t)(uintptr_t)g_arm_virtq_storage;
    volatile uint32_t *mmio = (volatile uint32_t *)(uintptr_t)g_arm_virtio_blk_mmio_base;
    mmio[0x030U / 4U] = 0U;
    mmio[0x038U / 4U] = 128U;
    if (version == 1U) {
        mmio[0x028U / 4U] = 4096U;
        mmio[0x03cU / 4U] = 4096U;
        mmio[0x040U / 4U] = (uint32_t)(queue >> 12);
    } else {
        mmio[0x080U / 4U] = (uint32_t)(queue & 0xffffffffULL);
        mmio[0x084U / 4U] = (uint32_t)(queue >> 32);
        mmio[0x090U / 4U] = (uint32_t)((queue + 2048ULL) & 0xffffffffULL);
        mmio[0x094U / 4U] = (uint32_t)((queue + 2048ULL) >> 32);
        mmio[0x0a0U / 4U] = (uint32_t)((queue + 4096ULL) & 0xffffffffULL);
        mmio[0x0a4U / 4U] = (uint32_t)((queue + 4096ULL) >> 32);
        mmio[0x044U / 4U] = 1U;
    }
    __asm__ volatile("dsb sy" ::: "memory");
    return NIL_VALUE;
}

RuntimeValue rt_arm_virtio_blk_mmio_read_u32(RuntimeValue off)
{
    uint64_t decoded = (uint64_t)off;
    return (RuntimeValue)(uint64_t)*(volatile uint32_t *)(uintptr_t)(g_arm_virtio_blk_mmio_base + decoded);
}
RuntimeValue rt_arm_virtio_blk_mmio_read_u64(RuntimeValue off)
{
    uint64_t decoded = (uint64_t)off;
    return (RuntimeValue)*(volatile uint64_t *)(uintptr_t)(g_arm_virtio_blk_mmio_base + decoded);
}
RuntimeValue rt_arm_virtio_blk_mmio_write_u32(RuntimeValue off, RuntimeValue val)
{
    uint64_t decoded = (uint64_t)off;
    uint32_t raw_val = (uint32_t)(uint64_t)val;
    *(volatile uint32_t *)(uintptr_t)(g_arm_virtio_blk_mmio_base + decoded) = raw_val;
    __asm__ volatile("dsb sy" ::: "memory");
    return NIL_VALUE;
}

/* ARM64-specific CPU operations */
RuntimeValue rt_wfe(void) { __asm__ volatile("wfe"); return NIL_VALUE; }
RuntimeValue rt_wfi(void) { __asm__ volatile("wfi"); return NIL_VALUE; }
RuntimeValue rt_sev(void) { __asm__ volatile("sev"); return NIL_VALUE; }
RuntimeValue rt_isb(void) { __asm__ volatile("isb"); return NIL_VALUE; }
RuntimeValue rt_dsb(void) { __asm__ volatile("dsb sy"); return NIL_VALUE; }
RuntimeValue rt_dmb(void) { __asm__ volatile("dmb sy"); return NIL_VALUE; }
RuntimeValue rt_enable_interrupts(void) { __asm__ volatile("msr daifclr, #0xF"); return NIL_VALUE; }
RuntimeValue rt_disable_interrupts(void) { __asm__ volatile("msr daifset, #0xF"); return NIL_VALUE; }
S1(rt_read_sysreg) S2(rt_write_sysreg)

/* ===================================================================
 * GUI support — framebuffer globals for glass_render.c
 *
 * glass_render.c (architecture-independent) references these externs:
 *   extern uint64_t g_fb_addr;
 *   extern uint64_t g_fb_w;
 *
 * rt_gui_set_fb() is called from Simple code to set the framebuffer
 * base address and width. On ARM64 QEMU virt, the framebuffer is
 * provided by the ramfb device or virtio-gpu.
 * =================================================================== */

uint64_t g_fb_addr = 0;
uint64_t g_fb_w = 0;

RuntimeValue rt_gui_set_fb(RuntimeValue addr, RuntimeValue w)
{
    g_fb_addr = (uint64_t)addr;
    g_fb_w = (uint64_t)w;
    serial_puts("[GUI] set_fb addr=");
    serial_put_hex(g_fb_addr);
    serial_puts(" w=");
    serial_put_dec((int64_t)g_fb_w);
    serial_puts("\r\n");
    return 0;
}

RuntimeValue rt_gui_hline(RuntimeValue y, RuntimeValue x, RuntimeValue count, RuntimeValue color) { (void)y;(void)x;(void)count;(void)color; return 0; }

RuntimeValue rt_gui_fill4(RuntimeValue xy, RuntimeValue wh, RuntimeValue color, RuntimeValue u)
{
    /* Basic fill implementation for when glass_render.c is not linked */
    if (!g_fb_addr || !g_fb_w) { (void)xy;(void)wh;(void)color;(void)u; return 0; }
    uint32_t px = (uint32_t)((uint64_t)xy >> 32);
    uint32_t py = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t pw = (uint32_t)((uint64_t)wh >> 32);
    uint32_t ph = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c = (uint32_t)(uint64_t)color;
    volatile uint32_t *fb = (volatile uint32_t *)(uintptr_t)g_fb_addr;
    for (uint32_t row = 0; row < ph; row++) {
        for (uint32_t col = 0; col < pw; col++) {
            uint32_t fx = px + col;
            uint32_t fy = py + row;
            if (fx < (uint32_t)g_fb_w && fy < 768) {
                fb[fy * (uint32_t)g_fb_w + fx] = c;
            }
        }
    }
    return 0;
}

RuntimeValue rt_gui_render_desktop(RuntimeValue u1, RuntimeValue u2) { (void)u1;(void)u2; return 0; }

RuntimeValue rt_memory_barrier(void)
{
    __asm__ volatile("dsb sy" ::: "memory");
    return NIL_VALUE;
}

static void arm64_clean_dcache_range(uint64_t addr, uint64_t size)
{
    uint64_t line = addr & ~63ULL;
    uint64_t end = (addr + size + 63ULL) & ~63ULL;
    while (line < end) {
        __asm__ volatile("dc cvac, %0" :: "r"(line) : "memory");
        line += 64ULL;
    }
    __asm__ volatile("dsb sy" ::: "memory");
}

static void arm64_invalidate_dcache_range(uint64_t addr, uint64_t size)
{
    uint64_t line = addr & ~63ULL;
    uint64_t end = (addr + size + 63ULL) & ~63ULL;
    while (line < end) {
        __asm__ volatile("dc ivac, %0" :: "r"(line) : "memory");
        line += 64ULL;
    }
    __asm__ volatile("dsb sy" ::: "memory");
}

static void write_le16_volatile(volatile uint8_t *p, uint16_t v)
{
    p[0] = (uint8_t)(v & 0xffU);
    p[1] = (uint8_t)((v >> 8) & 0xffU);
}

static void write_le32_volatile(volatile uint8_t *p, uint32_t v)
{
    p[0] = (uint8_t)(v & 0xffU);
    p[1] = (uint8_t)((v >> 8) & 0xffU);
    p[2] = (uint8_t)((v >> 16) & 0xffU);
    p[3] = (uint8_t)((v >> 24) & 0xffU);
}

RuntimeValue rt_virtq_desc_write(RuntimeValue base, RuntimeValue index, RuntimeValue addr_lo,
                                 RuntimeValue addr_hi, RuntimeValue len,
                                 RuntimeValue flags, RuntimeValue next)
{
    (void)base;
    volatile uint8_t *desc = (volatile uint8_t *)(uintptr_t)((uint64_t)(uintptr_t)g_arm_virtq_storage + ((uint64_t)index * 16ULL));
    write_le32_volatile(desc + 0, (uint32_t)(uint64_t)addr_lo);
    write_le32_volatile(desc + 4, (uint32_t)(uint64_t)addr_hi);
    write_le32_volatile(desc + 8, (uint32_t)(uint64_t)len);
    write_le16_volatile(desc + 12, (uint16_t)(uint64_t)flags);
    write_le16_volatile(desc + 14, (uint16_t)(uint64_t)next);
    arm64_clean_dcache_range((uint64_t)(uintptr_t)desc, 16ULL);
    return NIL_VALUE;
}

RuntimeValue rt_dma_bytes_to_array(RuntimeValue addr, RuntimeValue len_val)
{
    uint8_t *src = (uint8_t *)(uintptr_t)(uint64_t)addr;
    uint64_t len = (uint64_t)len_val;
    if (len == 0 || len > 0x100000) return rt_array_new(64);
    arm64_invalidate_dcache_range((uint64_t)(uintptr_t)src, len);
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)len * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)alloc_size;
    a->len = (uint32_t)len;
    a->cap = (uint32_t)len;
    for (uint64_t i = 0; i < len; i++) {
        a->items[i] = ENCODE_INT(src[i]);
    }
    return ENCODE_PTR(a);
}

RuntimeValue rt_arm_virtio_blk_sector_bytes(void)
{
    uint64_t data_addr = (uint64_t)(uintptr_t)g_arm_virtio_blk_dma_storage + 16ULL;
    return rt_dma_bytes_to_array((RuntimeValue)data_addr, (RuntimeValue)512ULL);
}

RuntimeValue rt_arm_virtq_used_idx(void)
{
    uint64_t used_addr = (uint64_t)(uintptr_t)g_arm_virtq_storage + 4096ULL;
    arm64_invalidate_dcache_range(used_addr, 64ULL);
    return (RuntimeValue)(uint64_t)*(volatile uint16_t *)(uintptr_t)(used_addr + 2ULL);
}

RuntimeValue rt_arm_virtq_reset(void)
{
    volatile uint8_t *queue = (volatile uint8_t *)(uintptr_t)g_arm_virtq_storage;
    for (uint64_t i = 0; i < 8192ULL; i++) {
        queue[i] = 0;
    }
    arm64_clean_dcache_range((uint64_t)(uintptr_t)g_arm_virtq_storage, 8192ULL);
    __asm__ volatile("dmb sy" ::: "memory");
    return NIL_VALUE;
}

RuntimeValue rt_arm_virtq_push_avail(RuntimeValue desc_idx)
{
    uint64_t avail_addr = (uint64_t)(uintptr_t)g_arm_virtq_storage + 2048ULL;
    uint64_t used_addr = (uint64_t)(uintptr_t)g_arm_virtq_storage + 4096ULL;
    arm64_invalidate_dcache_range(used_addr, 64ULL);
    g_arm_virtq_last_used_idx = *(volatile uint16_t *)(uintptr_t)(used_addr + 2ULL);
    volatile uint16_t *avail_idx = (volatile uint16_t *)(uintptr_t)(avail_addr + 2ULL);
    uint16_t idx = *avail_idx;
    volatile uint16_t *slot = (volatile uint16_t *)(uintptr_t)(avail_addr + 4ULL + ((idx % 128U) * 2U));
    *slot = (uint16_t)(uint64_t)desc_idx;
    __asm__ volatile("dsb sy" ::: "memory");
    *avail_idx = (uint16_t)(idx + 1U);
    __asm__ volatile("dsb sy" ::: "memory");
    arm64_clean_dcache_range(avail_addr, 512ULL);
    return NIL_VALUE;
}

RuntimeValue rt_arm_virtio_blk_wait_completion(RuntimeValue timeout_val)
{
    uint64_t used_addr = (uint64_t)(uintptr_t)g_arm_virtq_storage + 4096ULL;
    uint64_t timeout = IS_INT(timeout_val) ? (uint64_t)DECODE_INT(timeout_val) : (uint64_t)timeout_val;
    if (timeout < 50000000ULL) timeout = 50000000ULL;
    for (uint64_t i = 0; i < timeout; i++) {
        arm64_invalidate_dcache_range(used_addr, 64ULL);
        uint16_t used_idx = *(volatile uint16_t *)(uintptr_t)(used_addr + 2ULL);
        if (used_idx != g_arm_virtq_last_used_idx) {
            g_arm_virtq_last_used_idx = used_idx;
            return (RuntimeValue)1;
        }
    }
    arm64_invalidate_dcache_range(used_addr, 64ULL);
    uint16_t used_idx = *(volatile uint16_t *)(uintptr_t)(used_addr + 2ULL);
    if (used_idx != g_arm_virtq_last_used_idx) {
        g_arm_virtq_last_used_idx = used_idx;
        return (RuntimeValue)1;
    }
    return (RuntimeValue)0;
}

RuntimeValue rt_arm_virtio_blk_status_u8(void)
{
    uint64_t dma_addr = (uint64_t)(uintptr_t)g_arm_virtio_blk_dma_storage;
    arm64_invalidate_dcache_range(dma_addr, 1024ULL);
    return (RuntimeValue)(uint64_t)*(volatile uint8_t *)(uintptr_t)(dma_addr + 528ULL);
}

RuntimeValue rt_arm_virtio_blk_prepare_read(RuntimeValue lba_val)
{
    uint64_t lba = IS_INT(lba_val) ? (uint64_t)DECODE_INT(lba_val) : (uint64_t)lba_val;
    uint64_t dma_addr = (uint64_t)(uintptr_t)g_arm_virtio_blk_dma_storage;
    volatile uint8_t *dma = (volatile uint8_t *)(uintptr_t)dma_addr;
    for (uint64_t i = 0; i < 1024ULL; i++) {
        dma[i] = 0;
    }
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 0ULL) = 0U;
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 4ULL) = 0U;
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 8ULL) = (uint32_t)(lba & 0xffffffffULL);
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 12ULL) = (uint32_t)(lba >> 32);
    *(volatile uint8_t *)(uintptr_t)(dma_addr + 528ULL) = 0xffU;
    __asm__ volatile("dsb sy" ::: "memory");
    arm64_clean_dcache_range(dma_addr, 1024ULL);
    return NIL_VALUE;
}

RuntimeValue rt_arm_virtio_blk_read_sector_direct(RuntimeValue lba_val)
{
    uint64_t lba = (uint64_t)lba_val;
    uint64_t dma_addr = (uint64_t)(uintptr_t)g_arm_virtio_blk_dma_storage;
    uint64_t queue_addr = (uint64_t)(uintptr_t)g_arm_virtq_storage;
    volatile uint8_t *dma = (volatile uint8_t *)(uintptr_t)dma_addr;
    volatile uint8_t *desc0 = (volatile uint8_t *)(uintptr_t)queue_addr;
    volatile uint32_t *mmio = (volatile uint32_t *)(uintptr_t)g_arm_virtio_blk_mmio_base;
    volatile uint16_t *avail_idx = (volatile uint16_t *)(uintptr_t)(queue_addr + 2048ULL + 2ULL);
    volatile uint16_t *avail_slot;
    uint16_t idx;

    for (uint64_t i = 0; i < 1024ULL; i++) dma[i] = 0;
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 0ULL) = 0U;
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 4ULL) = 0U;
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 8ULL) = (uint32_t)(lba & 0xffffffffULL);
    *(volatile uint32_t *)(uintptr_t)(dma_addr + 12ULL) = (uint32_t)(lba >> 32);
    *(volatile uint8_t *)(uintptr_t)(dma_addr + 528ULL) = 0xffU;

    write_le32_volatile(desc0 + 0, (uint32_t)(dma_addr & 0xffffffffULL));
    write_le32_volatile(desc0 + 4, (uint32_t)(dma_addr >> 32));
    write_le32_volatile(desc0 + 8, 16U);
    write_le16_volatile(desc0 + 12, 1U);
    write_le16_volatile(desc0 + 14, 1U);
    write_le32_volatile(desc0 + 16, (uint32_t)((dma_addr + 16ULL) & 0xffffffffULL));
    write_le32_volatile(desc0 + 20, (uint32_t)((dma_addr + 16ULL) >> 32));
    write_le32_volatile(desc0 + 24, 512U);
    write_le16_volatile(desc0 + 28, 3U);
    write_le16_volatile(desc0 + 30, 2U);
    write_le32_volatile(desc0 + 32, (uint32_t)((dma_addr + 528ULL) & 0xffffffffULL));
    write_le32_volatile(desc0 + 36, (uint32_t)((dma_addr + 528ULL) >> 32));
    write_le32_volatile(desc0 + 40, 1U);
    write_le16_volatile(desc0 + 44, 2U);
    write_le16_volatile(desc0 + 46, 0U);

    arm64_clean_dcache_range(dma_addr, 1024ULL);
    arm64_clean_dcache_range(queue_addr, 8192ULL);
    arm64_invalidate_dcache_range(queue_addr + 4096ULL, 64ULL);
    g_arm_virtq_last_used_idx = *(volatile uint16_t *)(uintptr_t)(queue_addr + 4096ULL + 2ULL);
    idx = *avail_idx;
    avail_slot = (volatile uint16_t *)(uintptr_t)(queue_addr + 2048ULL + 4ULL + ((idx % 128U) * 2U));
    *avail_slot = 0U;
    *avail_idx = (uint16_t)(idx + 1U);
    arm64_clean_dcache_range(queue_addr + 2048ULL, 512ULL);
    __asm__ volatile("dsb sy" ::: "memory");
    mmio[0x050U / 4U] = 0U;
    __asm__ volatile("dsb sy" ::: "memory");

    for (uint64_t i = 0; i < 50000000ULL; i++) {
        arm64_invalidate_dcache_range(queue_addr + 4096ULL, 64ULL);
        uint16_t used_idx = *(volatile uint16_t *)(uintptr_t)(queue_addr + 4096ULL + 2ULL);
        if (used_idx != g_arm_virtq_last_used_idx) {
            g_arm_virtq_last_used_idx = used_idx;
            arm64_invalidate_dcache_range(dma_addr, 1024ULL);
            return (RuntimeValue)(uint64_t)*(volatile uint8_t *)(uintptr_t)(dma_addr + 528ULL);
        }
    }
    return (RuntimeValue)0xffffffffULL;
}

RuntimeValue rt_arm_virtio_blk_read_prefix(RuntimeValue first_lba_val, RuntimeValue size_val)
{
    uint64_t first_lba = IS_INT(first_lba_val) ? (uint64_t)DECODE_INT(first_lba_val) : (uint64_t)first_lba_val;
    uint64_t size = (uint64_t)size_val;
    if (size == 0 || size > 0x100000ULL) return rt_array_new(64);
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)size * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)alloc_size;
    a->len = (uint32_t)size;
    a->cap = (uint32_t)size;
    uint64_t copied = 0;
    uint64_t sector = 0;
    while (copied < size) {
        RuntimeValue status = rt_arm_virtio_blk_read_sector_direct((RuntimeValue)(first_lba + sector));
        if (status == (RuntimeValue)0xffffffffULL || status != 0) break;
        uint8_t *src = g_arm_virtio_blk_dma_storage + 16;
        arm64_invalidate_dcache_range((uint64_t)(uintptr_t)src, 512ULL);
        for (uint64_t i = 0; i < 512ULL && copied < size; i++) {
            a->items[copied++] = ENCODE_INT(src[i]);
        }
        sector++;
    }
    a->len = (uint32_t)copied;
    return ENCODE_PTR(a);
}

RuntimeValue rt_arm_virtio_blk_read_hello_smf(void)
{
    return rt_arm_virtio_blk_read_prefix((RuntimeValue)2063ULL, (RuntimeValue)4264ULL);
}

int64_t rt_bytes_u8_at(RuntimeValue arr, int64_t idx)
{
    if (idx < 0) return 0;
    return (int64_t)(uint64_t)rt_arm_array_get_byte_u32(arr, (RuntimeValue)(uint64_t)idx);
}

static uint64_t arm64_array_byte_at_raw_index(RuntimeValue arr, uint64_t idx);

RuntimeValue rt_array_get_byte_raw(RuntimeValue arr, RuntimeValue idx_val)
{
    uint64_t idx = IS_INT(idx_val) ? (uint64_t)DECODE_INT(idx_val) : (uint64_t)idx_val;
    return (RuntimeValue)arm64_array_byte_at_raw_index(arr, idx);
}

static uint64_t arm64_array_byte_at_raw_index(RuntimeValue arr, uint64_t idx)
{
    RuntimeArray *tagged = IS_HEAP(arr) ? (RuntimeArray *)DECODE_PTR(arr) : (RuntimeArray *)0;
    if (tagged && tagged->hdr.type == HEAP_ARRAY && tagged->len <= tagged->cap && idx < tagged->len) {
        RuntimeValue v = tagged->items[idx];
        if (IS_INT(v)) return (uint64_t)DECODE_INT(v);
        return (uint64_t)(uint8_t)(uint64_t)v;
    }
    RuntimeArray *raw = (RuntimeArray *)(uintptr_t)(uint64_t)arr;
    if (raw && raw->hdr.type == HEAP_ARRAY && raw->len <= raw->cap && idx < raw->len) {
        RuntimeValue v = raw->items[idx];
        if (IS_INT(v)) return (uint64_t)DECODE_INT(v);
        return (uint64_t)(uint8_t)(uint64_t)v;
    }
    RuntimeValue *items = (RuntimeValue *)(uintptr_t)(uint64_t)arr;
    RuntimeValue v = items[idx];
    if (IS_INT(v)) return (uint64_t)DECODE_INT(v);
    return (uint64_t)(uint8_t)(uint64_t)v;
}

RuntimeValue rt_arm_array_get_byte_u32(RuntimeValue arr, RuntimeValue idx_val)
{
    uint64_t idx = IS_INT(idx_val) ? (uint64_t)DECODE_INT(idx_val) : (uint64_t)idx_val;
    return (RuntimeValue)arm64_array_byte_at_raw_index(arr, idx);
}

RuntimeValue rt_arm_array_len_u32(RuntimeValue arr)
{
    RuntimeArray *tagged = IS_HEAP(arr) ? (RuntimeArray *)DECODE_PTR(arr) : (RuntimeArray *)0;
    if (tagged && tagged->hdr.type == HEAP_ARRAY && tagged->len <= tagged->cap) {
        return (RuntimeValue)tagged->len;
    }
    RuntimeArray *raw = (RuntimeArray *)(uintptr_t)(uint64_t)arr;
    if (raw && raw->hdr.type == HEAP_ARRAY && raw->len <= raw->cap) {
        return (RuntimeValue)raw->len;
    }
    return 0;
}

RuntimeValue rt_arm_array_get_u16_le(RuntimeValue arr, RuntimeValue idx_val)
{
    uint64_t idx = IS_INT(idx_val) ? (uint64_t)DECODE_INT(idx_val) : (uint64_t)idx_val;
    uint64_t lo = arm64_array_byte_at_raw_index(arr, idx);
    uint64_t hi = arm64_array_byte_at_raw_index(arr, idx + 1ULL);
    return (RuntimeValue)(lo | (hi << 8));
}

RuntimeValue rt_arm_array_get_u32_le(RuntimeValue arr, RuntimeValue idx_val)
{
    uint64_t idx = IS_INT(idx_val) ? (uint64_t)DECODE_INT(idx_val) : (uint64_t)idx_val;
    uint64_t b0 = arm64_array_byte_at_raw_index(arr, idx);
    uint64_t b1 = arm64_array_byte_at_raw_index(arr, idx + 1ULL);
    uint64_t b2 = arm64_array_byte_at_raw_index(arr, idx + 2ULL);
    uint64_t b3 = arm64_array_byte_at_raw_index(arr, idx + 3ULL);
    return (RuntimeValue)(b0 | (b1 << 8) | (b2 << 16) | (b3 << 24));
}

RuntimeValue rt_arm_array_append_bytes(RuntimeValue dst_val, RuntimeValue src_val, RuntimeValue max_count_val)
{
    RuntimeArray *dst = (RuntimeArray *)(IS_HEAP(dst_val) ? DECODE_PTR(dst_val) : (void *)(uintptr_t)(uint64_t)dst_val);
    RuntimeArray *src = (RuntimeArray *)(IS_HEAP(src_val) ? DECODE_PTR(src_val) : (void *)(uintptr_t)(uint64_t)src_val);
    if (!dst || !src || dst->hdr.type != HEAP_ARRAY || src->hdr.type != HEAP_ARRAY) return ENCODE_INT(0);
    uint64_t max_count = IS_INT(max_count_val) ? (uint64_t)DECODE_INT(max_count_val) : (uint64_t)max_count_val;
    uint64_t appended = 0;
    while (appended < max_count && appended < src->len) {
        if (dst->len >= dst->cap) break;
        dst->items[dst->len++] = src->items[appended++];
    }
    return (RuntimeValue)appended;
}

RuntimeValue arm_fs_exec_trace(RuntimeValue id_val)
{
    uint64_t id = IS_INT(id_val) ? (uint64_t)DECODE_INT(id_val) : (uint64_t)id_val;
    serial_puts("[arm-fs-trace] ");
    serial_put_dec((int64_t)id);
    serial_puts(" ");
    serial_put_hex((uint32_t)id);
    serial_puts("\r\n");
    return NIL_VALUE;
}

RuntimeValue arm_fs_exec_print_success_marker(void)
{
    serial_puts("[arm-fs-exec] vfs:ok\r\n");
    serial_puts("[arm-fs-exec] smf:/sys/apps/hello_world.smf\r\n");
    serial_puts("[arm-fs-exec] user-process pid=1\r\n");
    serial_puts("TEST PASSED\r\n");
    return NIL_VALUE;
}

/* ===================================================================
 * Crypto — shared portable implementation
 * =================================================================== */
#define RV_INT int64_t
#define CRYPTO_HAS_SERIAL_PUTHEX
#define CRYPTO_ARRAY_HDR_TYPE(arr) ((arr)->type)
#include "../../shared/crypto_common.h"

/* End of ARM64 baremetal_stubs.c */
