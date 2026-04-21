/*
 * SimpleOS RISC-V64 Baremetal Runtime Stubs
 *
 * Provides a complete freestanding runtime for the Simple language compiler
 * targeting RISC-V64 bare-metal (QEMU virt, OpenSBI, 16550 UART at 0x10000000).
 *
 * Sections:
 *   1. Includes and types
 *   2. Serial I/O (16550 UART at MMIO 0x10000000)
 *   3. RuntimeValue tagging
 *   4. Heap allocator (bump, 64 MB)
 *   5. Memory functions
 *   6. String operations
 *   7. Print functions
 *   8. Comparison / Arithmetic / Type introspection
 *   9. Array operations
 *  10. Map/Dict operations
 *  11. Index/Len dispatch
 *  12. PCI enumeration (ECAM MMIO)
 *  13. Syscall dispatcher
 *  14. MMIO / Port I/O stubs
 *  15. _start entry point
 *  16. Fatal-panic stubs
 *  17. Additional runtime stubs
 */

/* ===================================================================
 * 1. Includes and types
 * =================================================================== */

#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

/* ===================================================================
 * 2. Serial I/O — 16550 UART at MMIO 0x10000000 (QEMU virt machine)
 * =================================================================== */

#define UART_BASE       0x10000000UL

#define UART_THR        (*(volatile uint8_t *)(UART_BASE + 0))
#define UART_RBR        (*(volatile uint8_t *)(UART_BASE + 0))
#define UART_IER        (*(volatile uint8_t *)(UART_BASE + 1))
#define UART_FCR        (*(volatile uint8_t *)(UART_BASE + 2))
#define UART_LCR        (*(volatile uint8_t *)(UART_BASE + 3))
#define UART_MCR        (*(volatile uint8_t *)(UART_BASE + 4))
#define UART_LSR        (*(volatile uint8_t *)(UART_BASE + 5))

#define UART_LSR_THRE   0x20
#define UART_LSR_DR     0x01
#define UART_LCR_DLAB   0x80

static void _uart_init(void)
{
    *(volatile uint8_t *)(UART_BASE + 1) = 0x00;  /* Disable all interrupts */
    *(volatile uint8_t *)(UART_BASE + 3) = 0x80;  /* Enable DLAB */
    *(volatile uint8_t *)(UART_BASE + 0) = 0x01;  /* Divisor low byte (115200 baud) */
    *(volatile uint8_t *)(UART_BASE + 1) = 0x00;  /* Divisor high byte */
    *(volatile uint8_t *)(UART_BASE + 3) = 0x03;  /* 8 bits, no parity, 1 stop bit (8N1) */
    *(volatile uint8_t *)(UART_BASE + 2) = 0x07;  /* Enable FIFO, clear, 1-byte threshold */
    *(volatile uint8_t *)(UART_BASE + 4) = 0x00;  /* No modem control */
}

static void serial_putchar(char c)
{
    while (!(UART_LSR & UART_LSR_THRE)) {}
    UART_THR = (uint8_t)c;
}

static void serial_puts(const char *s)
{
    while (*s) {
        if (*s == '\n') serial_putchar('\r');
        serial_putchar(*s++);
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

static void serial_puthex(uint32_t v)
{
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

typedef struct {
    HeapHeader    hdr;
    uint32_t      len;
    uint32_t      cap;
    RuntimeValue *keys;
    RuntimeValue *values;
} RuntimeMap;

/* Forward declarations */
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
        register unsigned long a7 __asm__("a7") = 8;
        register unsigned long a0r __asm__("a0") = 0;
        __asm__ volatile("ecall" : : "r"(a7), "r"(a0r));
        for(;;) __asm__ volatile("wfi");
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

RuntimeValue rt_string_data(RuntimeValue str)
{
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s) return 0;
    return (RuntimeValue)(uintptr_t)s->data;
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

RuntimeValue rt_string_find(RuntimeValue str, RuntimeValue needle)
{
    if (!IS_HEAP(str) || !IS_HEAP(needle)) return ENCODE_INT(-1);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(needle);
    if (!s || !n) return ENCODE_INT(-1);
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

RuntimeValue rt_string_rfind(RuntimeValue str, RuntimeValue needle)
{
    if (!IS_HEAP(str) || !IS_HEAP(needle)) return ENCODE_INT(-1);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(needle);
    if (!s || !n || n->len == 0) return ENCODE_INT(-1);
    if (n->len > s->len) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)(s->len - n->len); i >= 0; i--) {
        int found = 1;
        for (uint32_t j = 0; j < n->len; j++) {
            if (s->data[i + j] != n->data[j]) { found = 0; break; }
        }
        if (found) return ENCODE_INT(i);
    }
    return ENCODE_INT(-1);
}

/* Helper: decode string or NULL */
static RuntimeString *decode_string(RuntimeValue v)
{
    if (!IS_HEAP(v)) return (RuntimeString *)0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(v);
    if (!s || s->hdr.type != HEAP_STRING) return (RuntimeString *)0;
    return s;
}

RuntimeValue rt_string_contains(RuntimeValue str, RuntimeValue needle)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *n = decode_string(needle);
    if (!s || !n) return 0;
    if (n->len == 0) return 1;
    if (n->len > s->len) return 0;
    for (uint32_t i = 0; i <= s->len - n->len; i++) {
        uint32_t j;
        for (j = 0; j < n->len; j++) {
            if (s->data[i + j] != n->data[j]) break;
        }
        if (j == n->len) return 1;
    }
    return 0;
}

RuntimeValue rt_string_starts_with(RuntimeValue str, RuntimeValue prefix)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *p = decode_string(prefix);
    if (!s || !p) return 0;
    if (p->len > s->len) return 0;
    for (uint32_t i = 0; i < p->len; i++) {
        if (s->data[i] != p->data[i]) return 0;
    }
    return 1;
}

RuntimeValue rt_string_ends_with(RuntimeValue str, RuntimeValue suffix)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *x = decode_string(suffix);
    if (!s || !x) return 0;
    if (x->len > s->len) return 0;
    uint32_t off = s->len - x->len;
    for (uint32_t i = 0; i < x->len; i++) {
        if (s->data[off + i] != x->data[i]) return 0;
    }
    return 1;
}

RuntimeValue rt_string_index_of(RuntimeValue str, RuntimeValue needle)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *n = decode_string(needle);
    if (!s || !n || n->len == 0) return ENCODE_INT(-1);
    if (n->len > s->len) return ENCODE_INT(-1);
    for (uint32_t i = 0; i <= s->len - n->len; i++) {
        uint32_t j;
        for (j = 0; j < n->len; j++) {
            if (s->data[i + j] != n->data[j]) break;
        }
        if (j == n->len) return ENCODE_INT((int64_t)i);
    }
    return ENCODE_INT(-1);
}

RuntimeValue rt_string_last_index_of(RuntimeValue str, RuntimeValue needle)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *n = decode_string(needle);
    if (!s || !n || n->len == 0) return ENCODE_INT(-1);
    if (n->len > s->len) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)(s->len - n->len); i >= 0; i--) {
        uint32_t j;
        for (j = 0; j < n->len; j++) {
            if (s->data[i + j] != n->data[j]) break;
        }
        if (j == n->len) return ENCODE_INT(i);
    }
    return ENCODE_INT(-1);
}

RuntimeValue rt_string_substr(RuntimeValue str, RuntimeValue start)
{
    RuntimeString *s = decode_string(str);
    if (!s) return NIL_VALUE;
    int64_t a = DECODE_INT(start);
    if (a < 0) a = 0;
    if ((uint32_t)a >= s->len) return rt_string_from_cstr("");
    return rt_string_slice(str, start, ENCODE_INT(s->len));
}

static int is_whitespace(char c)
{
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

RuntimeValue rt_string_trim(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len == 0) return str;
    uint32_t start = 0;
    while (start < s->len && is_whitespace(s->data[start])) start++;
    uint32_t end = s->len;
    while (end > start && is_whitespace(s->data[end - 1])) end--;
    return rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(end));
}

RuntimeValue rt_string_trim_start(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len == 0) return str;
    uint32_t start = 0;
    while (start < s->len && is_whitespace(s->data[start])) start++;
    return rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(s->len));
}

RuntimeValue rt_string_trim_end(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len == 0) return str;
    uint32_t end = s->len;
    while (end > 0 && is_whitespace(s->data[end - 1])) end--;
    return rt_string_slice(str, ENCODE_INT(0), ENCODE_INT(end));
}

RuntimeValue rt_string_to_upper(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1);
    r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        r->data[i] = (c >= 'a' && c <= 'z') ? (char)(c - 32) : c;
    }
    r->data[s->len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_to_lower(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1);
    r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        r->data[i] = (c >= 'A' && c <= 'Z') ? (char)(c + 32) : c;
    }
    r->data[s->len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_replace(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *o = decode_string(old_val);
    RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str;
    if (o->len > s->len) return str;
    uint32_t nlen = n ? n->len : 0;
    for (uint32_t i = 0; i <= s->len - o->len; i++) {
        uint32_t j;
        for (j = 0; j < o->len; j++) {
            if (s->data[i + j] != o->data[j]) break;
        }
        if (j == o->len) {
            uint32_t result_len = s->len - o->len + nlen;
            RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
            if (!r) return str;
            r->hdr.type = HEAP_STRING;
            r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
            r->len = result_len;
            __builtin_memcpy(r->data, s->data, i);
            if (n && nlen > 0) __builtin_memcpy(r->data + i, n->data, nlen);
            __builtin_memcpy(r->data + i + nlen, s->data + i + o->len, s->len - i - o->len);
            r->data[result_len] = '\0';
            return ENCODE_PTR(r);
        }
    }
    return str;
}

RuntimeValue rt_string_replace_all(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *o = decode_string(old_val);
    RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str;
    uint32_t nlen = n ? n->len : 0;
    uint32_t count = 0;
    for (uint32_t i = 0; i + o->len <= s->len; ) {
        uint32_t j;
        for (j = 0; j < o->len; j++) {
            if (s->data[i + j] != o->data[j]) break;
        }
        if (j == o->len) { count++; i += o->len; }
        else { i++; }
    }
    if (count == 0) return str;
    uint32_t result_len = s->len - count * o->len + count * nlen;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
    r->len = result_len;
    uint32_t out = 0;
    for (uint32_t i = 0; i < s->len; ) {
        if (i + o->len <= s->len) {
            uint32_t j;
            for (j = 0; j < o->len; j++) {
                if (s->data[i + j] != o->data[j]) break;
            }
            if (j == o->len) {
                if (n && nlen > 0) { __builtin_memcpy(r->data + out, n->data, nlen); out += nlen; }
                i += o->len;
                continue;
            }
        }
        r->data[out++] = s->data[i++];
    }
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_repeat(RuntimeValue str, RuntimeValue count_val)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len == 0) return str;
    int64_t count = DECODE_INT(count_val);
    if (count <= 0) return rt_string_from_cstr("");
    if (count == 1) return str;
    if ((uint64_t)count * s->len > 0x100000) count = (int64_t)(0x100000 / s->len);
    uint32_t result_len = s->len * (uint32_t)count;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
    r->len = result_len;
    for (int64_t i = 0; i < count; i++) __builtin_memcpy(r->data + i * s->len, s->data, s->len);
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_pad_start(RuntimeValue str, RuntimeValue width_val)
{
    RuntimeString *s = decode_string(str);
    if (!s) return str;
    int64_t width = DECODE_INT(width_val);
    if (width <= 0 || (uint32_t)width <= s->len) return str;
    uint32_t pad = (uint32_t)width - s->len;
    uint32_t result_len = (uint32_t)width;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
    r->len = result_len;
    __builtin_memset(r->data, ' ', pad);
    __builtin_memcpy(r->data + pad, s->data, s->len);
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_pad_end(RuntimeValue str, RuntimeValue width_val)
{
    RuntimeString *s = decode_string(str);
    if (!s) return str;
    int64_t width = DECODE_INT(width_val);
    if (width <= 0 || (uint32_t)width <= s->len) return str;
    uint32_t pad = (uint32_t)width - s->len;
    uint32_t result_len = (uint32_t)width;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
    r->len = result_len;
    __builtin_memcpy(r->data, s->data, s->len);
    __builtin_memset(r->data + s->len, ' ', pad);
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_reverse(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len <= 1) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1);
    r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) r->data[i] = s->data[s->len - 1 - i];
    r->data[s->len] = '\0';
    return ENCODE_PTR(r);
}

RuntimeValue rt_string_chars(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    RuntimeValue arr = rt_array_new(ENCODE_INT(s ? s->len : 0));
    if (!s) return arr;
    for (uint32_t i = 0; i < s->len; i++) {
        RuntimeValue ch = rt_string_new((RuntimeValue)(uintptr_t)&s->data[i], 1);
        arr = rt_array_push(arr, ch);
    }
    return arr;
}

RuntimeValue rt_string_bytes(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    RuntimeValue arr = rt_array_new(ENCODE_INT(s ? s->len : 0));
    if (!s) return arr;
    for (uint32_t i = 0; i < s->len; i++) {
        arr = rt_array_push(arr, ENCODE_INT((int64_t)(unsigned char)s->data[i]));
    }
    return arr;
}

RuntimeValue rt_string_is_empty(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s) return 1;
    return s->len == 0 ? 1 : 0;
}

RuntimeValue rt_string_compare(RuntimeValue a, RuntimeValue b)
{
    RuntimeString *sa = decode_string(a);
    RuntimeString *sb = decode_string(b);
    if (!sa && !sb) return ENCODE_INT(0);
    if (!sa) return ENCODE_INT(-1);
    if (!sb) return ENCODE_INT(1);
    uint32_t min_len = sa->len < sb->len ? sa->len : sb->len;
    for (uint32_t i = 0; i < min_len; i++) {
        if (sa->data[i] != sb->data[i])
            return ENCODE_INT((int64_t)(unsigned char)sa->data[i] - (int64_t)(unsigned char)sb->data[i]);
    }
    if (sa->len < sb->len) return ENCODE_INT(-1);
    if (sa->len > sb->len) return ENCODE_INT(1);
    return ENCODE_INT(0);
}

RuntimeValue rt_string_split(RuntimeValue str, RuntimeValue delim)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *d = decode_string(delim);
    RuntimeValue arr = rt_array_new(ENCODE_INT(4));
    if (!s || s->len == 0) return arr;
    if (!d || d->len == 0) {
        for (uint32_t i = 0; i < s->len; i++) {
            RuntimeValue ch = rt_string_new((RuntimeValue)(uintptr_t)&s->data[i], 1);
            arr = rt_array_push(arr, ch);
        }
        return arr;
    }
    if (d->len > s->len) {
        return rt_array_push(arr, str);
    }
    uint32_t start = 0;
    for (uint32_t i = 0; i <= s->len - d->len; ) {
        uint32_t j;
        for (j = 0; j < d->len; j++) {
            if (s->data[i + j] != d->data[j]) break;
        }
        if (j == d->len) {
            RuntimeValue part = rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(i));
            arr = rt_array_push(arr, part);
            i += d->len;
            start = i;
        } else {
            i++;
        }
    }
    RuntimeValue rest = rt_string_slice(str, ENCODE_INT(start), ENCODE_INT(s->len));
    arr = rt_array_push(arr, rest);
    return arr;
}

RuntimeValue rt_string_format(RuntimeValue fmt, RuntimeValue val)
{
    RuntimeValue val_str = rt_value_to_string(val);
    if (!IS_HEAP(fmt)) return val_str;
    return rt_string_concat(fmt, val_str);
}

/* Helper: integer to decimal string in buffer */
static int int_to_buf(char *buf, int buf_size, int64_t n)
{
    if (n == 0) { buf[0] = '0'; return 1; }
    int neg = 0;
    uint64_t uv;
    if (n < 0) { neg = 1; uv = (uint64_t)(-n); }
    else { uv = (uint64_t)n; }
    char tmp[21];
    int pos = 0;
    while (uv > 0 && pos < 20) { tmp[pos++] = '0' + (char)(uv % 10); uv /= 10; }
    int out = 0;
    if (neg && out < buf_size) buf[out++] = '-';
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

static int int_to_hex_buf(char *buf, int buf_size, uint64_t v, int uppercase)
{
    const char *digits = uppercase ? "0123456789ABCDEF" : "0123456789abcdef";
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[17]; int pos = 0;
    while (v > 0 && pos < 16) { tmp[pos++] = digits[v & 0xF]; v >>= 4; }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

static int int_to_oct_buf(char *buf, int buf_size, uint64_t v)
{
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[23]; int pos = 0;
    while (v > 0 && pos < 22) { tmp[pos++] = '0' + (char)(v & 7); v >>= 3; }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

static int int_to_bin_buf(char *buf, int buf_size, uint64_t v)
{
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[65]; int pos = 0;
    while (v > 0 && pos < 64) { tmp[pos++] = '0' + (char)(v & 1); v >>= 1; }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

RuntimeValue rt_value_format_string(RuntimeValue val, RuntimeValue fmt_ptr_rv, RuntimeValue fmt_len_rv)
{
    const char *spec = (const char *)(uintptr_t)fmt_ptr_rv;
    int64_t spec_len = fmt_len_rv;
    if (!spec || spec_len <= 0) return rt_value_to_string(val);

    char fill = ' '; char align = '\0'; char sign_mode = '\0';
    int alt_form = 0; int zero_pad = 0; int width = -1; int precision = -1; char type_code = '\0';
    int pos = 0;

    if (spec_len >= 2 && (spec[1] == '<' || spec[1] == '>' || spec[1] == '^' || spec[1] == '='))
        { fill = spec[0]; align = spec[1]; pos = 2; }
    else if (spec_len >= 1 && (spec[0] == '<' || spec[0] == '>' || spec[0] == '^' || spec[0] == '='))
        { align = spec[0]; pos = 1; }

    if (pos < spec_len && (spec[pos] == '+' || spec[pos] == '-' || spec[pos] == ' ')) { sign_mode = spec[pos]; pos++; }
    if (pos < spec_len && spec[pos] == '#') { alt_form = 1; pos++; }
    if (pos < spec_len && spec[pos] == '0') { zero_pad = 1; pos++; }
    if (pos < spec_len && spec[pos] >= '1' && spec[pos] <= '9') {
        width = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') { width = width * 10 + (spec[pos] - '0'); pos++; }
    }
    if (pos < spec_len && spec[pos] == '.') {
        pos++; precision = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') { precision = precision * 10 + (spec[pos] - '0'); pos++; }
    }
    if (pos < spec_len) type_code = spec[pos];

    char raw_buf[128]; int raw_len = 0;
    int64_t int_val = 0;
    if (IS_INT(val)) int_val = DECODE_INT(val);

    switch (type_code) {
    case 'd': {
        int is_neg = (int_val < 0);
        uint64_t abs_v = is_neg ? (uint64_t)(-int_val) : (uint64_t)int_val;
        char digits[21]; int dlen = int_to_buf(digits, 21, (int64_t)abs_v);
        raw_len = 0;
        if (is_neg) raw_buf[raw_len++] = '-';
        else if (sign_mode == '+') raw_buf[raw_len++] = '+';
        else if (sign_mode == ' ') raw_buf[raw_len++] = ' ';
        __builtin_memcpy(raw_buf + raw_len, digits, (size_t)dlen); raw_len += dlen;
        break;
    }
    case 'x': case 'X': {
        raw_len = 0;
        if (alt_form) { raw_buf[raw_len++] = '0'; raw_buf[raw_len++] = (type_code == 'X') ? 'X' : 'x'; }
        raw_len += int_to_hex_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), (uint64_t)int_val, (type_code == 'X'));
        break;
    }
    case 'o': {
        raw_len = 0;
        if (alt_form) { raw_buf[raw_len++] = '0'; raw_buf[raw_len++] = 'o'; }
        raw_len += int_to_oct_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), (uint64_t)int_val);
        break;
    }
    case 'b': {
        raw_len = 0;
        if (alt_form) { raw_buf[raw_len++] = '0'; raw_buf[raw_len++] = 'b'; }
        raw_len += int_to_bin_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), (uint64_t)int_val);
        break;
    }
    case 'f': case 'F': {
        int prec = (precision >= 0) ? precision : 6;
        int is_neg = (int_val < 0);
        int64_t abs_v = is_neg ? -int_val : int_val;
        raw_len = 0;
        if (is_neg) raw_buf[raw_len++] = '-';
        else if (sign_mode == '+') raw_buf[raw_len++] = '+';
        else if (sign_mode == ' ') raw_buf[raw_len++] = ' ';
        raw_len += int_to_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), abs_v);
        if (prec > 0) { raw_buf[raw_len++] = '.'; for (int i = 0; i < prec && raw_len < (int)sizeof(raw_buf) - 1; i++) raw_buf[raw_len++] = '0'; }
        break;
    }
    default: {
        RuntimeValue str_rv = rt_value_to_string(val);
        RuntimeString *str_s = decode_string(str_rv);
        if (str_s) {
            int slen = (int)str_s->len;
            if (precision >= 0 && slen > precision) slen = precision;
            if (slen > (int)sizeof(raw_buf) - 1) slen = (int)sizeof(raw_buf) - 1;
            __builtin_memcpy(raw_buf, str_s->data, (size_t)slen);
            raw_len = slen;
        } else { __builtin_memcpy(raw_buf, "nil", 3); raw_len = 3; }
        break;
    }
    }

    if (width > 0 && raw_len < width) {
        int padding = width - raw_len;
        char fill_char = (zero_pad && align == '\0') ? '0' : fill;
        char eff_align = align;
        if (eff_align == '\0') eff_align = zero_pad ? '>' : '<';
        char result_buf[256]; int result_len = 0;
        switch (eff_align) {
        case '>':
            if (fill_char == '0' && raw_len > 0 && (raw_buf[0] == '+' || raw_buf[0] == '-' || raw_buf[0] == ' ')) {
                result_buf[result_len++] = raw_buf[0];
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 1; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            } else {
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            }
            break;
        case '<':
            for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
            break;
        case '^': {
            int lp = padding / 2, rp = padding - lp;
            for (int i = 0; i < lp && result_len < 255; i++) result_buf[result_len++] = fill_char;
            for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            for (int i = 0; i < rp && result_len < 255; i++) result_buf[result_len++] = fill_char;
            break;
        }
        case '=':
            if (raw_len > 0 && (raw_buf[0] == '+' || raw_buf[0] == '-' || raw_buf[0] == ' ')) {
                result_buf[result_len++] = raw_buf[0];
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 1; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            } else {
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            }
            break;
        }
        return rt_string_new((RuntimeValue)(uintptr_t)result_buf, (RuntimeValue)result_len);
    }
    return rt_string_new((RuntimeValue)(uintptr_t)raw_buf, (RuntimeValue)raw_len);
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

void rt_println_str(RuntimeValue str) { rt_print_str(str); serial_putchar('\r'); serial_putchar('\n'); }

void rt_print_value(RuntimeValue val)
{
    if (val == 0 || IS_NIL(val)) { serial_puts("nil"); }
    else if (IS_INT(val)) { serial_put_dec(DECODE_INT(val)); }
    else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) rt_print_str(val);
        else serial_puts("<object>");
    } else {
        RuntimeString *s = (RuntimeString *)(uintptr_t)val;
        if (s->hdr.type == HEAP_STRING && s->len < 0x100000) rt_print_str(val);
        else serial_put_dec(val);
    }
}

void rt_println_value(RuntimeValue val) { rt_print_value(val); serial_putchar('\r'); serial_putchar('\n'); }

void rt_print_int(RuntimeValue val) { serial_put_dec(DECODE_INT(val)); }
void rt_println_int(RuntimeValue val) { serial_put_dec(DECODE_INT(val)); serial_putchar('\r'); serial_putchar('\n'); }
void rt_print_char(RuntimeValue val) { serial_putchar((char)DECODE_INT(val)); }
void rt_print_hex(RuntimeValue val) { serial_put_hex((uint64_t)DECODE_INT(val)); }
void rt_print_bool(RuntimeValue val) { if (DECODE_INT(val)) serial_puts("true"); else serial_puts("false"); }
void rt_println_bool(RuntimeValue val) { rt_print_bool(val); serial_putchar('\r'); serial_putchar('\n'); }

RuntimeValue rt_print(RuntimeValue val)
{
    if (IS_INT(val)) serial_put_dec(DECODE_INT(val));
    else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]); }
        else serial_puts("<object>");
    } else if (IS_NIL(val)) serial_puts("nil");
    else serial_puts("<value>");
    return NIL_VALUE;
}

RuntimeValue rt_println(RuntimeValue val) { rt_print(val); serial_putchar('\r'); serial_putchar('\n'); return NIL_VALUE; }

/* serial_println — callable from Simple via extern fn serial_println(msg: text) */
RuntimeValue serial_println(RuntimeValue val)
{
    rt_print(val);
    serial_puts("\r\n");
    return NIL_VALUE;
}

RuntimeValue rt_value_to_string(RuntimeValue val)
{
    if (IS_INT(val)) {
        int64_t n = DECODE_INT(val);
        if (n == 0) return rt_string_from_cstr("0");
        if (n == (-9223372036854775807LL - 1)) return rt_string_from_cstr("-9223372036854775808");
        char buf[21]; int pos = 0; int neg = 0; uint64_t uv;
        if (n < 0) { neg = 1; uv = (uint64_t)(-n); } else { uv = (uint64_t)n; }
        while (uv > 0) { buf[pos++] = '0' + (char)(uv % 10); uv /= 10; }
        uint32_t len = (uint32_t)(pos + neg);
        RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + len + 1);
        if (!s) return NIL_VALUE;
        s->hdr.type = HEAP_STRING; s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1); s->len = len;
        int out = 0; if (neg) s->data[out++] = '-';
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

/* ===================================================================
 * 8. Comparison / Arithmetic / Type introspection
 * =================================================================== */

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
            for (uint32_t i = 0; i < sa->len; i++) { if (sa->data[i] != sb->data[i]) return 0; }
            return 1;
        }
    }
    return 0;
}

RuntimeValue rt_native_neq(RuntimeValue a, RuntimeValue b) { return rt_native_eq(a, b) ? 0 : 1; }

RuntimeValue rt_eq(RuntimeValue a, RuntimeValue b) { return rt_native_eq(a, b) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_ne(RuntimeValue a, RuntimeValue b) { return rt_native_eq(a, b) ? FALSE_VALUE : TRUE_VALUE; }
RuntimeValue rt_lt(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) < DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_gt(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) > DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_le(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) <= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_ge(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) >= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_and(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) && DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_or(RuntimeValue a, RuntimeValue b) { return (DECODE_INT(a) || DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE; }
RuntimeValue rt_not(RuntimeValue a) { return DECODE_INT(a) ? FALSE_VALUE : TRUE_VALUE; }

RuntimeValue rt_add(RuntimeValue a, RuntimeValue b)
{
    if (IS_INT(a) && IS_INT(b)) return ENCODE_INT(DECODE_INT(a) + DECODE_INT(b));
    if (IS_HEAP(a) || IS_HEAP(b)) return rt_string_concat(a, b);
    return ENCODE_INT(0);
}
RuntimeValue rt_sub(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) - DECODE_INT(b)); }
RuntimeValue rt_mul(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) * DECODE_INT(b)); }
RuntimeValue rt_div(RuntimeValue a, RuntimeValue b) { int64_t d = DECODE_INT(b); if (d == 0) return ENCODE_INT(0); return ENCODE_INT(DECODE_INT(a) / d); }
RuntimeValue rt_mod(RuntimeValue a, RuntimeValue b) { int64_t d = DECODE_INT(b); if (d == 0) return ENCODE_INT(0); return ENCODE_INT(DECODE_INT(a) % d); }
RuntimeValue rt_pow(RuntimeValue a, RuntimeValue b)
{
    int64_t base = DECODE_INT(a); int64_t exp = DECODE_INT(b);
    if (exp < 0) return ENCODE_INT(0);
    int64_t result = 1; for (int64_t i = 0; i < exp; i++) result *= base;
    return ENCODE_INT(result);
}
RuntimeValue rt_neg(RuntimeValue a) { return ENCODE_INT(-DECODE_INT(a)); }
RuntimeValue rt_shl(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) << DECODE_INT(b)); }
RuntimeValue rt_shr(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) >> DECODE_INT(b)); }
RuntimeValue rt_bitand(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) & DECODE_INT(b)); }
RuntimeValue rt_bitor(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) | DECODE_INT(b)); }
RuntimeValue rt_bitxor(RuntimeValue a, RuntimeValue b) { return ENCODE_INT(DECODE_INT(a) ^ DECODE_INT(b)); }
RuntimeValue rt_bitnot(RuntimeValue a) { return ENCODE_INT(~DECODE_INT(a)); }

RuntimeValue rt_type_of(RuntimeValue val)
{
    if (IS_NIL(val))   return rt_string_from_cstr("nil");
    if (IS_INT(val))   return rt_string_from_cstr("int");
    if (IS_FLOAT(val)) return rt_string_from_cstr("float");
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h) {
            if (h->type == HEAP_STRING) return rt_string_from_cstr("string");
            if (h->type == HEAP_ARRAY)  return rt_string_from_cstr("array");
            if (h->type == HEAP_MAP)    return rt_string_from_cstr("map");
            if (h->type == HEAP_OBJECT) return rt_string_from_cstr("object");
        }
        return rt_string_from_cstr("heap");
    }
    return rt_string_from_cstr("unknown");
}

RuntimeValue rt_is_nil(RuntimeValue val) { return IS_NIL(val) ? 1 : 0; }
RuntimeValue rt_is_int(RuntimeValue val) { return IS_INT(val) ? 1 : 0; }
RuntimeValue rt_is_float(RuntimeValue val) { return IS_FLOAT(val) ? 1 : 0; }
RuntimeValue rt_is_string(RuntimeValue val) { if (!IS_HEAP(val)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(val); return (h && h->type == HEAP_STRING) ? 1 : 0; }
RuntimeValue rt_is_bool(RuntimeValue val) { if (!IS_INT(val)) return 0; int64_t v = DECODE_INT(val); return (v == 0 || v == 1) ? 1 : 0; }
RuntimeValue rt_is_array(RuntimeValue val) { if (!IS_HEAP(val)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(val); return (h && h->type == HEAP_ARRAY) ? 1 : 0; }
RuntimeValue rt_is_map(RuntimeValue val) { if (!IS_HEAP(val)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(val); return (h && h->type == HEAP_MAP) ? 1 : 0; }
RuntimeValue rt_is_object(RuntimeValue val) { if (!IS_HEAP(val)) return 0; HeapHeader *h = (HeapHeader *)DECODE_PTR(val); return (h && h->type == HEAP_OBJECT) ? 1 : 0; }

RuntimeValue rt_to_int(RuntimeValue val)
{
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
            for (; i < s->len; i++) { char c = s->data[i]; if (c < '0' || c > '9') break; result = result * 10 + (c - '0'); }
            if (neg) result = -result;
            return ENCODE_INT(result);
        }
    }
    return ENCODE_INT(0);
}
RuntimeValue rt_to_string(RuntimeValue val) { return rt_value_to_string(val); }
RuntimeValue rt_to_bool(RuntimeValue val)
{
    if (IS_NIL(val)) return FALSE_VALUE;
    if (IS_INT(val)) return DECODE_INT(val) ? TRUE_VALUE : FALSE_VALUE;
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; return s->len > 0 ? TRUE_VALUE : FALSE_VALUE; }
        if (h && h->type == HEAP_ARRAY) { RuntimeArray *a = (RuntimeArray *)h; return a->len > 0 ? TRUE_VALUE : FALSE_VALUE; }
        return TRUE_VALUE;
    }
    return FALSE_VALUE;
}

RuntimeValue rt_clone(RuntimeValue val)
{
    if (!IS_HEAP(val)) return val;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    if (!h) return val;
    if (h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; return rt_string_new((RuntimeValue)(uintptr_t)s->data, (RuntimeValue)s->len); }
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

RuntimeValue rt_value_compare(RuntimeValue a, RuntimeValue b) {
    int64_t va = (int64_t)a, vb = (int64_t)b;
    if (va < vb) return ENCODE_INT(-1);
    if (va > vb) return ENCODE_INT(1);
    return ENCODE_INT(0);
}

/* ===================================================================
 * 9. Array operations
 * =================================================================== */

RuntimeValue rt_array_new(RuntimeValue cap_val)
{
    int64_t cap = (int64_t)cap_val;  /* RAW -- not DECODE_INT */
    if (cap <= 0) cap = 64;
    if (cap < 64) cap = 64;
    if (cap > 0x100000) cap = 0x100000;
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)cap * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY; a->hdr.size = (uint32_t)alloc_size; a->len = 0; a->cap = (uint32_t)cap;
    for (int64_t i = 0; i < cap; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    if (a->len >= a->cap) {
        /* At capacity -- cannot grow (flexible array member can't be resized in-place).
         * Silently drop. Initial capacity should be large enough for the use case. */
        return ENCODE_PTR(a);
    }
    a->items[a->len] = val; a->len++;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_pop(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return NIL_VALUE;
    a->len--; RuntimeValue val = a->items[a->len]; a->items[a->len] = NIL_VALUE; return val;
}

RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    return a->items[i];
}

RuntimeValue rt_array_set(RuntimeValue arr, RuntimeValue idx, RuntimeValue val) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    a->items[i] = val; return val;
}

RuntimeValue rt_array_len(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return ENCODE_INT(0);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(0);
    return ENCODE_INT(a->len);
}

RuntimeValue rt_array_slice(RuntimeValue arr, RuntimeValue start, RuntimeValue end) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t s = DECODE_INT(start), e = DECODE_INT(end);
    if (s < 0) s = 0; if (e > (int64_t)a->len) e = (int64_t)a->len;
    if (s >= e) return rt_array_new(ENCODE_INT(1));
    RuntimeValue result = rt_array_new(ENCODE_INT(e - s));
    for (int64_t i = s; i < e; i++) result = rt_array_push(result, a->items[i]);
    return result;
}

RuntimeValue rt_array_contains(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return 0;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return 0;
    for (uint32_t i = 0; i < a->len; i++) { if (rt_native_eq(a->items[i], val)) return 1; }
    return 0;
}

RuntimeValue rt_array_index_of(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return ENCODE_INT(-1);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (uint32_t i = 0; i < a->len; i++) { if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i); }
    return ENCODE_INT(-1);
}

RuntimeValue rt_array_last_index_of(RuntimeValue arr, RuntimeValue val) {
    if (!IS_HEAP(arr)) return ENCODE_INT(-1);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)a->len - 1; i >= 0; i--) { if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i); }
    return ENCODE_INT(-1);
}

RuntimeValue rt_array_remove(RuntimeValue arr, RuntimeValue idx) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    RuntimeValue removed = a->items[i];
    for (uint32_t j = (uint32_t)i; j + 1 < a->len; j++) a->items[j] = a->items[j + 1];
    a->len--; a->items[a->len] = NIL_VALUE;
    return removed;
}

RuntimeValue rt_array_join(RuntimeValue arr, RuntimeValue sep) {
    if (!IS_HEAP(arr)) return rt_string_from_cstr("");
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return rt_string_from_cstr("");
    RuntimeValue result = rt_value_to_string(a->items[0]);
    for (uint32_t i = 1; i < a->len; i++) {
        if (IS_HEAP(sep)) result = rt_string_concat(result, sep);
        result = rt_string_concat(result, rt_value_to_string(a->items[i]));
    }
    return result;
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
    if (!IS_HEAP(arr)) return arr;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return arr;
    for (uint32_t i = 0; i < a->len; i++) a->items[i] = NIL_VALUE;
    a->len = 0; return arr;
}

RuntimeValue rt_array_clone(RuntimeValue arr) {
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    RuntimeValue result = rt_array_new(ENCODE_INT(a->cap));
    for (uint32_t i = 0; i < a->len; i++) result = rt_array_push(result, a->items[i]);
    return result;
}

RuntimeValue rt_array_first(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_array_last(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_array_repeat(RuntimeValue v, RuntimeValue n) { (void)v; (void)n; return NIL_VALUE; }

/* ===================================================================
 * 9b. Enum / Optional / Result operations
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
 * 10. Map/Dict operations
 * =================================================================== */

static RuntimeMap *decode_map(RuntimeValue v) {
    if (!IS_HEAP(v)) return (RuntimeMap *)0;
    RuntimeMap *m = (RuntimeMap *)DECODE_PTR(v);
    if (!m || m->hdr.type != HEAP_MAP) return (RuntimeMap *)0;
    return m;
}

static int32_t map_find_key(RuntimeMap *m, RuntimeValue key) {
    for (uint32_t i = 0; i < m->len; i++) { if (rt_native_eq(m->keys[i], key)) return (int32_t)i; }
    return -1;
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
    RuntimeMap *m = (RuntimeMap *)malloc(sizeof(RuntimeMap));
    if (!m) return NIL_VALUE;
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
    m->keys[m->len] = key; m->values[m->len] = value; m->len++;
    return map;
}

RuntimeValue rt_map_get(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key); if (idx >= 0) return m->values[idx];
    return NIL_VALUE;
}

RuntimeValue rt_map_has(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return 0;
    return map_find_key(m, key) >= 0 ? 1 : 0;
}

RuntimeValue rt_map_remove(RuntimeValue map, RuntimeValue key) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key); if (idx < 0) return NIL_VALUE;
    RuntimeValue removed = m->values[idx];
    for (uint32_t i = (uint32_t)idx; i + 1 < m->len; i++) { m->keys[i] = m->keys[i + 1]; m->values[i] = m->values[i + 1]; }
    m->len--; m->keys[m->len] = NIL_VALUE; m->values[m->len] = NIL_VALUE;
    return removed;
}

RuntimeValue rt_map_keys(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) arr = rt_array_push(arr, m->keys[i]);
    return arr;
}

RuntimeValue rt_map_values(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) arr = rt_array_push(arr, m->values[i]);
    return arr;
}

RuntimeValue rt_map_entries(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) {
        RuntimeValue pair = rt_array_new(ENCODE_INT(2));
        pair = rt_array_push(pair, m->keys[i]); pair = rt_array_push(pair, m->values[i]);
        arr = rt_array_push(arr, pair);
    }
    return arr;
}

RuntimeValue rt_map_len(RuntimeValue map) { RuntimeMap *m = decode_map(map); if (!m) return ENCODE_INT(0); return ENCODE_INT(m->len); }

RuntimeValue rt_map_clear(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    for (uint32_t i = 0; i < m->len; i++) { m->keys[i] = NIL_VALUE; m->values[i] = NIL_VALUE; }
    m->len = 0; return map;
}

RuntimeValue rt_map_clone(RuntimeValue map) {
    RuntimeMap *m = decode_map(map); if (!m) return NIL_VALUE;
    RuntimeValue new_map = rt_map_new();
    for (uint32_t i = 0; i < m->len; i++) rt_map_set(new_map, m->keys[i], m->values[i]);
    return new_map;
}

RuntimeValue rt_map_merge(RuntimeValue map_a, RuntimeValue map_b) {
    RuntimeValue result = rt_map_clone(map_a);
    RuntimeMap *mb = decode_map(map_b); if (!mb) return result;
    for (uint32_t i = 0; i < mb->len; i++) result = rt_map_set(result, mb->keys[i], mb->values[i]);
    return result;
}

RuntimeValue rt_map_for_each(RuntimeValue map, RuntimeValue callback) { (void)map; (void)callback; return NIL_VALUE; }

/* Dict aliases */
RuntimeValue rt_dict_new(void) { return rt_map_new(); }
RuntimeValue rt_dict_get(RuntimeValue d, RuntimeValue k) { return rt_map_get(d, k); }
RuntimeValue rt_dict_set(RuntimeValue d, RuntimeValue k, RuntimeValue v) { return rt_map_set(d, k, v); }
RuntimeValue rt_dict_len(RuntimeValue d) { return rt_map_len(d); }
RuntimeValue rt_dict_keys(RuntimeValue d) { return rt_map_keys(d); }
RuntimeValue rt_dict_values(RuntimeValue d) { return rt_map_values(d); }
RuntimeValue rt_dict_clear(RuntimeValue d) { return rt_map_clear(d); }

/* ===================================================================
 * 11. Index/Len dispatch
 * =================================================================== */

RuntimeValue rt_len(RuntimeValue v)
{
    if (IS_INT(v)) return ENCODE_INT(0);
    if (!IS_HEAP(v)) return ENCODE_INT(0);
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return ENCODE_INT(0);
    if (h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; return ENCODE_INT(s->len); }
    if (h->type == HEAP_ARRAY) { RuntimeArray *a = (RuntimeArray *)h; return ENCODE_INT(a->len); }
    if (h->type == HEAP_MAP) { RuntimeMap *m = (RuntimeMap *)h; return ENCODE_INT(m->len); }
    return ENCODE_INT(0);
}

RuntimeValue rt_index_get(RuntimeValue v, RuntimeValue idx)
{
    if (!IS_HEAP(v)) return NIL_VALUE;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v); if (!h) return NIL_VALUE;
    if (h->type == HEAP_STRING) return rt_string_char_at(v, idx);
    if (h->type == HEAP_ARRAY) { int64_t i = DECODE_INT(idx); RuntimeArray *a = (RuntimeArray *)h; if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE; return a->items[i]; }
    if (h->type == HEAP_MAP) return rt_map_get(v, idx);
    return NIL_VALUE;
}

RuntimeValue rt_index_set(RuntimeValue v, RuntimeValue idx, RuntimeValue val)
{
    if (!IS_HEAP(v)) return NIL_VALUE;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v); if (!h) return NIL_VALUE;
    if (h->type == HEAP_ARRAY) { int64_t i = DECODE_INT(idx); RuntimeArray *a = (RuntimeArray *)h; if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE; a->items[i] = val; return val; }
    if (h->type == HEAP_MAP) { rt_map_set(v, idx, val); return val; }
    return NIL_VALUE;
}

RuntimeValue rt_value_bool(RuntimeValue value)
{
    if (value == TRUE_VALUE || value == 1) return TRUE_VALUE;
    if (value == FALSE_VALUE || value == 0 || value == NIL_VALUE) return FALSE_VALUE;
    if (IS_INT(value)) return DECODE_INT(value) != 0 ? TRUE_VALUE : FALSE_VALUE;
    return TRUE_VALUE;
}

RuntimeValue ptr(RuntimeValue value)
{
    return value;
}

/* ===================================================================
 * 12. PCI enumeration via ECAM MMIO (QEMU virt: 0x30000000)
 * =================================================================== */

#define ECAM_BASE 0x30000000ULL
#define MAX_PCI_CACHED 32

static struct {
    uint8_t bus, dev, func, class_code, subclass, progif, htype, irq;
    uint16_t vendor, device;
    uint32_t bar0;
} _pci_cache[MAX_PCI_CACHED];
static int _pci_cache_count = 0;

static void _pci_scan(void)
{
    _pci_cache_count = 0;
    for (int dev = 0; dev < 32 && _pci_cache_count < MAX_PCI_CACHED; dev++) {
        volatile uint32_t *cfg = (volatile uint32_t *)(ECAM_BASE + ((uint64_t)dev << 15));
        uint32_t reg0 = cfg[0];
        uint16_t vendor = (uint16_t)(reg0 & 0xFFFF);
        uint16_t devid = (uint16_t)(reg0 >> 16);
        if (vendor == 0xFFFF || vendor == 0) continue;
        uint32_t class_reg = cfg[2];
        uint32_t bar0_reg = cfg[4];
        uint32_t irq_reg = cfg[15]; /* offset 0x3C */
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

static int64_t _pci_enumerate(uint64_t mode, uint64_t index, uint64_t buf_addr)
{
    if (_pci_cache_count == 0) _pci_scan();
    if (mode == 0) return (int64_t)_pci_cache_count;
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
        return (int64_t)_pci_cache[(int)index].bar0;
    }
    return -38;
}

int64_t rt_pci_device_count(void)
{
    if (_pci_cache_count == 0) _pci_scan();
    return (int64_t)_pci_cache_count;
}

int64_t rt_pci_get_field(int64_t index, int64_t field)
{
    if (_pci_cache_count == 0) _pci_scan();
    if (index < 0 || index >= _pci_cache_count) return -22;
    int i = (int)index;
    switch (field) {
        case 0: return (int64_t)_pci_cache[i].bus;
        case 1: return (int64_t)_pci_cache[i].dev;
        case 2: return (int64_t)_pci_cache[i].func;
        case 3: return (int64_t)_pci_cache[i].class_code;
        case 4: return (int64_t)_pci_cache[i].subclass;
        case 5: return (int64_t)_pci_cache[i].vendor;
        case 6: return (int64_t)_pci_cache[i].device;
        case 7: return (int64_t)_pci_cache[i].bar0;
        case 8: return (int64_t)_pci_cache[i].irq;
        default: return -22;
    }
}

/* ===================================================================
 * 12b. QEMU virt poweroff + minimal modern VirtIO device tests
 * =================================================================== */

#define QEMU_TEST_BASE 0x100000ULL
#define QEMU_TEST_PASS 0x5555U
#define QEMU_TEST_FAIL 0x3333U

__attribute__((noreturn))
static void qemu_poweroff(int32_t code)
{
    register unsigned long a7 __asm__("a7") = 8;
    register unsigned long a0r __asm__("a0") = 0;
    __asm__ volatile("ecall" : : "r"(a7), "r"(a0r));
    uint32_t value = (code == 0) ? QEMU_TEST_PASS : (QEMU_TEST_FAIL | ((uint32_t)(code & 0xffff) << 16));
    *(volatile uint32_t *)(uintptr_t)QEMU_TEST_BASE = value;
    for (;;) __asm__ volatile("wfi");
}

static void *dma_alloc_aligned(size_t size, size_t align)
{
    uintptr_t raw = (uintptr_t)_heap_alloc(size + align + 64);
    uintptr_t aligned = (raw + align - 1) & ~(uintptr_t)(align - 1);
    __builtin_memset((void *)aligned, 0, size);
    return (void *)aligned;
}

static inline uint8_t pci_cfg_read8(int cache_idx, uint32_t off)
{
    uint64_t dev = _pci_cache[cache_idx].dev;
    return *(volatile uint8_t *)(uintptr_t)(ECAM_BASE + (dev << 15) + off);
}

static inline uint16_t pci_cfg_read16(int cache_idx, uint32_t off)
{
    uint64_t dev = _pci_cache[cache_idx].dev;
    return *(volatile uint16_t *)(uintptr_t)(ECAM_BASE + (dev << 15) + off);
}

static inline uint32_t pci_cfg_read32(int cache_idx, uint32_t off)
{
    uint64_t dev = _pci_cache[cache_idx].dev;
    return *(volatile uint32_t *)(uintptr_t)(ECAM_BASE + (dev << 15) + off);
}

static inline void pci_cfg_write16(int cache_idx, uint32_t off, uint16_t value)
{
    uint64_t dev = _pci_cache[cache_idx].dev;
    *(volatile uint16_t *)(uintptr_t)(ECAM_BASE + (dev << 15) + off) = value;
}

static inline void pci_cfg_write32(int cache_idx, uint32_t off, uint32_t value)
{
    uint64_t dev = _pci_cache[cache_idx].dev;
    *(volatile uint32_t *)(uintptr_t)(ECAM_BASE + (dev << 15) + off) = value;
}

static uint32_t _pci_mmio_next = 0x40000000U;

static uint64_t pci_bar_addr(int cache_idx, uint8_t bar)
{
    if (bar >= 6) return 0;
    uint32_t low = pci_cfg_read32(cache_idx, 0x10 + (uint32_t)bar * 4);
    if (low == 0 || low == 0xffffffffU) return 0;
    if (low & 1U) return (uint64_t)(low & 0xfffffffcU);
    if ((low & 0xfffffff0U) == 0) {
        uint32_t flags = low & 0x0fU;
        uint32_t assigned = _pci_mmio_next;
        _pci_mmio_next += 0x00010000U;
        pci_cfg_write32(cache_idx, 0x10 + (uint32_t)bar * 4, assigned | flags);
        if ((flags & 0x6U) == 0x4U && bar < 5) {
            pci_cfg_write32(cache_idx, 0x10 + ((uint32_t)bar + 1) * 4, 0);
        }
        low = pci_cfg_read32(cache_idx, 0x10 + (uint32_t)bar * 4);
    }
    if ((low & 0x6U) == 0x4U && bar < 5) {
        uint32_t high = pci_cfg_read32(cache_idx, 0x10 + ((uint32_t)bar + 1) * 4);
        return ((uint64_t)high << 32) | (uint64_t)(low & 0xfffffff0U);
    }
    return (uint64_t)(low & 0xfffffff0U);
}

typedef struct {
    uint64_t common;
    uint64_t notify;
    uint64_t isr;
    uint32_t notify_mult;
} VirtioCaps;

typedef struct {
    uint64_t addr;
    uint32_t len;
    uint16_t flags;
    uint16_t next;
} VirtqDesc;

typedef struct {
    uint16_t qsize;
    uint16_t notify_off;
    uint16_t last_used;
    uint16_t avail_idx;
    VirtqDesc *desc;
    uint16_t *avail;
    uint16_t *used;
} Virtq;

static inline uint8_t mmio8(uint64_t addr) { return *(volatile uint8_t *)(uintptr_t)addr; }
static inline uint16_t mmio16(uint64_t addr) { return *(volatile uint16_t *)(uintptr_t)addr; }
static inline uint32_t mmio32(uint64_t addr) { return *(volatile uint32_t *)(uintptr_t)addr; }
static inline void mmio_w8(uint64_t addr, uint8_t v) { *(volatile uint8_t *)(uintptr_t)addr = v; }
static inline void mmio_w16(uint64_t addr, uint16_t v) { *(volatile uint16_t *)(uintptr_t)addr = v; }
static inline void mmio_w32(uint64_t addr, uint32_t v) { *(volatile uint32_t *)(uintptr_t)addr = v; }
static inline void mmio_w64(uint64_t addr, uint64_t v) { *(volatile uint64_t *)(uintptr_t)addr = v; }

static int virtio_find_caps(int cache_idx, VirtioCaps *caps)
{
    __builtin_memset(caps, 0, sizeof(*caps));
    uint8_t cap = pci_cfg_read8(cache_idx, 0x34);
    for (int guard = 0; cap >= 0x40 && cap != 0xff && guard < 32; guard++) {
        uint8_t cap_id = pci_cfg_read8(cache_idx, cap);
        uint8_t next = pci_cfg_read8(cache_idx, cap + 1);
        if (cap_id == 0x09) {
            uint8_t cfg_type = pci_cfg_read8(cache_idx, cap + 3);
            uint8_t bar = pci_cfg_read8(cache_idx, cap + 4);
            uint32_t offset = pci_cfg_read32(cache_idx, cap + 8);
            uint32_t length = pci_cfg_read32(cache_idx, cap + 12);
            uint64_t base = pci_bar_addr(cache_idx, bar);
            if (base && length) {
                if (cfg_type == 1) caps->common = base + offset;
                else if (cfg_type == 2) {
                    caps->notify = base + offset;
                    caps->notify_mult = pci_cfg_read32(cache_idx, cap + 16);
                } else if (cfg_type == 3) caps->isr = base + offset;
            }
        }
        if (next == 0 || next == cap) break;
        cap = next;
    }
    return caps->common != 0 && caps->notify != 0;
}

static int virtio_modern_begin(int cache_idx, VirtioCaps *caps)
{
    if (!virtio_find_caps(cache_idx, caps)) return -19;
    uint16_t cmd = pci_cfg_read16(cache_idx, 0x04);
    pci_cfg_write16(cache_idx, 0x04, (uint16_t)(cmd | 0x0006));
    mmio_w8(caps->common + 0x14, 0);
    mmio_w8(caps->common + 0x14, 1);
    mmio_w8(caps->common + 0x14, 3);
    mmio_w32(caps->common + 0x08, 0);
    mmio_w32(caps->common + 0x0c, 0);
    mmio_w32(caps->common + 0x08, 1);
    mmio_w32(caps->common + 0x0c, 1);
    mmio_w8(caps->common + 0x14, 11);
    if ((mmio8(caps->common + 0x14) & 8) == 0) return -5;
    return 0;
}

static int virtio_setup_queue(VirtioCaps *caps, uint16_t queue, Virtq *vq, uint16_t wanted)
{
    mmio_w16(caps->common + 0x16, queue);
    uint16_t max = mmio16(caps->common + 0x18);
    if (max < 2) return -19;
    uint16_t qsize = wanted;
    if (qsize > max) qsize = max;
    if (qsize < 2) qsize = 2;
    __builtin_memset(vq, 0, sizeof(*vq));
    vq->qsize = qsize;
    vq->desc = (VirtqDesc *)dma_alloc_aligned((size_t)qsize * sizeof(VirtqDesc), 4096);
    vq->avail = (uint16_t *)dma_alloc_aligned(6 + (size_t)qsize * 2, 4096);
    vq->used = (uint16_t *)dma_alloc_aligned(6 + (size_t)qsize * 8, 4096);
    if (!vq->desc || !vq->avail || !vq->used) return -12;
    mmio_w16(caps->common + 0x18, qsize);
    vq->notify_off = mmio16(caps->common + 0x1e);
    mmio_w64(caps->common + 0x20, (uint64_t)(uintptr_t)vq->desc);
    mmio_w64(caps->common + 0x28, (uint64_t)(uintptr_t)vq->avail);
    mmio_w64(caps->common + 0x30, (uint64_t)(uintptr_t)vq->used);
    mmio_w16(caps->common + 0x1c, 1);
    return 0;
}

static int virtio_wait_used(Virtq *vq, uint32_t spins)
{
    while (spins-- > 0) {
        __sync_synchronize();
        if (vq->used[1] != vq->last_used) {
            vq->last_used = vq->used[1];
            return 0;
        }
    }
    return -110;
}

static void virtio_notify(VirtioCaps *caps, Virtq *vq, uint16_t queue)
{
    uint64_t addr = caps->notify + ((uint64_t)vq->notify_off * (uint64_t)caps->notify_mult);
    __sync_synchronize();
    mmio_w16(addr, queue);
}

static int _net_ready = 0;
static int64_t _net_tx_count = 0;
static VirtioCaps _net_caps;
static Virtq _net_txq;

int64_t rt_net_init(void)
{
    if (_pci_cache_count == 0) _pci_scan();
    for (int i = 0; i < _pci_cache_count; i++) {
        if (_pci_cache[i].class_code == 0x02 && _pci_cache[i].subclass == 0x00 && _pci_cache[i].vendor == 0x1af4) {
            int rc = virtio_modern_begin(i, &_net_caps);
            if (rc < 0) return rc;
            rc = virtio_setup_queue(&_net_caps, 1, &_net_txq, 8);
            if (rc < 0) return rc;
            mmio_w8(_net_caps.common + 0x14, 15);
            _net_ready = 1;
            return 0;
        }
    }
    _net_ready = 0;
    return -19; /* ENODEV */
}

int64_t rt_net_tx_test(void)
{
    if (!_net_ready) {
        int64_t rc = rt_net_init();
        if (rc < 0) return rc;
    }
    uint8_t *hdr = (uint8_t *)dma_alloc_aligned(64, 64);
    uint8_t *frame = (uint8_t *)dma_alloc_aligned(128, 64);
    if (!hdr || !frame) return -12;
    __builtin_memset(hdr, 0, 64);
    __builtin_memset(frame, 0, 128);
    for (int i = 0; i < 6; i++) frame[i] = 0xff;
    frame[6] = 0x52; frame[7] = 0x54; frame[8] = 0x00; frame[9] = 0x12; frame[10] = 0x34; frame[11] = 0x56;
    frame[12] = 0x88; frame[13] = 0xb5;
    for (int i = 14; i < 60; i++) frame[i] = (uint8_t)i;
    _net_txq.desc[0].addr = (uint64_t)(uintptr_t)hdr;
    _net_txq.desc[0].len = 10;
    _net_txq.desc[0].flags = 1;
    _net_txq.desc[0].next = 1;
    _net_txq.desc[1].addr = (uint64_t)(uintptr_t)frame;
    _net_txq.desc[1].len = 60;
    _net_txq.desc[1].flags = 0;
    _net_txq.desc[1].next = 0;
    uint16_t slot = (uint16_t)(2 + (_net_txq.avail_idx % _net_txq.qsize));
    _net_txq.avail[slot] = 0;
    _net_txq.avail_idx++;
    _net_txq.avail[1] = _net_txq.avail_idx;
    virtio_notify(&_net_caps, &_net_txq, 1);
    int rc = virtio_wait_used(&_net_txq, 10000000);
    if (rc < 0) return rc;
    _net_tx_count++;
    return 0;
}

int64_t rt_net_stats(void)
{
    return _net_ready ? _net_tx_count : -19;
}

static int _gpu_ready = 0;
static int _gpu_flushed = 0;
static int64_t _gpu_width = 0;
static int64_t _gpu_height = 0;
static VirtioCaps _gpu_caps;
static Virtq _gpu_q;
static uint8_t *_gpu_cmd = 0;
static uint8_t *_gpu_resp = 0;
static uint32_t *_gpu_fb = 0;

static void gpu_hdr(uint32_t type)
{
    __builtin_memset(_gpu_cmd, 0, 4096);
    __builtin_memset(_gpu_resp, 0, 4096);
    *(uint32_t *)(_gpu_cmd + 0) = type;
}

static uint32_t gpu_cmd(uint32_t req_len, uint32_t resp_len)
{
    _gpu_q.desc[0].addr = (uint64_t)(uintptr_t)_gpu_cmd;
    _gpu_q.desc[0].len = req_len;
    _gpu_q.desc[0].flags = 1;
    _gpu_q.desc[0].next = 1;
    _gpu_q.desc[1].addr = (uint64_t)(uintptr_t)_gpu_resp;
    _gpu_q.desc[1].len = resp_len;
    _gpu_q.desc[1].flags = 2;
    _gpu_q.desc[1].next = 0;
    uint16_t slot = (uint16_t)(2 + (_gpu_q.avail_idx % _gpu_q.qsize));
    _gpu_q.avail[slot] = 0;
    _gpu_q.avail_idx++;
    _gpu_q.avail[1] = _gpu_q.avail_idx;
    virtio_notify(&_gpu_caps, &_gpu_q, 0);
    if (virtio_wait_used(&_gpu_q, 10000000) < 0) return 0;
    return *(uint32_t *)_gpu_resp;
}

int64_t rt_display_init(void)
{
    if (_gpu_ready) return 0;
    if (_pci_cache_count == 0) _pci_scan();
    for (int i = 0; i < _pci_cache_count; i++) {
        if (_pci_cache[i].vendor != 0x1af4) continue;
        if (!(_pci_cache[i].class_code == 0x03 || _pci_cache[i].device == 0x1050)) continue;
        int rc = virtio_modern_begin(i, &_gpu_caps);
        if (rc < 0) return rc;
        rc = virtio_setup_queue(&_gpu_caps, 0, &_gpu_q, 8);
        if (rc < 0) return rc;
        mmio_w8(_gpu_caps.common + 0x14, 15);
        _gpu_cmd = (uint8_t *)dma_alloc_aligned(4096, 4096);
        _gpu_resp = (uint8_t *)dma_alloc_aligned(4096, 4096);
        if (!_gpu_cmd || !_gpu_resp) return -12;
        gpu_hdr(0x0100);
        if (gpu_cmd(24, 408) != 0x1101) return -5;
        _gpu_width = 320;
        _gpu_height = 240;
        gpu_hdr(0x0101);
        *(uint32_t *)(_gpu_cmd + 24) = 1;
        *(uint32_t *)(_gpu_cmd + 28) = 1;
        *(uint32_t *)(_gpu_cmd + 32) = (uint32_t)_gpu_width;
        *(uint32_t *)(_gpu_cmd + 36) = (uint32_t)_gpu_height;
        if (gpu_cmd(40, 24) != 0x1100) return -5;
        _gpu_fb = (uint32_t *)dma_alloc_aligned((size_t)(_gpu_width * _gpu_height * 4), 4096);
        if (!_gpu_fb) return -12;
        gpu_hdr(0x0106);
        *(uint32_t *)(_gpu_cmd + 24) = 1;
        *(uint32_t *)(_gpu_cmd + 28) = 1;
        *(uint64_t *)(_gpu_cmd + 32) = (uint64_t)(uintptr_t)_gpu_fb;
        *(uint32_t *)(_gpu_cmd + 40) = (uint32_t)(_gpu_width * _gpu_height * 4);
        if (gpu_cmd(48, 24) != 0x1100) return -5;
        gpu_hdr(0x0103);
        *(uint32_t *)(_gpu_cmd + 32) = (uint32_t)_gpu_width;
        *(uint32_t *)(_gpu_cmd + 36) = (uint32_t)_gpu_height;
        *(uint32_t *)(_gpu_cmd + 40) = 0;
        *(uint32_t *)(_gpu_cmd + 44) = 1;
        if (gpu_cmd(48, 24) != 0x1100) return -5;
        _gpu_ready = 1;
        return 0;
    }
    return -19;
}

int64_t rt_display_flush_test(void)
{
    if (!_gpu_ready) {
        int64_t rc = rt_display_init();
        if (rc < 0) return rc;
    }
    for (uint32_t y = 0; y < (uint32_t)_gpu_height; y++) {
        for (uint32_t x = 0; x < (uint32_t)_gpu_width; x++) {
            uint32_t band = (x * 4) / (uint32_t)_gpu_width;
            uint32_t c = band == 0 ? 0xffff0000U : (band == 1 ? 0xff00ff00U : (band == 2 ? 0xff0000ffU : 0xffffffffU));
            _gpu_fb[y * (uint32_t)_gpu_width + x] = c;
        }
    }
    gpu_hdr(0x0105);
    *(uint32_t *)(_gpu_cmd + 32) = (uint32_t)_gpu_width;
    *(uint32_t *)(_gpu_cmd + 36) = (uint32_t)_gpu_height;
    *(uint64_t *)(_gpu_cmd + 40) = 0;
    *(uint32_t *)(_gpu_cmd + 48) = 1;
    if (gpu_cmd(56, 24) != 0x1100) return -5;
    gpu_hdr(0x0104);
    *(uint32_t *)(_gpu_cmd + 32) = (uint32_t)_gpu_width;
    *(uint32_t *)(_gpu_cmd + 36) = (uint32_t)_gpu_height;
    *(uint32_t *)(_gpu_cmd + 40) = 1;
    if (gpu_cmd(48, 24) != 0x1100) return -5;
    _gpu_flushed = 1;
    serial_puts("[display-riscv] Display capture ready\r\n");
    for (volatile uint32_t delay = 0; delay < 300000000U; delay++) {
        __asm__ volatile("" ::: "memory");
    }
    return 0;
}

int64_t rt_display_width(void) { return _gpu_width; }
int64_t rt_display_height(void) { return _gpu_height; }

/* ===================================================================
 * 13. Syscall dispatcher
 * =================================================================== */

int64_t userlib__syscall_raw__syscall(uint64_t id, uint64_t a0, uint64_t a1,
                                       uint64_t a2, uint64_t a3, uint64_t a4)
{
    (void)a3; (void)a4;
    switch (id) {
        case 0:
            qemu_poweroff((int32_t)a0);
            return 0;
        case 4: return 1; /* GetPid */
        case 60: serial_putchar((char)(a0 & 0xFF)); return 0; /* DebugWrite */
        case 80: return _pci_enumerate(a0, a1, a2); /* DevEnumerate */
        case 82: return _pci_enumerate(5, a0, 0); /* DeviceGrant */
        case 83: return (int64_t)a0; /* MapBar — identity mapped */
        case 84: { void *p = _heap_alloc(a0 > 0 ? a0 : 4096); return ENCODE_INT((int64_t)(uintptr_t)p); }
        case 90: return rt_net_init(); /* VirtioNetInit */
        case 91: return rt_net_tx_test(); /* VirtioNetTxTest */
        case 92: return rt_display_init(); /* VirtioGpuInit */
        case 93: return rt_net_stats(); /* NetStats */
        case 94: return rt_display_flush_test(); /* VirtioGpuFlushTest */
        default: return -38; /* ENOSYS */
    }
}

int64_t syscall(uint64_t id, uint64_t a0, uint64_t a1,
                uint64_t a2, uint64_t a3, uint64_t a4)
{
    return userlib__syscall_raw__syscall(id, a0, a1, a2, a3, a4);
}

int64_t rt_x86_syscall(uint64_t id, uint64_t a0, uint64_t a1,
                       uint64_t a2, uint64_t a3, uint64_t a4)
{
    return userlib__syscall_raw__syscall(id, a0, a1, a2, a3, a4);
}

/* ===================================================================
 * 14. MMIO (real) / Port I/O (no-op stubs) / CPU control
 * =================================================================== */

/* MMIO: real implementations for RISC-V */
RuntimeValue rt_mmio_read_u8(RuntimeValue addr)  { return (RuntimeValue)(uint64_t)*(volatile uint8_t  *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_read_u16(RuntimeValue addr) { return (RuntimeValue)(uint64_t)*(volatile uint16_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_read_u32(RuntimeValue addr) { return (RuntimeValue)(uint64_t)*(volatile uint32_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_read_u64(RuntimeValue addr) { return (RuntimeValue)*(volatile uint64_t *)(uintptr_t)(uint64_t)addr; }
RuntimeValue rt_mmio_write_u8(RuntimeValue addr, RuntimeValue val)  { *(volatile uint8_t  *)(uintptr_t)(uint64_t)addr = (uint8_t)(uint64_t)val; return 0; }
RuntimeValue rt_mmio_write_u16(RuntimeValue addr, RuntimeValue val) { *(volatile uint16_t *)(uintptr_t)(uint64_t)addr = (uint16_t)(uint64_t)val; return 0; }
RuntimeValue rt_mmio_write_u32(RuntimeValue addr, RuntimeValue val) { *(volatile uint32_t *)(uintptr_t)(uint64_t)addr = (uint32_t)(uint64_t)val; return 0; }
RuntimeValue rt_mmio_write_u64(RuntimeValue addr, RuntimeValue val) { *(volatile uint64_t *)(uintptr_t)(uint64_t)addr = (uint64_t)val; return 0; }

/* Port I/O: RISC-V has none — provide no-op stubs */
RuntimeValue rt_port_outb(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_outw(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_outl(RuntimeValue p, RuntimeValue v) { (void)p; (void)v; return NIL_VALUE; }
RuntimeValue rt_port_inb(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_inw(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_inl(RuntimeValue p) { (void)p; return ENCODE_INT(0); }
RuntimeValue rt_port_io_wait(void) { return NIL_VALUE; }

/* CPU control */
RuntimeValue rt_hlt(void)  { __asm__ volatile("wfi"); return NIL_VALUE; }
RuntimeValue rt_sti(void)  { return NIL_VALUE; /* S-mode: csrsi sstatus, 0x2 not safe here */ }
RuntimeValue rt_cli(void)  { return NIL_VALUE; }
RuntimeValue rt_enable_interrupts(void) { return NIL_VALUE; }
RuntimeValue rt_disable_interrupts(void) { return NIL_VALUE; }
RuntimeValue rt_invlpg(RuntimeValue a) { (void)a; __asm__ volatile("sfence.vma" ::: "memory"); return NIL_VALUE; }
RuntimeValue rt_rdtsc(void) { uint64_t t; __asm__ volatile("rdtime %0" : "=r"(t)); return ENCODE_INT((int64_t)t); }
RuntimeValue rt_lgdt(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_lidt(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_ltr(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_read_cr3(RuntimeValue a) { (void)a; uint64_t satp; __asm__ volatile("csrr %0, satp" : "=r"(satp)); return ENCODE_INT((int64_t)satp); }
RuntimeValue rt_write_cr3(RuntimeValue a) { __asm__ volatile("csrw satp, %0" : : "r"((uint64_t)DECODE_INT(a)) : "memory"); __asm__ volatile("sfence.vma" ::: "memory"); return NIL_VALUE; }
RuntimeValue rt_read_cr2(RuntimeValue a) { (void)a; uint64_t stval; __asm__ volatile("csrr %0, stval" : "=r"(stval)); return ENCODE_INT((int64_t)stval); }

/* Framebuffer helpers (no-ops on headless RISC-V) */
void rt_framebuffer_copy(RuntimeValue dst, RuntimeValue src, RuntimeValue count) { (void)dst; (void)src; (void)count; }
void rt_framebuffer_write(RuntimeValue addr, RuntimeValue offset, RuntimeValue val) { (void)addr; (void)offset; (void)val; }
RuntimeValue rt_gui_set_fb(RuntimeValue a, RuntimeValue w) { (void)a; (void)w; return 0; }
RuntimeValue rt_gui_hline(RuntimeValue y, RuntimeValue x, RuntimeValue c, RuntimeValue col) { (void)y; (void)x; (void)c; (void)col; return 0; }
RuntimeValue rt_gui_fill4(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { (void)a; (void)b; (void)c; (void)d; return 0; }
RuntimeValue rt_gui_render_desktop(RuntimeValue a, RuntimeValue b) { (void)a; (void)b; return 0; }
void rt_fb_fill_rect(int64_t fb_addr, int64_t pitch, int64_t x, int64_t y, int64_t w, int64_t h, int64_t color) {
    (void)fb_addr; (void)pitch; (void)x; (void)y; (void)w; (void)h; (void)color;
}

/* ===================================================================
 * 15. _start entry point
 *
 * Note: crt0.S provides the real _start that sets up stack, zeroes BSS,
 * and calls spl_start. The C _start below is NOT used when crt0.S is
 * linked — spl_start is the entry from crt0.S.
 *
 * However, the compiler-generated code calls _start in os_entry.spl
 * which becomes spl_start after mangling. The C _start here is kept
 * as a fallback if crt0.S is not linked.
 * =================================================================== */

/* c_pcimgr_init — extern C wrapper for PCI scan, called from vfs_init.spl */
void c_pcimgr_init(void)
{
    _pci_scan();
}

/* _boot_init: called from crt0.S before spl_start() */
void _boot_init(void)
{
    /* Direct UART write - no function calls needed */
    volatile uint8_t *uart = (volatile uint8_t *)0x10000000UL;

    /* Wait for TX ready then write 'B' */
    while (!(uart[5] & 0x20)) {}
    uart[0] = 'B';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '1';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '\r';
    while (!(uart[5] & 0x20)) {}
    uart[0] = '\n';

    _uart_init();

    serial_puts("SimpleOS RISC-V64 boot\r\n");
    serial_puts("[BOOT] 16550 UART initialized at 0x10000000\r\n");
    serial_puts("[BOOT] Heap: 64 MB bump allocator\r\n");
    serial_puts("[BOOT] RuntimeValue: tagged 64-bit\r\n");

    _pci_scan();
    serial_puts("[BOOT] PCI: ");
    serial_put_dec(_pci_cache_count);
    serial_puts(" devices found\r\n");

    serial_puts("[BOOT] Calling spl_start()...\r\n");
}

extern void spl_start(void) __attribute__((weak));

/* Provide _start only if crt0.S is not linked (weak to avoid conflict) */
void _c_start(void) __attribute__((weak));
void _c_start(void)
{
    _uart_init();
    serial_puts("SimpleOS RISC-V64 boot\r\n");
    serial_puts("[BOOT] 16550 UART initialized at 0x10000000\r\n");
    serial_puts("[BOOT] Heap: 64 MB bump allocator\r\n");
    serial_puts("[BOOT] RuntimeValue: tagged 64-bit\r\n");

    _pci_scan();
    serial_puts("[BOOT] PCI: ");
    serial_put_dec(_pci_cache_count);
    serial_puts(" devices found\r\n");

    serial_puts("[BOOT] Calling spl_start()...\r\n");
    if (spl_start) {
        spl_start();
    } else {
        serial_puts("[BOOT] No spl_start() found\r\n");
    }
    serial_puts("[BOOT] spl_start() returned\r\n");
    serial_puts("[BOOT] RISC-V64 boot complete\r\n");

    /* SBI shutdown */
    register unsigned long a7 __asm__("a7") = 8;
    register unsigned long a0r __asm__("a0") = 0;
    __asm__ volatile("ecall" : : "r"(a7), "r"(a0r));
    for(;;) __asm__ volatile("wfi");
}

/* ===================================================================
 * 16. Fatal-panic stubs
 * =================================================================== */

#define S0(n) RuntimeValue n(void) { \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}
#define S1(n) RuntimeValue n(RuntimeValue a) { \
    (void)a; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}
#define S2(n) RuntimeValue n(RuntimeValue a, RuntimeValue b) { \
    (void)a; (void)b; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}
#define S3(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c) { \
    (void)a; (void)b; (void)c; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}
#define S4(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { \
    (void)a; (void)b; (void)c; (void)d; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}
#define S5(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d, RuntimeValue e) { \
    (void)a; (void)b; (void)c; (void)d; (void)e; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
    return 0; \
}

#define V0(n) void n(void) { \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
}
#define V1(n) void n(RuntimeValue a) { \
    (void)a; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
}
#define V2(n) void n(RuntimeValue a, RuntimeValue b) { \
    (void)a; (void)b; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("wfi"); \
}

#define TRAP_STUB_RET(n, nargs) \
    RuntimeValue n(TRAP_ARGS_##nargs) { \
        TRAP_SUPPRESS_##nargs \
        serial_puts("[TRAP] " #n " called on baremetal -- halting\r\n"); \
        for (;;) { __asm__ volatile("wfi"); } \
        return 0; \
    }
#define TRAP_STUB_VOID(n, nargs) \
    void n(TRAP_ARGS_##nargs) { \
        TRAP_SUPPRESS_##nargs \
        serial_puts("[TRAP] " #n " called on baremetal -- halting\r\n"); \
        for (;;) { __asm__ volatile("wfi"); } \
    }
#define TRAP_ARGS_0   void
#define TRAP_ARGS_1   RuntimeValue _a
#define TRAP_ARGS_2   RuntimeValue _a, RuntimeValue _b
#define TRAP_ARGS_3   RuntimeValue _a, RuntimeValue _b, RuntimeValue _c
#define TRAP_SUPPRESS_0
#define TRAP_SUPPRESS_1  (void)_a;
#define TRAP_SUPPRESS_2  (void)_a; (void)_b;
#define TRAP_SUPPRESS_3  (void)_a; (void)_b; (void)_c;

/* ===================================================================
 * 17. All stubs (matching x86_64 complete list)
 * =================================================================== */

/* --- File I/O --- */
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

TRAP_STUB_RET(rt_file_read, 1)
TRAP_STUB_RET(rt_file_write, 2)
TRAP_STUB_RET(rt_file_exists, 1)
TRAP_STUB_RET(rt_file_delete, 1)
TRAP_STUB_RET(rt_file_append, 2)
TRAP_STUB_RET(rt_file_size, 1)
TRAP_STUB_RET(rt_file_copy, 2)
TRAP_STUB_RET(rt_file_move, 2)
TRAP_STUB_RET(rt_file_rename, 2)
TRAP_STUB_RET(rt_file_is_dir, 1)
TRAP_STUB_RET(rt_file_is_file, 1)
TRAP_STUB_RET(rt_file_read_bytes, 1)
TRAP_STUB_RET(rt_file_write_bytes, 2)
TRAP_STUB_RET(rt_file_stat, 1)
TRAP_STUB_RET(rt_file_realpath, 1)

/* --- Directory I/O --- */
TRAP_STUB_RET(rt_dir_list, 1)
TRAP_STUB_RET(rt_dir_create, 1)
TRAP_STUB_RET(rt_dir_create_all, 1)
TRAP_STUB_RET(rt_dir_exists, 1)
TRAP_STUB_RET(rt_dir_remove, 1)
TRAP_STUB_RET(rt_dir_remove_all, 1)
TRAP_STUB_RET(rt_dir_cwd, 0)
TRAP_STUB_RET(rt_dir_chdir, 1)
TRAP_STUB_RET(rt_dir_home, 0)
TRAP_STUB_RET(rt_dir_temp, 0)

/* --- Process --- */
RuntimeValue rt_process_execute(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_process_exists(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_process_is_running(RuntimeValue a) { (void)a; return ENCODE_INT(0); }
RuntimeValue rt_process_run_with_limits(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { (void)a;(void)b;(void)c;(void)d; return NIL_VALUE; }
RuntimeValue rt_process_spawn_async(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
TRAP_STUB_RET(rt_process_run, 2)
TRAP_STUB_RET(rt_process_run_timeout, 3)
TRAP_STUB_RET(rt_process_spawn, 1)
TRAP_STUB_RET(rt_process_kill, 1)
TRAP_STUB_RET(rt_process_wait, 1)
TRAP_STUB_RET(rt_process_pid, 0)
/* rt_cli_get_args / rt_cli_args: aliased to args stubs below */
int32_t      rt_args_count(void)              { return 0; }
RuntimeValue rt_args_get(int32_t index)       { (void)index; return rt_string_from_cstr(""); }
RuntimeValue rt_args_all(void)                { return rt_array_new((RuntimeValue)0); }
RuntimeValue rt_cli_get_args(RuntimeValue _a) { (void)_a; return rt_array_new((RuntimeValue)0); }
RuntimeValue rt_cli_args(void)                { return rt_array_new((RuntimeValue)0); }
RuntimeValue rt_exit_code(void)               { return ENCODE_INT(0); }
/* rt_exit: noreturn — print exit marker then halt via wfi loop */
__attribute__((noreturn)) void rt_exit(int32_t code)
{
    serial_puts("[exit] rt_exit(");
    serial_put_dec((int64_t)code);
    serial_puts(") -- poweroff\r\n");
    __asm__ volatile("csrci mstatus, 0x8"); /* disable machine interrupts */
    qemu_poweroff(code);
}
TRAP_STUB_RET(rt_env_get, 1)
TRAP_STUB_RET(rt_env_set, 2)
TRAP_STUB_RET(rt_env_all, 0)

/* --- Print helpers --- */
RuntimeValue rt_cli_print(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_cli_println(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_cli_eprint(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_cli_eprintln(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }

/* rt_stdout_write / rt_stderr_write — decode SimpleOS RuntimeString and
 * emit each byte to the 16550 UART. Both stdout and stderr share the
 * serial sink (no tty layer yet). Replaces a missing stub so
 * std.io.Stdout / std.io.Stderr produce real output on riscv64. */
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
RuntimeValue rt_stdout_flush(RuntimeValue _a)   { (void)_a; return ENCODE_INT(0); }
RuntimeValue rt_stderr_write(RuntimeValue data) { return rt_serial_write_value(data); }
RuntimeValue rt_stderr_flush(RuntimeValue _a)   { (void)_a; return ENCODE_INT(0); }
RuntimeValue rt_eprint_str(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_eprint_value(RuntimeValue v) { rt_print(v); return NIL_VALUE; }
RuntimeValue rt_eprintln_str(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_eprintln_value(RuntimeValue v) { rt_print(v); serial_puts("\r\n"); return NIL_VALUE; }
RuntimeValue rt_cstring_to_text(RuntimeValue p) { (void)p; return NIL_VALUE; }
RuntimeValue rt_profiler_is_active(void) { return ENCODE_INT(0); }
RuntimeValue rt_profiler_record_call(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_profiler_record_return(RuntimeValue a) { (void)a; return NIL_VALUE; }
RuntimeValue rt_option_map(RuntimeValue o, RuntimeValue f) { (void)o;(void)f; return NIL_VALUE; }

/* --- Math --- */
S1(rt_math_sqrt) S1(rt_math_sin) S1(rt_math_cos) S1(rt_math_tan) S1(rt_math_asin)
S1(rt_math_acos) S1(rt_math_atan) S2(rt_math_atan2) S1(rt_math_abs) S1(rt_math_floor)
S1(rt_math_ceil) S1(rt_math_round) S1(rt_math_log) S1(rt_math_log2) S1(rt_math_log10)
S1(rt_math_exp) S2(rt_math_min) S2(rt_math_max) S2(rt_math_pow) S0(rt_math_random)
S0(rt_math_pi) S0(rt_math_e) S0(rt_math_inf) S0(rt_math_nan) S1(rt_math_is_nan) S1(rt_math_is_inf)

/* --- Timer / Clock --- */
S1(rt_time_now_ms) S0(rt_time_now_nanos) S0(rt_time_monotonic) S1(rt_sleep_ms)
S1(rt_timer_create) S1(rt_timer_cancel)

/* --- Interrupt / ISR --- */
S2(rt_register_isr) S1(rt_send_eoi) S0(rt_get_interrupt_flag)

/* --- Network --- */
TRAP_STUB_RET(rt_net_connect, 2) TRAP_STUB_RET(rt_net_listen, 1) TRAP_STUB_RET(rt_net_send, 2)
TRAP_STUB_RET(rt_net_recv, 1) TRAP_STUB_RET(rt_net_close, 1) TRAP_STUB_RET(rt_net_bind, 2)
TRAP_STUB_RET(rt_net_accept, 1) TRAP_STUB_RET(rt_net_set_timeout, 2) TRAP_STUB_RET(rt_net_get_addr, 1)

/* --- HTTP --- */
TRAP_STUB_RET(rt_http_get, 2) TRAP_STUB_RET(rt_http_post, 3) TRAP_STUB_RET(rt_http_put, 3)
TRAP_STUB_RET(rt_http_patch, 3) TRAP_STUB_RET(rt_http_delete, 2) TRAP_STUB_RET(rt_http_request, 2)
TRAP_STUB_RET(rt_http_request_full, 3) TRAP_STUB_RET(rt_http_set_header, 2)

/* --- JSON --- */
S1(rt_json_parse) S1(rt_json_stringify) S2(rt_json_get) S3(rt_json_set) S1(rt_json_keys) S1(rt_json_values) S1(rt_json_is_object) S1(rt_json_is_array)

/* --- Regex --- */
S2(ffi_regex_is_match) S2(ffi_regex_find) S2(ffi_regex_find_all) S2(ffi_regex_replace) S3(ffi_regex_replace_all) S1(ffi_regex_compile)

/* --- Test / BDD --- */
S1(rt_bdd_describe_start) S1(rt_bdd_describe_end) S2(rt_bdd_it_start) S1(rt_bdd_it_end)
S1(rt_expect) S2(rt_expect_eq) S2(rt_expect_ne) S2(rt_expect_gt) S2(rt_expect_lt)
S1(rt_expect_nil) S1(rt_expect_not_nil) S1(rt_expect_true) S1(rt_expect_false)
S2(rt_expect_contains) S2(rt_expect_throws) S0(rt_bdd_suite_start) S0(rt_bdd_suite_end) S0(rt_bdd_report)

/* --- Misc / Debug --- */
RuntimeValue rt_hash(RuntimeValue val)
{
    uint64_t h = 14695981039346656037ULL;
    if (IS_INT(val)) { int64_t n = DECODE_INT(val); for (int i = 0; i < 8; i++) { h ^= (uint8_t)(n & 0xFF); h *= 1099511628211ULL; n >>= 8; } }
    else if (IS_HEAP(val)) {
        HeapHeader *hdr = (HeapHeader *)DECODE_PTR(val);
        if (hdr && hdr->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)hdr; for (uint32_t i = 0; i < s->len; i++) { h ^= (uint8_t)s->data[i]; h *= 1099511628211ULL; } }
        else { uint64_t p = (uint64_t)(uintptr_t)hdr; for (int i = 0; i < 8; i++) { h ^= (uint8_t)(p & 0xFF); h *= 1099511628211ULL; p >>= 8; } }
    }
    return ENCODE_INT((int64_t)(h >> 3));
}

RuntimeValue rt_hash_combine(RuntimeValue h1, RuntimeValue h2) {
    int64_t a = DECODE_INT(h1), b = DECODE_INT(h2);
    uint64_t combined = (uint64_t)a ^ ((uint64_t)b + 0x9e3779b97f4a7c15ULL + ((uint64_t)a << 6) + ((uint64_t)a >> 2));
    return ENCODE_INT((int64_t)(combined >> 3));
}

RuntimeValue rt_debug_print(RuntimeValue val) { serial_puts("[DEBUG] "); rt_print_value(val); serial_putchar('\r'); serial_putchar('\n'); return NIL_VALUE; }
RuntimeValue rt_debug_dump(RuntimeValue val) { serial_puts("[DUMP] raw="); serial_put_hex((uint64_t)val); serial_puts(" tag="); serial_put_dec((int64_t)((uint64_t)val & TAG_MASK)); serial_putchar('\r'); serial_putchar('\n'); return NIL_VALUE; }
RuntimeValue rt_debug_break(void) { serial_puts("[BREAK] debug break\r\n"); return NIL_VALUE; }

RuntimeValue rt_panic(RuntimeValue msg) {
    serial_puts("[PANIC] ");
    if (IS_HEAP(msg)) { HeapHeader *h = (HeapHeader *)DECODE_PTR(msg); if (h && h->type == HEAP_STRING) { RuntimeString *s = (RuntimeString *)h; for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]); } else serial_puts("<non-string>"); }
    else serial_put_hex((uint64_t)msg);
    serial_puts("\r\n");
    for (;;) __asm__ volatile("wfi");
    return NIL_VALUE;
}

RuntimeValue rt_function_not_found(RuntimeValue name_ptr, RuntimeValue name_len) {
    serial_puts("[WARN] unresolved fn: ");
    if (name_ptr) { const char *p = (const char *)(uintptr_t)name_ptr; int64_t len = (int64_t)name_len; for (int64_t i = 0; i < len && i < 128; i++) serial_putchar(p[i]); }
    serial_puts("\r\n");
    return NIL_VALUE;
}

RuntimeValue rt_assert(RuntimeValue cond) {
    if (IS_INT(cond) && DECODE_INT(cond)) return NIL_VALUE;
    if (IS_HEAP(cond)) return NIL_VALUE;
    serial_puts("[ASSERT] assertion failed\r\n");
    for (;;) __asm__ volatile("wfi");
    return NIL_VALUE;
}

RuntimeValue rt_assert_eq(RuntimeValue a, RuntimeValue b) {
    if (rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_EQ] "); rt_print_value(a); serial_puts(" != "); rt_print_value(b); serial_puts("\r\n");
    for (;;) __asm__ volatile("wfi");
    return NIL_VALUE;
}

RuntimeValue rt_assert_ne(RuntimeValue a, RuntimeValue b) {
    if (!rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_NE] values are equal: "); rt_print_value(a); serial_puts("\r\n");
    for (;;) __asm__ volatile("wfi");
    return NIL_VALUE;
}

RuntimeValue rt_abort(RuntimeValue msg) { serial_puts("[ABORT] "); rt_print_value(msg); serial_puts("\r\n"); for (;;) __asm__ volatile("wfi"); return NIL_VALUE; }

/* GC: safe no-ops */
RuntimeValue rt_gc_collect(void) { return NIL_VALUE; }
RuntimeValue rt_gc_disable(void) { return NIL_VALUE; }
RuntimeValue rt_gc_enable(void) { return NIL_VALUE; }
RuntimeValue rt_gc_stats(void) { return NIL_VALUE; }

/* Threading: safe no-ops on single-threaded bare metal */
TRAP_STUB_RET(rt_thread_create, 1)
TRAP_STUB_RET(rt_thread_join, 1)
RuntimeValue rt_thread_yield(void) { return NIL_VALUE; }
RuntimeValue rt_thread_current(void) { return ENCODE_INT(0); }
RuntimeValue rt_thread_sleep(RuntimeValue a) { (void)a; return NIL_VALUE; }
TRAP_STUB_RET(rt_mutex_new, 0)
TRAP_STUB_RET(rt_mutex_lock, 1)
TRAP_STUB_RET(rt_mutex_unlock, 1)
TRAP_STUB_RET(rt_mutex_try_lock, 1)
TRAP_STUB_RET(rt_condvar_new, 0)
TRAP_STUB_RET(rt_condvar_wait, 1)
TRAP_STUB_RET(rt_condvar_notify, 1)
TRAP_STUB_RET(rt_condvar_notify_all, 1)

/* Channels */
TRAP_STUB_RET(rt_channel_new, 0)
TRAP_STUB_RET(rt_channel_send, 2)
TRAP_STUB_RET(rt_channel_recv, 1)
TRAP_STUB_RET(rt_channel_try_recv, 1)
TRAP_STUB_RET(rt_channel_close, 1)

/* Async */
TRAP_STUB_RET(rt_async_spawn, 1)
TRAP_STUB_RET(rt_async_await, 1)
RuntimeValue rt_async_yield(void) { return NIL_VALUE; }
TRAP_STUB_RET(rt_async_select, 2)

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

S1(rt_to_float)

/* Array extras not yet implemented */
S3(rt_array_insert) S1(rt_array_reverse) S1(rt_array_sort) S2(rt_array_sort_by)
S2(rt_array_map) S2(rt_array_filter) S3(rt_array_reduce) S2(rt_array_for_each)
S2(rt_array_find) S2(rt_array_find_index) S2(rt_array_every) S2(rt_array_some)
S1(rt_array_flatten) S2(rt_array_fill) S2(rt_array_zip) S1(rt_array_uniq) S1(rt_array_compact)

RuntimeValue rt_string_hash(RuntimeValue str) { return rt_hash(str); }
RuntimeValue rt_string_to_int(RuntimeValue s) { return rt_to_int(s); }
RuntimeValue rt_string_to_float(RuntimeValue s) { (void)s; return ENCODE_INT(0); }
RuntimeValue rt_string_join(RuntimeValue a, RuntimeValue sep) { return rt_array_join(a, sep); }
RuntimeValue rt_int_to_string(RuntimeValue val) { return rt_value_to_string(val); }

/* ===================================================================
 * Crypto — shared portable implementation
 * =================================================================== */
#define RV_INT int64_t
#define CRYPTO_ARRAY_HDR_TYPE(arr) ((arr)->type)
#define CRYPTO_ARRAY_ITEMS(arr) ((arr)->items)
#define CRYPTO_HAS_SERIAL_PUTHEX
#include "../../shared/crypto_common.h"

/* End of RISC-V64 baremetal_stubs.c */
