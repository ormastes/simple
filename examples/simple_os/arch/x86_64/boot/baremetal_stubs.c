/*
 * SimpleOS x86_64 Baremetal Runtime Stubs
 *
 * Provides a complete freestanding runtime for the Simple language compiler
 * targeting x86_64 bare-metal (QEMU isa-debug-exit, COM1 serial).
 *
 * Sections:
 *   1. Includes and types
 *   2. Serial I/O (COM1 0x3F8)
 *   3. RuntimeValue tagging
 *   4. Heap allocator (bump, 16 MB)
 *   5. Memory functions
 *   6. String operations
 *   7. Print functions
 *   8. Framebuffer copy
 *   9. _start (serial init, call spl_start, isa-debug-exit)
 *  10. No-op stubs (~200 runtime functions)
 *  11. Real x86_64 port-I/O and MMIO overrides
 */

/* ===================================================================
 * 1. Includes and types
 * =================================================================== */

#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;

/* ===================================================================
 * 2. Serial I/O — COM1 at 0x3F8 via x86 outb / inb
 *
 * Note: These use x86-specific asm constraints ("a", "Nd") that are
 * only valid when compiling for x86/x86_64 targets. Guard with
 * __x86_64__ to suppress false diagnostics on non-x86 host compilers.
 * =================================================================== */

#if defined(__x86_64__) || defined(__i386__)

static inline void outb(uint16_t port, uint8_t val)
{
    __asm__ volatile("outb %0, %1" : : "a"(val), "Nd"(port));
}

static inline uint8_t inb(uint16_t port)
{
    uint8_t r;
    __asm__ volatile("inb %1, %0" : "=a"(r) : "Nd"(port));
    return r;
}

static inline void outw(uint16_t port, uint16_t val)
{
    __asm__ volatile("outw %0, %1" : : "a"(val), "Nd"(port));
}

static inline uint16_t inw(uint16_t port)
{
    uint16_t r;
    __asm__ volatile("inw %1, %0" : "=a"(r) : "Nd"(port));
    return r;
}

static inline void outl(uint16_t port, uint32_t val)
{
    __asm__ volatile("outl %0, %1" : : "a"(val), "Nd"(port));
}

static inline uint32_t inl(uint16_t port)
{
    uint32_t r;
    __asm__ volatile("inl %1, %0" : "=a"(r) : "Nd"(port));
    return r;
}

static inline void io_wait(void)
{
    outb(0x80, 0);
}

#else
/* Stubs for non-x86 host analysis (never called at runtime) */
static inline void outb(uint16_t p, uint8_t v) { (void)p; (void)v; }
static inline uint8_t inb(uint16_t p) { (void)p; return 0; }
static inline void outw(uint16_t p, uint16_t v) { (void)p; (void)v; }
static inline uint16_t inw(uint16_t p) { (void)p; return 0; }
static inline void outl(uint16_t p, uint32_t v) { (void)p; (void)v; }
static inline uint32_t inl(uint16_t p) { (void)p; return 0; }
static inline void io_wait(void) {}
#endif

static void serial_putchar(char c)
{
    /* Wait until transmit holding register is empty (bit 5 of LSR) */
    while (!(inb(0x3F8 + 5) & 0x20)) {}
    outb(0x3F8, (uint8_t)c);
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
    /* Skip leading zeros but always print at least one digit */
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
        /* Handle INT64_MIN carefully */
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

/* Forward declaration — full definition in the Map section */
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
void rt_print_value(RuntimeValue val);

/* ===================================================================
 * 4. Heap allocator — bump allocator, 16 MB
 * =================================================================== */

static char   _heap[64 * 1024 * 1024] __attribute__((aligned(16)));
static size_t _heap_off = 0;

void *malloc(size_t sz)
{
    sz = (sz + 15) & ~(size_t)15;
    if (_heap_off + sz > sizeof(_heap)) {
        serial_puts("[PANIC] heap exhausted\r\n");
        for(;;) outb(0xF4, 0);
    }
    void *p = &_heap[_heap_off];
    _heap_off += sz;
    return p;
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
    size_t bytes = (size_t)DECODE_INT(sz);
    if (bytes == 0 || bytes > 0x1000000) bytes = (size_t)sz; /* fallback to raw */
    void *p = malloc(bytes);
    if (!p) return NIL_VALUE;
    return ENCODE_PTR(p);
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
    /* Parameters are raw (untagged) per the Rust runtime ABI.
       len_val is the raw byte count, data is a raw pointer. */
    int64_t len = len_val;
    if (len < 0 || len > 0x100000) return NIL_VALUE;
    /* len == 0 is valid: creates an empty string (used as f-string accumulator
       by compile_fstring_format which calls rt_string_new(NULL, 0)) */
    RuntimeString *s = (RuntimeString *)malloc(sizeof(RuntimeString) + (size_t)len + 1);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + (size_t)len + 1);
    s->len = (uint32_t)len;
    /* data is a raw pointer cast to i64 */
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
        /* empty string */
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

/* --- rt_value_to_string: convert any RuntimeValue to a string RuntimeValue --- */
RuntimeValue rt_value_to_string(RuntimeValue val)
{
    /* Integer -> decimal string */
    if (IS_INT(val)) {
        int64_t n = DECODE_INT(val);
        /* Handle zero */
        if (n == 0) return rt_string_from_cstr("0");
        /* Handle INT64_MIN */
        if (n == (-9223372036854775807LL - 1))
            return rt_string_from_cstr("-9223372036854775808");

        char buf[21]; /* max 20 digits + sign */
        int pos = 0;
        int neg = 0;
        uint64_t uv;
        if (n < 0) {
            neg = 1;
            uv = (uint64_t)(-n);
        } else {
            uv = (uint64_t)n;
        }
        /* Build digits in reverse */
        while (uv > 0) {
            buf[pos++] = '0' + (char)(uv % 10);
            uv /= 10;
        }
        /* Total length */
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
    /* Heap string -> return as-is */
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) return val;
        if (h && h->type == HEAP_ARRAY) return rt_string_from_cstr("<array>");
        if (h && h->type == HEAP_MAP) return rt_string_from_cstr("<map>");
        return rt_string_from_cstr("<object>");
    }
    /* nil */
    if (IS_NIL(val)) return rt_string_from_cstr("nil");
    /* float */
    if (IS_FLOAT(val)) return rt_string_from_cstr("<float>");
    /* unknown */
    return rt_string_from_cstr("<unknown>");
}

RuntimeValue rt_len(RuntimeValue v)
{
    if (IS_INT(v)) return ENCODE_INT(0);
    if (!IS_HEAP(v)) return ENCODE_INT(0);
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return ENCODE_INT(0);
    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        return ENCODE_INT(s->len);
    }
    if (h->type == HEAP_ARRAY) {
        RuntimeArray *a = (RuntimeArray *)h;
        return ENCODE_INT(a->len);
    }
    if (h->type == HEAP_MAP) {
        RuntimeMap *m = (RuntimeMap *)h;
        return ENCODE_INT(m->len);
    }
    return ENCODE_INT(0);
}

RuntimeValue rt_index_get(RuntimeValue v, RuntimeValue idx)
{
    if (!IS_HEAP(v)) return NIL_VALUE;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) return NIL_VALUE;
    if (h->type == HEAP_STRING) {
        return rt_string_char_at(v, idx);
    }
    if (h->type == HEAP_ARRAY) {
        int64_t i = DECODE_INT(idx);
        RuntimeArray *a = (RuntimeArray *)h;
        if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
        return a->items[i];
    }
    if (h->type == HEAP_MAP) {
        /* Map indexing: key is the idx argument */
        return rt_map_get(v, idx);
    }
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
        /* Map indexing: key is the idx argument */
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
    /* Fallback: try as raw pointer */
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
        /* Try as raw pointer */
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

void rt_print_int(RuntimeValue val)
{
    serial_put_dec(DECODE_INT(val));
}

void rt_println_int(RuntimeValue val)
{
    serial_put_dec(DECODE_INT(val));
    serial_putchar('\r');
    serial_putchar('\n');
}

void rt_print_char(RuntimeValue val)
{
    serial_putchar((char)DECODE_INT(val));
}

void rt_print_hex(RuntimeValue val)
{
    serial_put_hex((uint64_t)DECODE_INT(val));
}

void rt_print_bool(RuntimeValue val)
{
    if (DECODE_INT(val)) serial_puts("true");
    else serial_puts("false");
}

void rt_println_bool(RuntimeValue val)
{
    rt_print_bool(val);
    serial_putchar('\r');
    serial_putchar('\n');
}

/* --- rt_print: generic print to serial --- */
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
 * 8. Framebuffer copy
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

/* ===================================================================
 * 8b. Native comparison — Cranelift emits calls to these for == and !=.
 *     Receives raw i64 values (Cranelift ABI), returns 1 or 0.
 * =================================================================== */

RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b)
{
    /* Fast path: bitwise identical (same int, same pointer, both nil) */
    if (a == b) return 1;
    /* Heap objects: compare by content if both are strings */
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
 * 9. _start — serial init, spl_start, isa-debug-exit
 * =================================================================== */

static void _serial_init(void)
{
    /* Disable interrupts */
    outb(0x3F8 + 1, 0x00);
    /* Set DLAB (divisor latch access bit) */
    outb(0x3F8 + 3, 0x80);
    /* Set divisor to 1 (115200 baud) */
    outb(0x3F8 + 0, 0x01);  /* low byte */
    outb(0x3F8 + 1, 0x00);  /* high byte */
    /* 8 bits, no parity, one stop bit */
    outb(0x3F8 + 3, 0x03);
    /* Enable FIFO, clear, 14-byte threshold */
    outb(0x3F8 + 2, 0xC7);
    /* IRQs enabled, RTS/DSR set */
    outb(0x3F8 + 4, 0x0B);
}

/* ===================================================================
 * 9a. BGA framebuffer init — direct C, no runtime dependencies
 * =================================================================== */

#define BGA_INDEX_PORT 0x01CE
#define BGA_DATA_PORT  0x01CF

static void bga_write(uint16_t index, uint16_t value)
{
    outw(BGA_INDEX_PORT, index);
    outw(BGA_DATA_PORT, value);
}

static uint32_t pci_config_read32(uint8_t bus, uint8_t dev, uint8_t func, uint8_t off)
{
    uint32_t addr = 0x80000000u
        | ((uint32_t)bus << 16)
        | ((uint32_t)dev << 11)
        | ((uint32_t)func << 8)
        | ((uint32_t)(off & 0xFC));
    outl(0x0CF8, addr);
    return inl(0x0CFC);
}

static uint64_t detect_vga_lfb(void)
{
    for (uint8_t d = 0; d < 32; d++) {
        uint32_t vendor = pci_config_read32(0, d, 0, 0x00) & 0xFFFF;
        if (vendor == 0xFFFF || vendor == 0) continue;
        uint32_t cls = pci_config_read32(0, d, 0, 0x08);
        if (((cls >> 24) & 0xFF) == 0x03 && ((cls >> 16) & 0xFF) == 0x00) {
            uint32_t bar0 = pci_config_read32(0, d, 0, 0x10);
            uint64_t a = (uint64_t)(bar0 & 0xFFFFFFF0u);
            if (a) return a;
        }
    }
    return 0xFD000000ULL; /* QEMU Q35 fallback */
}

static uint64_t g_fb_addr;
static uint32_t g_fb_width, g_fb_height, g_fb_pitch;

static void bga_init(uint32_t w, uint32_t h, uint32_t bpp)
{
    bga_write(0x04, 0x00);           /* VBE_DISPI_DISABLE */
    bga_write(0x01, (uint16_t)w);    /* XRES */
    bga_write(0x02, (uint16_t)h);    /* YRES */
    bga_write(0x03, (uint16_t)bpp);  /* BPP */
    bga_write(0x04, 0x01 | 0x40);    /* ENABLE | LFB */
    g_fb_addr = detect_vga_lfb();
    g_fb_width = w;
    g_fb_height = h;
    g_fb_pitch = w * (bpp / 8);
}

static void fb_put_pixel(uint32_t x, uint32_t y, uint32_t color)
{
    if (x >= g_fb_width || y >= g_fb_height) return;
    volatile uint32_t *fb = (volatile uint32_t *)(uintptr_t)g_fb_addr;
    fb[y * (g_fb_pitch / 4) + x] = color;
}

static void fb_fill_rect(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t color)
{
    for (uint32_t dy = 0; dy < h; dy++)
        for (uint32_t dx = 0; dx < w; dx++)
            fb_put_pixel(x + dx, y + dy, color);
}

/* 8x16 bitmap font — minimal ASCII subset for "Hello World" */
static const uint8_t font_H[] = {0x42,0x42,0x42,0x42,0x7E,0x42,0x42,0x42,0x42,0x42,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_e[] = {0x00,0x00,0x00,0x00,0x3C,0x42,0x7E,0x40,0x3C,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_l[] = {0x00,0x20,0x20,0x20,0x20,0x20,0x20,0x20,0x3C,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_o[] = {0x00,0x00,0x00,0x00,0x3C,0x42,0x42,0x42,0x3C,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_W[] = {0x41,0x41,0x41,0x41,0x49,0x49,0x55,0x55,0x22,0x22,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_r[] = {0x00,0x00,0x00,0x00,0x5C,0x62,0x40,0x40,0x40,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_d[] = {0x00,0x02,0x02,0x02,0x3E,0x42,0x42,0x42,0x3E,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_bang[] = {0x00,0x10,0x10,0x10,0x10,0x10,0x10,0x00,0x10,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_space[] = {0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0};
static const uint8_t font_S[] = {0x3C,0x42,0x40,0x40,0x3C,0x02,0x02,0x42,0x3C,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_i[] = {0x00,0x00,0x10,0x00,0x10,0x10,0x10,0x10,0x10,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_m[] = {0x00,0x00,0x00,0x00,0x76,0x49,0x49,0x49,0x49,0x00,0x00,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_p[] = {0x00,0x00,0x00,0x00,0x5C,0x62,0x42,0x62,0x5C,0x40,0x40,0x00,0x00,0x00,0x00,0x00};
static const uint8_t font_O[] = {0x3C,0x42,0x42,0x42,0x42,0x42,0x42,0x42,0x3C,0x00,0x00,0x00,0x00,0x00,0x00,0x00};

static void fb_draw_char(uint32_t x, uint32_t y, const uint8_t *glyph, uint32_t fg, uint32_t bg)
{
    for (int row = 0; row < 16; row++) {
        uint8_t bits = (row < 10) ? glyph[row] : 0;
        for (int col = 0; col < 8; col++) {
            uint32_t color = (bits & (0x80 >> col)) ? fg : bg;
            fb_put_pixel(x + (uint32_t)col, y + (uint32_t)row, color);
        }
    }
}

static const uint8_t *get_glyph(char c)
{
    switch (c) {
        case 'H': return font_H; case 'e': return font_e; case 'l': return font_l;
        case 'o': return font_o; case 'W': return font_W; case 'r': return font_r;
        case 'd': return font_d; case '!': return font_bang; case ' ': return font_space;
        case 'S': return font_S; case 'i': return font_i; case 'm': return font_m;
        case 'p': return font_p; case 'O': return font_O;
        default: return font_space;
    }
}

static void fb_draw_text(uint32_t x, uint32_t y, const char *text, uint32_t fg, uint32_t bg)
{
    while (*text) {
        fb_draw_char(x, y, get_glyph(*text), fg, bg);
        x += 9; /* 8px char + 1px gap */
        text++;
    }
}

/* ===================================================================
 * 9b. Framebuffer rendering helpers for Pure Simple GUI
 *
 * These are called via extern fn from pure_gui.spl.
 * Cranelift passes RAW (untagged) u64 values for all args.
 * =================================================================== */

static uint64_t g_fb_addr = 0xFD000000;
static uint64_t g_fb_w = 1024;

RuntimeValue rt_gui_set_fb(RuntimeValue addr, RuntimeValue w)
{
    g_fb_addr = (uint64_t)addr;
    g_fb_w = (uint64_t)w;
    return 0;
}

RuntimeValue rt_gui_hline(RuntimeValue y, RuntimeValue x, RuntimeValue count, RuntimeValue color)
{
    uint64_t base = g_fb_addr + ((uint64_t)y * g_fb_w + (uint64_t)x) * 4;
    uint32_t c = (uint32_t)(uint64_t)color;
    for (uint64_t i = 0; i < (uint64_t)count; i++) {
        *(volatile uint32_t *)(uintptr_t)(base + i * 4) = c;
    }
    return 0;
}

/* 4-arg version: pack x|y into xy and w|h into wh (high 32 = first, low 32 = second) */
RuntimeValue rt_gui_fill4(RuntimeValue xy, RuntimeValue wh, RuntimeValue color, RuntimeValue _unused)
{
    (void)_unused;
    uint32_t rx = (uint32_t)((uint64_t)xy >> 32);
    uint32_t ry = (uint32_t)((uint64_t)xy & 0xFFFFFFFF);
    uint32_t rw = (uint32_t)((uint64_t)wh >> 32);
    uint32_t rh = (uint32_t)((uint64_t)wh & 0xFFFFFFFF);
    uint32_t c = (uint32_t)(uint64_t)color;
    for (uint32_t row = 0; row < rh; row++) {
        uint64_t base = g_fb_addr + ((uint64_t)(ry + row) * g_fb_w + rx) * 4;
        for (uint32_t col = 0; col < rw; col++) {
            *(volatile uint32_t *)(uintptr_t)(base + col * 4) = c;
        }
    }
    return 0;
}

/* ===================================================================
 * 9c. _start — BGA init, hello world, then spl_start
 * =================================================================== */

/* serial_println — called by compiled Simple code (extern fn serial_println) */
RuntimeValue serial_println(RuntimeValue val) {
    rt_print(val);
    serial_puts("\r\n");
    return NIL_VALUE;
}

extern void spl_start(void) __attribute__((weak));

void _start(void)
{
    /* Disable all PIC IRQs to prevent timer interrupts during rendering.
     * Mask all IRQs on both PICs (master 0x21, slave 0xA1). */
    outb(0x21, 0xFF);
    outb(0xA1, 0xFF);
    /* Also disable APIC timer if APIC is present */
    __asm__ volatile("cli");

    _serial_init();

    serial_puts("SimpleOS x86_64 boot\r\n");
    serial_puts("[BOOT] COM1 serial initialized at 115200 baud\r\n");
    serial_puts("[BOOT] Heap: 64 MB bump allocator\r\n");
    serial_puts("[BOOT] RuntimeValue: tagged 64-bit (int/heap/float/special)\r\n");

    /* BGA + GUI rendering is now done by Pure Simple code in spl_start().
     * C boot stub only provides serial, heap, and runtime stubs.
     */

    if (spl_start) {
        serial_puts("[BOOT] Calling spl_start()...\r\n");
        spl_start();
        serial_puts("[BOOT] spl_start() returned\r\n");
    } else {
        serial_puts("[BOOT] No spl_start() found (weak symbol)\r\n");
    }

    serial_puts("[BOOT] x86_64 boot complete\r\n");

    /* Halt forever (don't exit — keep display visible) */
    for (;;) {
        __asm__ volatile("hlt");
    }
}

/* ===================================================================
 * 10. Fatal-panic stubs — macro-generated runtime function stubs
 *
 * These provide link-time symbols for all runtime functions that the
 * Simple compiler may reference.  On bare metal, unimplemented stubs
 * print the function name to serial and halt (cli; hlt) instead of
 * silently returning 0, which would cause cascading silent failures.
 *
 * Functions that are intentionally safe as no-ops on bare metal
 * (GC, thread yield/current/sleep, async yield) are defined as
 * explicit inline implementations, NOT via the S* macros.
 * =================================================================== */

#define S0(n) RuntimeValue n(void) { \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}
#define S1(n) RuntimeValue n(RuntimeValue a) { \
    (void)a; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}
#define S2(n) RuntimeValue n(RuntimeValue a, RuntimeValue b) { \
    (void)a; (void)b; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}
#define S3(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c) { \
    (void)a; (void)b; (void)c; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}
#define S4(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d) { \
    (void)a; (void)b; (void)c; (void)d; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}
#define S5(n) RuntimeValue n(RuntimeValue a, RuntimeValue b, RuntimeValue c, RuntimeValue d, RuntimeValue e) { \
    (void)a; (void)b; (void)c; (void)d; (void)e; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
    return 0; \
}

/* void-return stub macros */
#define V0(n) void n(void) { \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
}
#define V1(n) void n(RuntimeValue a) { \
    (void)a; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
}
#define V2(n) void n(RuntimeValue a, RuntimeValue b) { \
    (void)a; (void)b; \
    serial_puts("FATAL: unimplemented rt function: " #n "\n"); \
    for(;;) __asm__ volatile("cli; hlt"); \
}

/* --- Arithmetic / comparison ---
 *
 * Cranelift emits raw i64 values.  These operate on tagged RuntimeValues:
 * integer args are ENCODE_INT(n) = n<<3, results likewise.
 * Comparison results are raw 1 or 0 (Cranelift boolean convention).
 */

RuntimeValue rt_add(RuntimeValue a, RuntimeValue b)
{
    if (IS_INT(a) && IS_INT(b))
        return ENCODE_INT(DECODE_INT(a) + DECODE_INT(b));
    /* String concat fallback */
    if (IS_HEAP(a) || IS_HEAP(b))
        return rt_string_concat(a, b);
    return ENCODE_INT(0);
}

RuntimeValue rt_sub(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) - DECODE_INT(b));
}

RuntimeValue rt_mul(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) * DECODE_INT(b));
}

RuntimeValue rt_div(RuntimeValue a, RuntimeValue b)
{
    int64_t denom = DECODE_INT(b);
    if (denom == 0) return ENCODE_INT(0); /* avoid div-by-zero trap */
    return ENCODE_INT(DECODE_INT(a) / denom);
}

RuntimeValue rt_mod(RuntimeValue a, RuntimeValue b)
{
    int64_t denom = DECODE_INT(b);
    if (denom == 0) return ENCODE_INT(0);
    return ENCODE_INT(DECODE_INT(a) % denom);
}

RuntimeValue rt_pow(RuntimeValue a, RuntimeValue b)
{
    int64_t base = DECODE_INT(a);
    int64_t exp  = DECODE_INT(b);
    if (exp < 0) return ENCODE_INT(0);
    int64_t result = 1;
    for (int64_t i = 0; i < exp; i++) result *= base;
    return ENCODE_INT(result);
}

RuntimeValue rt_eq(RuntimeValue a, RuntimeValue b)
{
    return rt_native_eq(a, b) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_ne(RuntimeValue a, RuntimeValue b)
{
    return rt_native_eq(a, b) ? FALSE_VALUE : TRUE_VALUE;
}

RuntimeValue rt_lt(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) < DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_gt(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) > DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_le(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) <= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_ge(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) >= DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_and(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) && DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_or(RuntimeValue a, RuntimeValue b)
{
    return (DECODE_INT(a) || DECODE_INT(b)) ? TRUE_VALUE : FALSE_VALUE;
}

RuntimeValue rt_not(RuntimeValue a)
{
    return DECODE_INT(a) ? FALSE_VALUE : TRUE_VALUE;
}

RuntimeValue rt_shl(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) << DECODE_INT(b));
}

RuntimeValue rt_shr(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) >> DECODE_INT(b));
}

RuntimeValue rt_bitand(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) & DECODE_INT(b));
}

RuntimeValue rt_bitor(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) | DECODE_INT(b));
}

RuntimeValue rt_bitxor(RuntimeValue a, RuntimeValue b)
{
    return ENCODE_INT(DECODE_INT(a) ^ DECODE_INT(b));
}

RuntimeValue rt_bitnot(RuntimeValue a)
{
    return ENCODE_INT(~DECODE_INT(a));
}

RuntimeValue rt_neg(RuntimeValue a)
{
    return ENCODE_INT(-DECODE_INT(a));
}

/* --- Type introspection / conversion ---
 *
 * rt_typeof returns a string describing the type.
 * rt_is_* predicates return raw 1 or 0 for Cranelift boolean ABI.
 */

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

RuntimeValue rt_is_nil(RuntimeValue val)
{
    return IS_NIL(val) ? 1 : 0;
}

RuntimeValue rt_is_int(RuntimeValue val)
{
    return IS_INT(val) ? 1 : 0;
}

RuntimeValue rt_is_float(RuntimeValue val)
{
    return IS_FLOAT(val) ? 1 : 0;
}

RuntimeValue rt_is_string(RuntimeValue val)
{
    if (!IS_HEAP(val)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    return (h && h->type == HEAP_STRING) ? 1 : 0;
}

RuntimeValue rt_is_bool(RuntimeValue val)
{
    /* Booleans are encoded as ENCODE_INT(0) or ENCODE_INT(1) */
    if (!IS_INT(val)) return 0;
    int64_t v = DECODE_INT(val);
    return (v == 0 || v == 1) ? 1 : 0;
}

RuntimeValue rt_is_array(RuntimeValue val)
{
    if (!IS_HEAP(val)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    return (h && h->type == HEAP_ARRAY) ? 1 : 0;
}

RuntimeValue rt_is_map(RuntimeValue val)
{
    if (!IS_HEAP(val)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    return (h && h->type == HEAP_MAP) ? 1 : 0;
}

RuntimeValue rt_is_object(RuntimeValue val)
{
    if (!IS_HEAP(val)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    return (h && h->type == HEAP_OBJECT) ? 1 : 0;
}
/* rt_to_int: convert to integer */
RuntimeValue rt_to_int(RuntimeValue val)
{
    if (IS_INT(val)) return val;
    if (IS_NIL(val)) return ENCODE_INT(0);
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) {
            /* Parse decimal string to integer */
            RuntimeString *s = (RuntimeString *)h;
            if (s->len == 0) return ENCODE_INT(0);
            int64_t result = 0;
            int neg = 0;
            uint32_t i = 0;
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
S1(rt_to_float)
/* rt_to_string: convert to string (delegates to rt_value_to_string) */
RuntimeValue rt_to_string(RuntimeValue val)
{
    return rt_value_to_string(val);
}
/* rt_to_bool: convert to boolean */
RuntimeValue rt_to_bool(RuntimeValue val)
{
    if (IS_NIL(val)) return FALSE_VALUE;
    if (IS_INT(val)) return DECODE_INT(val) ? TRUE_VALUE : FALSE_VALUE;
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            return s->len > 0 ? TRUE_VALUE : FALSE_VALUE;
        }
        if (h && h->type == HEAP_ARRAY) {
            RuntimeArray *a = (RuntimeArray *)h;
            return a->len > 0 ? TRUE_VALUE : FALSE_VALUE;
        }
        return TRUE_VALUE; /* non-nil heap object is truthy */
    }
    return FALSE_VALUE;
}
/* rt_clone: return as-is for primitives; shallow copy for heap objects */
RuntimeValue rt_clone(RuntimeValue val)
{
    if (!IS_HEAP(val)) return val; /* int, nil, float: value semantics */
    HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
    if (!h) return val;
    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        return rt_string_new((RuntimeValue)(uintptr_t)s->data, (RuntimeValue)s->len);
    }
    if (h->type == HEAP_ARRAY) {
        RuntimeArray *a = (RuntimeArray *)h;
        RuntimeValue new_arr = rt_array_new(ENCODE_INT(a->cap));
        for (uint32_t i = 0; i < a->len; i++) {
            new_arr = rt_array_push(new_arr, a->items[i]);
        }
        return new_arr;
    }
    if (h->type == HEAP_MAP) {
        return rt_map_clone(val);
    }
    return val; /* unknown heap type: return as-is */
}

/* rt_freeze / rt_is_frozen: no-ops on bare metal (no GC, no mutability tracking) */
RuntimeValue rt_freeze(RuntimeValue val)
{
    return val;
}

RuntimeValue rt_is_frozen(RuntimeValue val)
{
    (void)val;
    return 0; /* always mutable on bare metal */
}

/* --- String extras ---
 *
 * Implement commonly-needed string operations for VFS routing and
 * general OS string handling.  Less-used ops remain as stubs.
 */

/* Helper: get RuntimeString pointer, or NULL */
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
    /* substr(str, start) -- returns from start to end */
    RuntimeString *s = decode_string(str);
    if (!s) return NIL_VALUE;
    int64_t a = DECODE_INT(start);
    if (a < 0) a = 0;
    if ((uint32_t)a >= s->len) {
        return rt_string_from_cstr("");
    }
    return rt_string_slice(str, start, ENCODE_INT(s->len));
}

/* rt_string_split: split by delimiter, return array of strings */
RuntimeValue rt_string_split(RuntimeValue str, RuntimeValue delim)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *d = decode_string(delim);
    RuntimeValue arr = rt_array_new(ENCODE_INT(4));
    if (!s || s->len == 0) return arr;
    if (!d || d->len == 0) {
        /* Split into individual characters */
        for (uint32_t i = 0; i < s->len; i++) {
            RuntimeValue ch = rt_string_new(
                (RuntimeValue)(uintptr_t)&s->data[i], 1);
            arr = rt_array_push(arr, ch);
        }
        return arr;
    }
    uint32_t start = 0;
    for (uint32_t i = 0; i <= s->len - d->len; ) {
        uint32_t j;
        for (j = 0; j < d->len; j++) {
            if (s->data[i + j] != d->data[j]) break;
        }
        if (j == d->len) {
            /* Found delimiter at i */
            RuntimeValue part = rt_string_slice(str,
                ENCODE_INT(start), ENCODE_INT(i));
            arr = rt_array_push(arr, part);
            i += d->len;
            start = i;
        } else {
            i++;
        }
    }
    /* Remainder */
    RuntimeValue rest = rt_string_slice(str,
        ENCODE_INT(start), ENCODE_INT(s->len));
    arr = rt_array_push(arr, rest);
    return arr;
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

/* rt_string_replace(str, old, new) — replace first occurrence */
RuntimeValue rt_string_replace(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *o = decode_string(old_val);
    RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str;
    if (o->len > s->len) return str; /* needle longer than haystack */
    if (!n) n = (RuntimeString *)0; /* treat nil replacement as empty */
    uint32_t nlen = n ? n->len : 0;

    /* Find first occurrence */
    for (uint32_t i = 0; i <= s->len - o->len; i++) {
        uint32_t j;
        for (j = 0; j < o->len; j++) {
            if (s->data[i + j] != o->data[j]) break;
        }
        if (j == o->len) {
            /* Found at position i */
            uint32_t result_len = s->len - o->len + nlen;
            RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
            if (!r) return str;
            r->hdr.type = HEAP_STRING;
            r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
            r->len = result_len;
            /* Copy: prefix + replacement + suffix */
            __builtin_memcpy(r->data, s->data, i);
            if (n && nlen > 0) __builtin_memcpy(r->data + i, n->data, nlen);
            __builtin_memcpy(r->data + i + nlen, s->data + i + o->len, s->len - i - o->len);
            r->data[result_len] = '\0';
            return ENCODE_PTR(r);
        }
    }
    return str; /* not found, return original */
}

/* rt_string_replace_all(str, old, new) — replace all occurrences (single-pass) */
RuntimeValue rt_string_replace_all(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    RuntimeString *s = decode_string(str);
    RuntimeString *o = decode_string(old_val);
    RuntimeString *n = decode_string(new_val);
    if (!s || !o || o->len == 0) return str;
    uint32_t nlen = n ? n->len : 0;

    /* First pass: count occurrences to compute result size */
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

    /* Allocate result */
    uint32_t result_len = s->len - count * o->len + count * nlen;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + result_len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + result_len + 1);
    r->len = result_len;

    /* Second pass: build result */
    uint32_t out = 0;
    for (uint32_t i = 0; i < s->len; ) {
        if (i + o->len <= s->len) {
            uint32_t j;
            for (j = 0; j < o->len; j++) {
                if (s->data[i + j] != o->data[j]) break;
            }
            if (j == o->len) {
                if (n && nlen > 0) {
                    __builtin_memcpy(r->data + out, n->data, nlen);
                    out += nlen;
                }
                i += o->len;
                continue;
            }
        }
        r->data[out++] = s->data[i++];
    }
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

/* rt_string_repeat(str, count) — repeat string N times */
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
    for (int64_t i = 0; i < count; i++) {
        __builtin_memcpy(r->data + i * s->len, s->data, s->len);
    }
    r->data[result_len] = '\0';
    return ENCODE_PTR(r);
}

/* rt_string_pad_start(str, width) — left-pad with spaces to width */
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

/* rt_string_pad_end(str, width) — right-pad with spaces to width */
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

/* rt_string_reverse(str) — reverse the string */
RuntimeValue rt_string_reverse(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    if (!s || s->len <= 1) return str;
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + s->len + 1);
    if (!r) return str;
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1);
    r->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) {
        r->data[i] = s->data[s->len - 1 - i];
    }
    r->data[s->len] = '\0';
    return ENCODE_PTR(r);
}

/* rt_string_chars(str) — return array of single-character strings */
RuntimeValue rt_string_chars(RuntimeValue str)
{
    RuntimeString *s = decode_string(str);
    RuntimeValue arr = rt_array_new(ENCODE_INT(s ? s->len : 0));
    if (!s) return arr;
    for (uint32_t i = 0; i < s->len; i++) {
        RuntimeValue ch = rt_string_new(
            (RuntimeValue)(uintptr_t)&s->data[i], 1);
        arr = rt_array_push(arr, ch);
    }
    return arr;
}

/* rt_string_bytes(str) — return array of byte values */
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
    if (!s) return 1; /* nil/non-string is "empty" */
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
            return ENCODE_INT((int64_t)(unsigned char)sa->data[i]
                            - (int64_t)(unsigned char)sb->data[i]);
    }
    if (sa->len < sb->len) return ENCODE_INT(-1);
    if (sa->len > sb->len) return ENCODE_INT(1);
    return ENCODE_INT(0);
}

/* --- rt_string_format(fmt, args_or_val) ---
 *
 * The compiler does NOT use this function for f-string interpolation
 * (it uses rt_string_new + rt_value_to_string + rt_string_concat instead).
 * This is a fallback/legacy symbol. Implement as simple concatenation
 * of the format template with the value converted to string. */
RuntimeValue rt_string_format(RuntimeValue fmt, RuntimeValue val)
{
    /* If fmt is a string template, just concatenate with val's string repr.
       For proper Python-style formatting, use rt_value_format_string. */
    RuntimeValue val_str = rt_value_to_string(val);
    if (!IS_HEAP(fmt)) return val_str;
    return rt_string_concat(fmt, val_str);
}

/* --- Helper: integer to decimal string in buffer, returns length --- */
static int int_to_buf(char *buf, int buf_size, int64_t n)
{
    if (n == 0) { buf[0] = '0'; return 1; }
    int neg = 0;
    uint64_t uv;
    if (n < 0) { neg = 1; uv = (uint64_t)(-n); }
    else { uv = (uint64_t)n; }
    /* Build digits in reverse */
    char tmp[21];
    int pos = 0;
    while (uv > 0 && pos < 20) {
        tmp[pos++] = '0' + (char)(uv % 10);
        uv /= 10;
    }
    int out = 0;
    if (neg && out < buf_size) buf[out++] = '-';
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

/* --- Helper: integer to hex string in buffer, returns length --- */
static int int_to_hex_buf(char *buf, int buf_size, uint64_t v, int uppercase)
{
    const char *digits = uppercase ? "0123456789ABCDEF" : "0123456789abcdef";
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[17];
    int pos = 0;
    while (v > 0 && pos < 16) {
        tmp[pos++] = digits[v & 0xF];
        v >>= 4;
    }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

/* --- Helper: integer to octal string in buffer, returns length --- */
static int int_to_oct_buf(char *buf, int buf_size, uint64_t v)
{
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[23];
    int pos = 0;
    while (v > 0 && pos < 22) {
        tmp[pos++] = '0' + (char)(v & 7);
        v >>= 3;
    }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

/* --- Helper: integer to binary string in buffer, returns length --- */
static int int_to_bin_buf(char *buf, int buf_size, uint64_t v)
{
    if (v == 0) { buf[0] = '0'; return 1; }
    char tmp[65];
    int pos = 0;
    while (v > 0 && pos < 64) {
        tmp[pos++] = '0' + (char)(v & 1);
        v >>= 1;
    }
    int out = 0;
    while (pos > 0 && out < buf_size) buf[out++] = tmp[--pos];
    return out;
}

/* --- rt_value_format_string(val, fmt_ptr, fmt_len) ---
 *
 * Format a RuntimeValue using a Python-style format specifier.
 * Signature: (RuntimeValue val, RuntimeValue fmt_ptr, RuntimeValue fmt_len) -> RuntimeValue
 * where fmt_ptr is a raw pointer to the format spec bytes and fmt_len is the byte count.
 *
 * Supports: [[fill]align][sign][#][0][width][.precision][type]
 * Types: f(fixed-point), d(decimal), x/X(hex), o(octal), b(binary), s(string)
 */
RuntimeValue rt_value_format_string(RuntimeValue val, RuntimeValue fmt_ptr_rv, RuntimeValue fmt_len_rv)
{
    const char *spec = (const char *)(uintptr_t)fmt_ptr_rv;
    int64_t spec_len = fmt_len_rv;

    /* If no format spec, just convert to string */
    if (!spec || spec_len <= 0) {
        return rt_value_to_string(val);
    }

    /* Parse the format spec: [[fill]align][sign][#][0][width][.precision][type] */
    char fill = ' ';
    char align = '\0';    /* '<' '>' '^' '=' or '\0' for default */
    char sign_mode = '\0'; /* '+' '-' ' ' or '\0' */
    int alt_form = 0;     /* '#' prefix */
    int zero_pad = 0;     /* '0' before width */
    int width = -1;       /* -1 = no width */
    int precision = -1;   /* -1 = no precision */
    char type_code = '\0';
    int pos = 0;

    /* Check for [fill]align */
    if (spec_len >= 2 && (spec[1] == '<' || spec[1] == '>' || spec[1] == '^' || spec[1] == '=')) {
        fill = spec[0];
        align = spec[1];
        pos = 2;
    } else if (spec_len >= 1 && (spec[0] == '<' || spec[0] == '>' || spec[0] == '^' || spec[0] == '=')) {
        align = spec[0];
        pos = 1;
    }

    /* Sign */
    if (pos < spec_len && (spec[pos] == '+' || spec[pos] == '-' || spec[pos] == ' ')) {
        sign_mode = spec[pos];
        pos++;
    }

    /* Alt form '#' */
    if (pos < spec_len && spec[pos] == '#') {
        alt_form = 1;
        pos++;
    }

    /* Zero pad '0' (before width) */
    if (pos < spec_len && spec[pos] == '0') {
        zero_pad = 1;
        pos++;
    }

    /* Width (digits) */
    if (pos < spec_len && spec[pos] >= '1' && spec[pos] <= '9') {
        width = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') {
            width = width * 10 + (spec[pos] - '0');
            pos++;
        }
    }

    /* Precision */
    if (pos < spec_len && spec[pos] == '.') {
        pos++;
        precision = 0;
        while (pos < spec_len && spec[pos] >= '0' && spec[pos] <= '9') {
            precision = precision * 10 + (spec[pos] - '0');
            pos++;
        }
    }

    /* Type code */
    if (pos < spec_len) {
        type_code = spec[pos];
    }

    /* Format the raw value based on type code */
    char raw_buf[128];
    int raw_len = 0;

    int64_t int_val = 0;
    if (IS_INT(val)) int_val = DECODE_INT(val);

    switch (type_code) {
    case 'd': {
        /* Decimal integer */
        int64_t v = int_val;
        int is_neg = (v < 0);
        uint64_t abs_v = is_neg ? (uint64_t)(-v) : (uint64_t)v;
        char digits[21];
        int dlen = int_to_buf(digits, 21, (int64_t)abs_v);
        /* Apply sign */
        raw_len = 0;
        if (is_neg) raw_buf[raw_len++] = '-';
        else if (sign_mode == '+') raw_buf[raw_len++] = '+';
        else if (sign_mode == ' ') raw_buf[raw_len++] = ' ';
        __builtin_memcpy(raw_buf + raw_len, digits, (size_t)dlen);
        raw_len += dlen;
        break;
    }
    case 'x': case 'X': {
        /* Hexadecimal */
        uint64_t v = (uint64_t)int_val;
        raw_len = 0;
        if (alt_form) {
            raw_buf[raw_len++] = '0';
            raw_buf[raw_len++] = (type_code == 'X') ? 'X' : 'x';
        }
        int hlen = int_to_hex_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len),
                                  v, (type_code == 'X'));
        raw_len += hlen;
        break;
    }
    case 'o': {
        /* Octal */
        uint64_t v = (uint64_t)int_val;
        raw_len = 0;
        if (alt_form) {
            raw_buf[raw_len++] = '0';
            raw_buf[raw_len++] = 'o';
        }
        int olen = int_to_oct_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), v);
        raw_len += olen;
        break;
    }
    case 'b': {
        /* Binary */
        uint64_t v = (uint64_t)int_val;
        raw_len = 0;
        if (alt_form) {
            raw_buf[raw_len++] = '0';
            raw_buf[raw_len++] = 'b';
        }
        int blen = int_to_bin_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), v);
        raw_len += blen;
        break;
    }
    case 'f': case 'F': {
        /* Fixed-point float — baremetal approximation for integers.
           Without FPU support, treat int as fixed-point: just append ".000000".
           If precision is 0, no decimal point. */
        int prec = (precision >= 0) ? precision : 6;
        int is_neg = (int_val < 0);
        int64_t abs_v = is_neg ? -int_val : int_val;
        raw_len = 0;
        if (is_neg) raw_buf[raw_len++] = '-';
        else if (sign_mode == '+') raw_buf[raw_len++] = '+';
        else if (sign_mode == ' ') raw_buf[raw_len++] = ' ';
        int dlen = int_to_buf(raw_buf + raw_len, (int)(sizeof(raw_buf) - (size_t)raw_len), abs_v);
        raw_len += dlen;
        if (prec > 0) {
            raw_buf[raw_len++] = '.';
            for (int i = 0; i < prec && raw_len < (int)sizeof(raw_buf) - 1; i++) {
                raw_buf[raw_len++] = '0';
            }
        }
        break;
    }
    case 's': case '\0': default: {
        /* String or default: convert to string, apply precision as max length */
        RuntimeValue str_rv = rt_value_to_string(val);
        RuntimeString *str_s = decode_string(str_rv);
        if (str_s) {
            int slen = (int)str_s->len;
            if (precision >= 0 && slen > precision) slen = precision;
            if (slen > (int)sizeof(raw_buf) - 1) slen = (int)sizeof(raw_buf) - 1;
            __builtin_memcpy(raw_buf, str_s->data, (size_t)slen);
            raw_len = slen;
        } else {
            /* rt_value_to_string returned nil — use "nil" */
            __builtin_memcpy(raw_buf, "nil", 3);
            raw_len = 3;
        }
        break;
    }
    }

    /* Apply width and alignment */
    if (width > 0 && raw_len < width) {
        int padding = width - raw_len;
        char fill_char = (zero_pad && align == '\0') ? '0' : fill;
        char eff_align = align;
        if (eff_align == '\0') {
            eff_align = zero_pad ? '>' : '<'; /* default alignment */
        }

        char result_buf[256];
        int result_len = 0;

        switch (eff_align) {
        case '>': {
            /* Right-align: for zero-pad, insert after sign */
            if (fill_char == '0' && raw_len > 0 &&
                (raw_buf[0] == '+' || raw_buf[0] == '-' || raw_buf[0] == ' ')) {
                result_buf[result_len++] = raw_buf[0]; /* sign */
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 1; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            } else {
                for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
                for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            }
            break;
        }
        case '<': {
            /* Left-align */
            for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            for (int i = 0; i < padding && result_len < 255; i++) result_buf[result_len++] = fill_char;
            break;
        }
        case '^': {
            /* Center-align */
            int left_pad = padding / 2;
            int right_pad = padding - left_pad;
            for (int i = 0; i < left_pad && result_len < 255; i++) result_buf[result_len++] = fill_char;
            for (int i = 0; i < raw_len && result_len < 255; i++) result_buf[result_len++] = raw_buf[i];
            for (int i = 0; i < right_pad && result_len < 255; i++) result_buf[result_len++] = fill_char;
            break;
        }
        case '=': {
            /* Pad between sign and digits */
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
        }

        return rt_string_new((RuntimeValue)(uintptr_t)result_buf, (RuntimeValue)result_len);
    }

    /* No width/alignment needed — return raw formatted value */
    return rt_string_new((RuntimeValue)(uintptr_t)raw_buf, (RuntimeValue)raw_len);
}

/* --- Array --- */

/* rt_array_new: create a new array with given capacity */
RuntimeValue rt_array_new(RuntimeValue cap_val)
{
    int64_t cap = DECODE_INT(cap_val);
    if (cap <= 0) cap = 4; /* default capacity */
    if (cap > 0x100000) cap = 0x100000; /* safety limit */
    size_t alloc_size = sizeof(RuntimeArray) + (size_t)cap * sizeof(RuntimeValue);
    RuntimeArray *a = (RuntimeArray *)malloc(alloc_size);
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)alloc_size;
    a->len = 0;
    a->cap = (uint32_t)cap;
    /* Zero-init items */
    for (int64_t i = 0; i < cap; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

/* rt_array_push: push a value onto the array, growing if needed */
RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    /* Grow if needed */
    if (a->len >= a->cap) {
        uint32_t new_cap = a->cap * 2;
        if (new_cap < 8) new_cap = 8;
        size_t new_size = sizeof(RuntimeArray) + (size_t)new_cap * sizeof(RuntimeValue);
        RuntimeArray *na = (RuntimeArray *)malloc(new_size);
        if (!na) return NIL_VALUE;
        /* Copy header and existing items */
        na->hdr.type = HEAP_ARRAY;
        na->hdr.size = (uint32_t)new_size;
        na->len = a->len;
        na->cap = new_cap;
        for (uint32_t i = 0; i < a->len; i++) na->items[i] = a->items[i];
        /* Zero new slots */
        for (uint32_t i = a->len; i < new_cap; i++) na->items[i] = NIL_VALUE;
        /* Note: bump allocator can't free old array, but we return the new pointer.
           Callers must use the returned value. This is a limitation of the bump allocator. */
        a = na;
    }
    a->items[a->len] = val;
    a->len++;
    return ENCODE_PTR(a);
}

/* rt_array_pop: remove and return last element */
RuntimeValue rt_array_pop(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return NIL_VALUE;
    a->len--;
    RuntimeValue val = a->items[a->len];
    a->items[a->len] = NIL_VALUE;
    return val;
}

/* rt_array_get: get element at index */
RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    return a->items[i];
}

/* rt_array_set: set element at index */
RuntimeValue rt_array_set(RuntimeValue arr, RuntimeValue idx, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    a->items[i] = val;
    return val;
}

/* rt_array_len: return array length */
RuntimeValue rt_array_len(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return ENCODE_INT(0);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(0);
    return ENCODE_INT(a->len);
}
/* rt_array_slice(arr, start, end) — return sub-array */
RuntimeValue rt_array_slice(RuntimeValue arr, RuntimeValue start, RuntimeValue end)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t s = DECODE_INT(start);
    int64_t e = DECODE_INT(end);
    if (s < 0) s = 0;
    if (e > (int64_t)a->len) e = (int64_t)a->len;
    if (s >= e) return rt_array_new(ENCODE_INT(1));
    RuntimeValue result = rt_array_new(ENCODE_INT(e - s));
    for (int64_t i = s; i < e; i++) {
        result = rt_array_push(result, a->items[i]);
    }
    return result;
}

/* rt_array_contains(arr, val) — linear scan for match */
RuntimeValue rt_array_contains(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return 0;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return 0;
    for (uint32_t i = 0; i < a->len; i++) {
        if (rt_native_eq(a->items[i], val)) return 1;
    }
    return 0;
}

/* rt_array_index_of(arr, val) — return first index or -1 */
RuntimeValue rt_array_index_of(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return ENCODE_INT(-1);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (uint32_t i = 0; i < a->len; i++) {
        if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i);
    }
    return ENCODE_INT(-1);
}

/* rt_array_last_index_of(arr, val) */
RuntimeValue rt_array_last_index_of(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return ENCODE_INT(-1);
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return ENCODE_INT(-1);
    for (int64_t i = (int64_t)a->len - 1; i >= 0; i--) {
        if (rt_native_eq(a->items[i], val)) return ENCODE_INT(i);
    }
    return ENCODE_INT(-1);
}

/* rt_array_remove(arr, idx) — remove at index, shift down */
RuntimeValue rt_array_remove(RuntimeValue arr, RuntimeValue idx)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    int64_t i = DECODE_INT(idx);
    if (i < 0 || (uint32_t)i >= a->len) return NIL_VALUE;
    RuntimeValue removed = a->items[i];
    for (uint32_t j = (uint32_t)i; j + 1 < a->len; j++) {
        a->items[j] = a->items[j + 1];
    }
    a->len--;
    a->items[a->len] = NIL_VALUE;
    return removed;
}

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

/* rt_array_join(arr, sep) — join string array with separator */
RuntimeValue rt_array_join(RuntimeValue arr, RuntimeValue sep)
{
    if (!IS_HEAP(arr)) return rt_string_from_cstr("");
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0)
        return rt_string_from_cstr("");
    RuntimeValue result = rt_value_to_string(a->items[0]);
    for (uint32_t i = 1; i < a->len; i++) {
        if (IS_HEAP(sep)) result = rt_string_concat(result, sep);
        result = rt_string_concat(result, rt_value_to_string(a->items[i]));
    }
    return result;
}

/* rt_array_concat(arr_a, arr_b) */
RuntimeValue rt_array_concat(RuntimeValue arr_a, RuntimeValue arr_b)
{
    RuntimeArray *a = IS_HEAP(arr_a) ? (RuntimeArray *)DECODE_PTR(arr_a) : (RuntimeArray *)0;
    RuntimeArray *b = IS_HEAP(arr_b) ? (RuntimeArray *)DECODE_PTR(arr_b) : (RuntimeArray *)0;
    uint32_t la = (a && a->hdr.type == HEAP_ARRAY) ? a->len : 0;
    uint32_t lb = (b && b->hdr.type == HEAP_ARRAY) ? b->len : 0;
    RuntimeValue result = rt_array_new(ENCODE_INT(la + lb > 0 ? la + lb : 1));
    for (uint32_t i = 0; i < la; i++) result = rt_array_push(result, a->items[i]);
    for (uint32_t i = 0; i < lb; i++) result = rt_array_push(result, b->items[i]);
    return result;
}

/* rt_array_clear(arr) */
RuntimeValue rt_array_clear(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return arr;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return arr;
    for (uint32_t i = 0; i < a->len; i++) a->items[i] = NIL_VALUE;
    a->len = 0;
    return arr;
}

S1(rt_array_flatten)
S2(rt_array_fill)

/* rt_array_clone(arr) — shallow copy */
RuntimeValue rt_array_clone(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    RuntimeValue result = rt_array_new(ENCODE_INT(a->cap));
    for (uint32_t i = 0; i < a->len; i++) {
        result = rt_array_push(result, a->items[i]);
    }
    return result;
}

S2(rt_array_zip)
S1(rt_array_uniq)
S1(rt_array_compact)

/* --- Map / Dictionary ---
 *
 * RuntimeMap: linear-probe map with separate key/value arrays.
 * Keys are RuntimeValues compared via rt_native_eq (works for ints
 * and strings).  Suitable for small maps (VFS mount table, IPC
 * service registry) on bare metal.
 *
 * RuntimeMap typedef is in section 3 (forward-declared for rt_len).
 */

static RuntimeMap *decode_map(RuntimeValue v)
{
    if (!IS_HEAP(v)) return (RuntimeMap *)0;
    RuntimeMap *m = (RuntimeMap *)DECODE_PTR(v);
    if (!m || m->hdr.type != HEAP_MAP) return (RuntimeMap *)0;
    return m;
}

/* rt_map_new: create map.  Ignores argument (raw ABI); uses default cap 16. */
RuntimeValue rt_map_new(void)
{
    uint32_t cap = 16;
    RuntimeMap *m = (RuntimeMap *)malloc(sizeof(RuntimeMap));
    if (!m) return NIL_VALUE;
    m->hdr.type = HEAP_MAP;
    m->hdr.size = (uint32_t)sizeof(RuntimeMap);
    m->len = 0;
    m->cap = cap;
    m->keys   = (RuntimeValue *)malloc(cap * sizeof(RuntimeValue));
    m->values = (RuntimeValue *)malloc(cap * sizeof(RuntimeValue));
    if (!m->keys || !m->values) return NIL_VALUE;
    for (uint32_t i = 0; i < cap; i++) {
        m->keys[i]   = NIL_VALUE;
        m->values[i] = NIL_VALUE;
    }
    return ENCODE_PTR(m);
}

/* Linear scan for key; returns index or -1 */
static int32_t map_find_key(RuntimeMap *m, RuntimeValue key)
{
    for (uint32_t i = 0; i < m->len; i++) {
        if (rt_native_eq(m->keys[i], key)) return (int32_t)i;
    }
    return -1;
}

/* Grow the map arrays when full */
static void map_grow(RuntimeMap *m)
{
    uint32_t new_cap = m->cap * 2;
    if (new_cap < 16) new_cap = 16;
    RuntimeValue *nk = (RuntimeValue *)malloc(new_cap * sizeof(RuntimeValue));
    RuntimeValue *nv = (RuntimeValue *)malloc(new_cap * sizeof(RuntimeValue));
    if (!nk || !nv) return; /* OOM: silently fail on bare metal */
    for (uint32_t i = 0; i < m->len; i++) {
        nk[i] = m->keys[i];
        nv[i] = m->values[i];
    }
    for (uint32_t i = m->len; i < new_cap; i++) {
        nk[i] = NIL_VALUE;
        nv[i] = NIL_VALUE;
    }
    /* Bump allocator: old arrays leak but that is acceptable on bare metal */
    m->keys   = nk;
    m->values = nv;
    m->cap    = new_cap;
}

/* rt_map_set(map, key, value) — insert or update */
RuntimeValue rt_map_set(RuntimeValue map, RuntimeValue key, RuntimeValue value)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key);
    if (idx >= 0) {
        m->values[idx] = value;
        return map; /* return same map pointer */
    }
    /* Insert new entry */
    if (m->len >= m->cap) map_grow(m);
    if (m->len >= m->cap) return map; /* grow failed */
    m->keys[m->len]   = key;
    m->values[m->len]  = value;
    m->len++;
    return map;
}

/* rt_map_get(map, key) — return value or NIL_VALUE */
RuntimeValue rt_map_get(RuntimeValue map, RuntimeValue key)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key);
    if (idx >= 0) return m->values[idx];
    return NIL_VALUE;
}

/* rt_map_has(map, key) — return 1 or 0 (raw i64) */
RuntimeValue rt_map_has(RuntimeValue map, RuntimeValue key)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return 0;
    return map_find_key(m, key) >= 0 ? 1 : 0;
}

/* rt_map_remove(map, key) — remove entry, return removed value */
RuntimeValue rt_map_remove(RuntimeValue map, RuntimeValue key)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    int32_t idx = map_find_key(m, key);
    if (idx < 0) return NIL_VALUE;
    RuntimeValue removed = m->values[idx];
    /* Shift remaining entries down */
    for (uint32_t i = (uint32_t)idx; i + 1 < m->len; i++) {
        m->keys[i]   = m->keys[i + 1];
        m->values[i] = m->values[i + 1];
    }
    m->len--;
    m->keys[m->len]   = NIL_VALUE;
    m->values[m->len]  = NIL_VALUE;
    return removed;
}

/* rt_map_keys(map) — return array of keys */
RuntimeValue rt_map_keys(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) {
        arr = rt_array_push(arr, m->keys[i]);
    }
    return arr;
}

/* rt_map_values(map) — return array of values */
RuntimeValue rt_map_values(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) {
        arr = rt_array_push(arr, m->values[i]);
    }
    return arr;
}

/* rt_map_entries(map) — return array of [key, value] pairs (as 2-element arrays) */
RuntimeValue rt_map_entries(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    RuntimeValue arr = rt_array_new(ENCODE_INT(m->len > 0 ? m->len : 1));
    for (uint32_t i = 0; i < m->len; i++) {
        RuntimeValue pair = rt_array_new(ENCODE_INT(2));
        pair = rt_array_push(pair, m->keys[i]);
        pair = rt_array_push(pair, m->values[i]);
        arr = rt_array_push(arr, pair);
    }
    return arr;
}

/* rt_map_len(map) — return entry count */
RuntimeValue rt_map_len(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return ENCODE_INT(0);
    return ENCODE_INT(m->len);
}

/* rt_map_clear(map) — remove all entries */
RuntimeValue rt_map_clear(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    for (uint32_t i = 0; i < m->len; i++) {
        m->keys[i]   = NIL_VALUE;
        m->values[i] = NIL_VALUE;
    }
    m->len = 0;
    return map;
}

/* rt_map_clone(map) — shallow copy */
RuntimeValue rt_map_clone(RuntimeValue map)
{
    RuntimeMap *m = decode_map(map);
    if (!m) return NIL_VALUE;
    RuntimeValue new_map = rt_map_new();
    RuntimeMap *nm = decode_map(new_map);
    if (!nm) return NIL_VALUE;
    for (uint32_t i = 0; i < m->len; i++) {
        rt_map_set(new_map, m->keys[i], m->values[i]);
    }
    return new_map;
}

/* rt_map_merge(map_a, map_b) — merge b into a copy of a */
RuntimeValue rt_map_merge(RuntimeValue map_a, RuntimeValue map_b)
{
    RuntimeValue result = rt_map_clone(map_a);
    RuntimeMap *mb = decode_map(map_b);
    if (!mb) return result;
    for (uint32_t i = 0; i < mb->len; i++) {
        result = rt_map_set(result, mb->keys[i], mb->values[i]);
    }
    return result;
}

/* rt_map_for_each(map, callback) — no-op on bare metal (closures not callable from C) */
RuntimeValue rt_map_for_each(RuntimeValue map, RuntimeValue callback)
{
    (void)map; (void)callback;
    return NIL_VALUE;
}

/* ---- Trap stubs: these should NEVER silently return 0 on baremetal ----
 * Instead of masking failures, print the function name and halt.
 * This makes it immediately obvious when kernel code accidentally
 * uses a hosted-only API path.
 */
#define TRAP_STUB_RET(n, nargs) \
    RuntimeValue n(TRAP_ARGS_##nargs) { \
        TRAP_SUPPRESS_##nargs \
        serial_puts("[TRAP] " #n " called on baremetal -- halting\r\n"); \
        for (;;) { __asm__ volatile("hlt"); } \
        return 0; \
    }
#define TRAP_STUB_VOID(n, nargs) \
    void n(TRAP_ARGS_##nargs) { \
        TRAP_SUPPRESS_##nargs \
        serial_puts("[TRAP] " #n " called on baremetal -- halting\r\n"); \
        for (;;) { __asm__ volatile("hlt"); } \
    }
#define TRAP_ARGS_0   void
#define TRAP_ARGS_1   RuntimeValue _a
#define TRAP_ARGS_2   RuntimeValue _a, RuntimeValue _b
#define TRAP_ARGS_3   RuntimeValue _a, RuntimeValue _b, RuntimeValue _c
#define TRAP_SUPPRESS_0
#define TRAP_SUPPRESS_1  (void)_a;
#define TRAP_SUPPRESS_2  (void)_a; (void)_b;
#define TRAP_SUPPRESS_3  (void)_a; (void)_b; (void)_c;

/* --- File I/O (no filesystem on baremetal) --- */
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

/* --- Directory I/O (no filesystem on baremetal) --- */
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

/* --- Process (no OS on baremetal) --- */
TRAP_STUB_RET(rt_process_run, 2)
TRAP_STUB_RET(rt_process_run_timeout, 3)
TRAP_STUB_RET(rt_process_spawn, 1)
TRAP_STUB_RET(rt_process_kill, 1)
TRAP_STUB_RET(rt_process_wait, 1)
TRAP_STUB_RET(rt_process_pid, 0)
TRAP_STUB_RET(rt_cli_get_args, 1)
TRAP_STUB_RET(rt_cli_args, 0)
TRAP_STUB_RET(rt_exit_code, 0)
TRAP_STUB_RET(rt_exit, 1)
TRAP_STUB_RET(rt_env_get, 1)
TRAP_STUB_RET(rt_env_set, 2)
TRAP_STUB_RET(rt_env_all, 0)

/* --- Math --- */
S1(rt_math_sqrt)
S1(rt_math_sin)
S1(rt_math_cos)
S1(rt_math_tan)
S1(rt_math_asin)
S1(rt_math_acos)
S1(rt_math_atan)
S2(rt_math_atan2)
S1(rt_math_abs)
S1(rt_math_floor)
S1(rt_math_ceil)
S1(rt_math_round)
S1(rt_math_log)
S1(rt_math_log2)
S1(rt_math_log10)
S1(rt_math_exp)
S2(rt_math_min)
S2(rt_math_max)
S2(rt_math_pow)
S0(rt_math_random)
S0(rt_math_pi)
S0(rt_math_e)
S0(rt_math_inf)
S0(rt_math_nan)
S1(rt_math_is_nan)
S1(rt_math_is_inf)

/* MMIO, CPU control, and interrupt stubs are provided as real
   implementations in Section 11 below — not generated via S* macros. */
S2(rt_register_isr)
S1(rt_send_eoi)
S0(rt_get_interrupt_flag)

/* --- Timer / Clock --- */
S1(rt_time_now_ms)
S0(rt_time_now_nanos)
S0(rt_time_monotonic)
S1(rt_sleep_ms)
S1(rt_timer_create)
S1(rt_timer_cancel)

/* --- Network (no network stack on baremetal) --- */
TRAP_STUB_RET(rt_net_connect, 2)
TRAP_STUB_RET(rt_net_listen, 1)
TRAP_STUB_RET(rt_net_send, 2)
TRAP_STUB_RET(rt_net_recv, 1)
TRAP_STUB_RET(rt_net_close, 1)
TRAP_STUB_RET(rt_net_bind, 2)
TRAP_STUB_RET(rt_net_accept, 1)
TRAP_STUB_RET(rt_net_set_timeout, 2)
TRAP_STUB_RET(rt_net_get_addr, 1)

/* --- HTTP (no network stack on baremetal) --- */
TRAP_STUB_RET(rt_http_get, 2)
TRAP_STUB_RET(rt_http_post, 3)
TRAP_STUB_RET(rt_http_put, 3)
TRAP_STUB_RET(rt_http_patch, 3)
TRAP_STUB_RET(rt_http_delete, 2)
TRAP_STUB_RET(rt_http_request, 2)
TRAP_STUB_RET(rt_http_request_full, 3)
TRAP_STUB_RET(rt_http_set_header, 2)

/* --- JSON --- */
S1(rt_json_parse)
S1(rt_json_stringify)
S2(rt_json_get)
S3(rt_json_set)
S1(rt_json_keys)
S1(rt_json_values)
S1(rt_json_is_object)
S1(rt_json_is_array)

/* --- Regex --- */
S2(ffi_regex_is_match)
S2(ffi_regex_find)
S2(ffi_regex_find_all)
S2(ffi_regex_replace)
S3(ffi_regex_replace_all)
S1(ffi_regex_compile)

/* --- Test / BDD --- */
S1(rt_bdd_describe_start)
S1(rt_bdd_describe_end)
S2(rt_bdd_it_start)
S1(rt_bdd_it_end)
S1(rt_expect)
S2(rt_expect_eq)
S2(rt_expect_ne)
S2(rt_expect_gt)
S2(rt_expect_lt)
S1(rt_expect_nil)
S1(rt_expect_not_nil)
S1(rt_expect_true)
S1(rt_expect_false)
S2(rt_expect_contains)
S2(rt_expect_throws)
S0(rt_bdd_suite_start)
S0(rt_bdd_suite_end)
S0(rt_bdd_report)

/* --- Misc / Debug --- */

/* rt_hash: FNV-1a-like hash for integers and strings */
RuntimeValue rt_hash(RuntimeValue val)
{
    uint64_t h = 14695981039346656037ULL; /* FNV offset basis */
    if (IS_INT(val)) {
        int64_t n = DECODE_INT(val);
        for (int i = 0; i < 8; i++) {
            h ^= (uint8_t)(n & 0xFF);
            h *= 1099511628211ULL; /* FNV prime */
            n >>= 8;
        }
    } else if (IS_HEAP(val)) {
        HeapHeader *hdr = (HeapHeader *)DECODE_PTR(val);
        if (hdr && hdr->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)hdr;
            for (uint32_t i = 0; i < s->len; i++) {
                h ^= (uint8_t)s->data[i];
                h *= 1099511628211ULL;
            }
        } else {
            /* Hash by pointer address */
            uint64_t p = (uint64_t)(uintptr_t)hdr;
            for (int i = 0; i < 8; i++) {
                h ^= (uint8_t)(p & 0xFF);
                h *= 1099511628211ULL;
                p >>= 8;
            }
        }
    }
    return ENCODE_INT((int64_t)(h >> 3)); /* Ensure tag bits are clear */
}

RuntimeValue rt_hash_combine(RuntimeValue h1, RuntimeValue h2)
{
    /* Boost-style hash combine */
    int64_t a = DECODE_INT(h1);
    int64_t b = DECODE_INT(h2);
    uint64_t combined = (uint64_t)a ^ ((uint64_t)b + 0x9e3779b97f4a7c15ULL
                         + ((uint64_t)a << 6) + ((uint64_t)a >> 2));
    return ENCODE_INT((int64_t)(combined >> 3));
}

RuntimeValue rt_debug_print(RuntimeValue val)
{
    serial_puts("[DEBUG] ");
    rt_print_value(val);
    serial_putchar('\r');
    serial_putchar('\n');
    return NIL_VALUE;
}

RuntimeValue rt_debug_dump(RuntimeValue val)
{
    serial_puts("[DUMP] raw=");
    serial_put_hex((uint64_t)val);
    serial_puts(" tag=");
    serial_put_dec((int64_t)((uint64_t)val & TAG_MASK));
    if (IS_INT(val)) {
        serial_puts(" int=");
        serial_put_dec(DECODE_INT(val));
    } else if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        serial_puts(" heap_type=");
        serial_put_dec(h ? (int64_t)h->type : -1);
    }
    serial_putchar('\r');
    serial_putchar('\n');
    return NIL_VALUE;
}

RuntimeValue rt_debug_break(void)
{
    serial_puts("[BREAK] debug break\r\n");
    return NIL_VALUE;
}

RuntimeValue rt_panic(RuntimeValue msg)
{
    serial_puts("[PANIC] ");
    if (IS_HEAP(msg)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(msg);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            for (uint32_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
        } else {
            serial_puts("<non-string>");
        }
    } else {
        serial_put_hex((uint64_t)msg);
    }
    serial_puts("\r\n");
    /* Halt the system */
    for (;;) __asm__ volatile("hlt");
    return NIL_VALUE; /* unreachable */
}

RuntimeValue rt_assert(RuntimeValue cond)
{
    if (IS_INT(cond) && DECODE_INT(cond)) return NIL_VALUE; /* truthy */
    if (IS_HEAP(cond)) return NIL_VALUE; /* non-nil heap is truthy */
    /* Assertion failed */
    serial_puts("[ASSERT] assertion failed\r\n");
    for (;;) __asm__ volatile("hlt");
    return NIL_VALUE;
}

RuntimeValue rt_assert_eq(RuntimeValue a, RuntimeValue b)
{
    if (rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_EQ] ");
    rt_print_value(a);
    serial_puts(" != ");
    rt_print_value(b);
    serial_puts("\r\n");
    for (;;) __asm__ volatile("hlt");
    return NIL_VALUE;
}

RuntimeValue rt_assert_ne(RuntimeValue a, RuntimeValue b)
{
    if (!rt_native_eq(a, b)) return NIL_VALUE;
    serial_puts("[ASSERT_NE] values are equal: ");
    rt_print_value(a);
    serial_puts("\r\n");
    for (;;) __asm__ volatile("hlt");
    return NIL_VALUE;
}

RuntimeValue rt_abort(RuntimeValue msg)
{
    serial_puts("[ABORT] ");
    rt_print_value(msg);
    serial_puts("\r\n");
    for (;;) __asm__ volatile("hlt");
    return NIL_VALUE;
}

/* GC: safe no-ops on bare metal (bump allocator, no GC) */
RuntimeValue rt_gc_collect(void) { return NIL_VALUE; }
RuntimeValue rt_gc_disable(void) { return NIL_VALUE; }
RuntimeValue rt_gc_enable(void)  { return NIL_VALUE; }
RuntimeValue rt_gc_stats(void)   { return NIL_VALUE; }

/* rt_typeof already implemented above in type introspection section */

/* --- Threading (no scheduler on bare metal) --- */
TRAP_STUB_RET(rt_thread_create, 1)
TRAP_STUB_RET(rt_thread_join, 1)
/* Safe no-ops on single-threaded bare metal */
RuntimeValue rt_thread_yield(void)          { return NIL_VALUE; }  /* yield: no-op */
RuntimeValue rt_thread_current(void)        { return ENCODE_INT(0); }  /* thread ID 0 */
RuntimeValue rt_thread_sleep(RuntimeValue a) { (void)a; return NIL_VALUE; }  /* sleep: return immediately */
TRAP_STUB_RET(rt_mutex_new, 0)
TRAP_STUB_RET(rt_mutex_lock, 1)
TRAP_STUB_RET(rt_mutex_unlock, 1)
TRAP_STUB_RET(rt_mutex_try_lock, 1)
TRAP_STUB_RET(rt_condvar_new, 0)
TRAP_STUB_RET(rt_condvar_wait, 1)
TRAP_STUB_RET(rt_condvar_notify, 1)
TRAP_STUB_RET(rt_condvar_notify_all, 1)

/* --- Channels (no IPC on bare metal) --- */
TRAP_STUB_RET(rt_channel_new, 0)
TRAP_STUB_RET(rt_channel_send, 2)
TRAP_STUB_RET(rt_channel_recv, 1)
TRAP_STUB_RET(rt_channel_try_recv, 1)
TRAP_STUB_RET(rt_channel_close, 1)

/* --- Async (no async runtime on bare metal) --- */
TRAP_STUB_RET(rt_async_spawn, 1)
TRAP_STUB_RET(rt_async_await, 1)
/* Safe no-op on single-threaded bare metal */
RuntimeValue rt_async_yield(void) { return NIL_VALUE; }
TRAP_STUB_RET(rt_async_select, 2)

/* --- Encoding --- */
S1(rt_base64_encode)
S1(rt_base64_decode)
S1(rt_hex_encode)
S1(rt_hex_decode)
S1(rt_utf8_encode)
S1(rt_utf8_decode)
S1(rt_url_encode)
S1(rt_url_decode)

/* --- Crypto (no-ops on bare metal) --- */
S1(rt_sha256)
S1(rt_sha512)
S1(rt_md5)
S2(rt_hmac_sha256)
S1(rt_random_bytes)

/* --- Object / Struct --- */
S1(rt_object_new)
S2(rt_object_get)
S3(rt_object_set)
S2(rt_object_has)
S2(rt_object_delete)
S1(rt_object_keys)
S1(rt_object_values)
S1(rt_object_freeze)
S1(rt_object_clone)

/* --- Error handling --- */
S1(rt_error_new)
S1(rt_error_message)
S1(rt_error_code)
S1(rt_error_stack)
S2(rt_result_ok)
S2(rt_result_err)
S1(rt_result_is_ok)
S1(rt_result_is_err)
S1(rt_result_unwrap)
S2(rt_result_unwrap_or)

/* --- Weak references & closures --- */
S1(rt_weak_ref)
S1(rt_weak_deref)
S1(rt_closure_new)
S2(rt_closure_call)
S1(rt_closure_bind)

/* ===================================================================
 * 11. Real x86_64 port-I/O, MMIO, and CPU overrides
 *
 * These provide actual hardware access for x86_64-specific operations.
 * We define _real_ suffixed functions and then use them via linker
 * wrappers or direct calls.  In a single translation unit the last
 * definition of a symbol wins, but we use _real suffix + alias to
 * be explicit and avoid redefinition warnings.
 * =================================================================== */

#if defined(__x86_64__) || defined(__i386__)
/* --- Port I/O: real x86 implementations --- */

/* Port I/O and MMIO: Cranelift passes RAW (untagged) integer values
 * to extern fns. Return RAW values too. No ENCODE/DECODE needed. */

RuntimeValue rt_port_outb_real(RuntimeValue port, RuntimeValue val)
{
    outb((uint16_t)(uint64_t)port, (uint8_t)(uint64_t)val);
    return 0;
}

RuntimeValue rt_port_outw_real(RuntimeValue port, RuntimeValue val)
{
    outw((uint16_t)(uint64_t)port, (uint16_t)(uint64_t)val);
    return 0;
}

RuntimeValue rt_port_outl_real(RuntimeValue port, RuntimeValue val)
{
    outl((uint16_t)(uint64_t)port, (uint32_t)(uint64_t)val);
    return 0;
}

RuntimeValue rt_port_inb_real(RuntimeValue port)
{
    return (RuntimeValue)(uint64_t)inb((uint16_t)(uint64_t)port);
}

RuntimeValue rt_port_inw_real(RuntimeValue port)
{
    return (RuntimeValue)(uint64_t)inw((uint16_t)(uint64_t)port);
}

RuntimeValue rt_port_inl_real(RuntimeValue port)
{
    return (RuntimeValue)(uint64_t)inl((uint16_t)(uint64_t)port);
}

RuntimeValue rt_port_io_wait_real(void)
{
    io_wait();
    return 0;
}

/* Expose as the primary symbols (linker sees these).
 * Use inline wrappers instead of __attribute__((alias)) for Mach-O compat. */
RuntimeValue rt_port_outb(RuntimeValue port, RuntimeValue val) {
    return rt_port_outb_real(port, val);
}
RuntimeValue rt_port_outw(RuntimeValue port, RuntimeValue val) {
    return rt_port_outw_real(port, val);
}
RuntimeValue rt_port_outl(RuntimeValue port, RuntimeValue val) {
    return rt_port_outl_real(port, val);
}
RuntimeValue rt_port_inb(RuntimeValue port) {
    return rt_port_inb_real(port);
}
RuntimeValue rt_port_inw(RuntimeValue port) {
    return rt_port_inw_real(port);
}
RuntimeValue rt_port_inl(RuntimeValue port) {
    return rt_port_inl_real(port);
}
RuntimeValue rt_port_io_wait(void) {
    return rt_port_io_wait_real();
}

/* --- MMIO: real x86_64 implementations --- */

RuntimeValue rt_mmio_read_u8_real(RuntimeValue addr)
{
    return (RuntimeValue)(uint64_t)*(volatile uint8_t *)(uintptr_t)(uint64_t)addr;
}

RuntimeValue rt_mmio_read_u16_real(RuntimeValue addr)
{
    return (RuntimeValue)(uint64_t)*(volatile uint16_t *)(uintptr_t)(uint64_t)addr;
}

RuntimeValue rt_mmio_read_u32_real(RuntimeValue addr)
{
    return (RuntimeValue)(uint64_t)*(volatile uint32_t *)(uintptr_t)(uint64_t)addr;
}

RuntimeValue rt_mmio_read_u64_real(RuntimeValue addr)
{
    return (RuntimeValue)*(volatile uint64_t *)(uintptr_t)(uint64_t)addr;
}

RuntimeValue rt_mmio_write_u8_real(RuntimeValue addr, RuntimeValue val)
{
    *(volatile uint8_t *)(uintptr_t)(uint64_t)addr = (uint8_t)(uint64_t)val;
    return 0;
}

RuntimeValue rt_mmio_write_u16_real(RuntimeValue addr, RuntimeValue val)
{
    *(volatile uint16_t *)(uintptr_t)(uint64_t)addr = (uint16_t)(uint64_t)val;
    return 0;
}

RuntimeValue rt_mmio_write_u32_real(RuntimeValue addr, RuntimeValue val)
{
    *(volatile uint32_t *)(uintptr_t)(uint64_t)addr = (uint32_t)(uint64_t)val;
    return 0;
}

RuntimeValue rt_mmio_write_u64_real(RuntimeValue addr, RuntimeValue val)
{
    *(volatile uint64_t *)(uintptr_t)(uint64_t)addr = (uint64_t)val;
    return 0;
}

RuntimeValue rt_mmio_read_u8(RuntimeValue a) { return rt_mmio_read_u8_real(a); }
RuntimeValue rt_mmio_read_u16(RuntimeValue a) { return rt_mmio_read_u16_real(a); }
RuntimeValue rt_mmio_read_u32(RuntimeValue a) { return rt_mmio_read_u32_real(a); }
RuntimeValue rt_mmio_read_u64(RuntimeValue a) { return rt_mmio_read_u64_real(a); }
RuntimeValue rt_mmio_write_u8(RuntimeValue a, RuntimeValue v) { return rt_mmio_write_u8_real(a, v); }
RuntimeValue rt_mmio_write_u16(RuntimeValue a, RuntimeValue v) { return rt_mmio_write_u16_real(a, v); }
RuntimeValue rt_mmio_write_u32(RuntimeValue a, RuntimeValue v) { return rt_mmio_write_u32_real(a, v); }
RuntimeValue rt_mmio_write_u64(RuntimeValue a, RuntimeValue v) { return rt_mmio_write_u64_real(a, v); }

/* --- CPU: real x86_64 implementations --- */

RuntimeValue rt_hlt_real(void)
{
    __asm__ volatile("hlt");
    return NIL_VALUE;
}

RuntimeValue rt_sti_real(void)
{
    __asm__ volatile("sti");
    return NIL_VALUE;
}

RuntimeValue rt_cli_real(void)
{
    __asm__ volatile("cli");
    return NIL_VALUE;
}

RuntimeValue rt_enable_interrupts_real(void)
{
    __asm__ volatile("sti");
    return NIL_VALUE;
}

RuntimeValue rt_disable_interrupts_real(void)
{
    __asm__ volatile("cli");
    return NIL_VALUE;
}

RuntimeValue rt_invlpg_real(RuntimeValue addr)
{
    __asm__ volatile("invlpg (%0)" : : "r"((uintptr_t)DECODE_INT(addr)) : "memory");
    return NIL_VALUE;
}

RuntimeValue rt_rdtsc_real(void)
{
    uint32_t lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return ENCODE_INT((int64_t)(((uint64_t)hi << 32) | lo));
}

RuntimeValue rt_lgdt_real(RuntimeValue desc)
{
    __asm__ volatile("lgdt (%0)" : : "r"((uintptr_t)DECODE_INT(desc)) : "memory");
    return NIL_VALUE;
}

RuntimeValue rt_lidt_real(RuntimeValue desc)
{
    __asm__ volatile("lidt (%0)" : : "r"((uintptr_t)DECODE_INT(desc)) : "memory");
    return NIL_VALUE;
}

RuntimeValue rt_ltr_real(RuntimeValue sel)
{
    uint16_t selector = (uint16_t)DECODE_INT(sel);
    __asm__ volatile("ltr %0" : : "r"(selector));
    return NIL_VALUE;
}

RuntimeValue rt_read_cr3_real(RuntimeValue dummy)
{
    (void)dummy;
    uint64_t cr3;
    __asm__ volatile("mov %%cr3, %0" : "=r"(cr3));
    return ENCODE_INT((int64_t)cr3);
}

RuntimeValue rt_write_cr3_real(RuntimeValue val)
{
    __asm__ volatile("mov %0, %%cr3" : : "r"((uint64_t)DECODE_INT(val)) : "memory");
    return NIL_VALUE;
}

RuntimeValue rt_read_cr2_real(RuntimeValue dummy)
{
    (void)dummy;
    uint64_t cr2;
    __asm__ volatile("mov %%cr2, %0" : "=r"(cr2));
    return ENCODE_INT((int64_t)cr2);
}

RuntimeValue rt_hlt(void) { return rt_hlt_real(); }
RuntimeValue rt_sti(void) { return rt_sti_real(); }
RuntimeValue rt_cli(void) { return rt_cli_real(); }
RuntimeValue rt_enable_interrupts(void) { return rt_enable_interrupts_real(); }
RuntimeValue rt_disable_interrupts(void) { return rt_disable_interrupts_real(); }
RuntimeValue rt_invlpg(RuntimeValue a) { return rt_invlpg_real(a); }
RuntimeValue rt_rdtsc(void) { return rt_rdtsc_real(); }
RuntimeValue rt_lgdt(RuntimeValue a) { return rt_lgdt_real(a); }
RuntimeValue rt_lidt(RuntimeValue a) { return rt_lidt_real(a); }
RuntimeValue rt_ltr(RuntimeValue a) { return rt_ltr_real(a); }
RuntimeValue rt_read_cr3(RuntimeValue a) { return rt_read_cr3_real(a); }
RuntimeValue rt_write_cr3(RuntimeValue a) { return rt_write_cr3_real(a); }
RuntimeValue rt_read_cr2(RuntimeValue a) { return rt_read_cr2_real(a); }

#endif /* __x86_64__ || __i386__ */

/* End of x86_64 baremetal_stubs.c */
