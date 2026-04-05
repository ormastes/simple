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
 *  8a. PCI device scan/cache
 *  8b. NVMe controller + sector read
 *  8b-fat32. FAT32 file system driver
 *  8c-net. VirtIO-net driver + ARP/ICMP responder
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

#define HEAP_STRING  1
#define HEAP_ARRAY   2
#define HEAP_MAP     3
#define HEAP_OBJECT  4
#define HEAP_CLOSURE 5
#define HEAP_MODULE  6
#define HEAP_ENUM    7

/* Enum/Optional/Result representation — matches Rust runtime RuntimeEnum.
 * Used by rt_enum_new / rt_enum_discriminant / rt_enum_payload.
 * Total size: 24 bytes (header 8 + enum_id 4 + discriminant 4 + payload 8). */
typedef struct {
    HeapHeader   hdr;
    uint32_t     enum_id;
    uint32_t     discriminant;
    RuntimeValue payload;
} RuntimeEnum;

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

static char   _heap[256 * 1024 * 1024] __attribute__((aligned(16)));
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
    /* compile_struct_init passes RAW size (not tagged): iconst.i64 16
     * Return RAW pointer — codegen uses it directly for store(val, ptr, offset).
     * Other runtime functions that need heap pointers use ENCODE_PTR themselves. */
    size_t bytes = (size_t)sz;
    if (bytes == 0) return 0;
    /* Debug: log allocations of PciDevice-sized (96) or similar struct sizes */
    if (bytes > 0x1000000) bytes = 0x1000000;
    void *p = malloc(bytes);
    if (!p) return 0;
    __builtin_memset(p, 0, bytes);  /* zero to avoid garbage in uninitialized fields */
    return (RuntimeValue)(uintptr_t)p;
}

RuntimeValue rt_alloc_zeroed(RuntimeValue sz)
{
    size_t bytes = (size_t)sz;
    if (bytes == 0) return 0;
    if (bytes > 0x1000000) bytes = 0x1000000;
    void *p = malloc(bytes);
    if (!p) return 0;
    __builtin_memset(p, 0, bytes);
    return (RuntimeValue)(uintptr_t)p;
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
    /* Return ENCODE_INT — callers expect tagged integer */
    if (!IS_HEAP(str)) return ENCODE_INT(0);
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s) return ENCODE_INT(0);
    return ENCODE_INT(s->len);
}

RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx)
{
    /* MIR lowering inserts BoxInt on indices, so idx is tagged. Return raw char. */
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int64_t i = DECODE_INT(idx);
    if (!s || i < 0 || (uint32_t)i >= s->len) return 0;
    return (RuntimeValue)(unsigned char)s->data[i];
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
    /* Return raw 0/1 (Cranelift uses raw convention) */
    if (!IS_HEAP(a) || !IS_HEAP(b)) return (RuntimeValue)(a == b ? 1 : 0);
    RuntimeString *sa = (RuntimeString *)DECODE_PTR(a);
    RuntimeString *sb = (RuntimeString *)DECODE_PTR(b);
    if (!sa || !sb) return 0;
    if (sa->len != sb->len) return 0;
    for (uint32_t i = 0; i < sa->len; i++) {
        if (sa->data[i] != sb->data[i]) return 0;
    }
    return 1;
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

/* --- rt_value_to_string: convert any RuntimeValue to a string RuntimeValue ---
 *
 * Handles both tagged (BoxInt: val << 3) and raw integer values.
 * The Cranelift codegen uses raw integers internally, but inserts BoxInt
 * before calling this function for f-string interpolation. Cross-module
 * return values may arrive without BoxInt (raw). We handle both cases.
 */
static RuntimeValue _int_to_string(int64_t n)
{
    if (n == 0) return rt_string_from_cstr("0");
    if (n == (-9223372036854775807LL - 1))
        return rt_string_from_cstr("-9223372036854775808");
    char buf[21];
    int pos = 0, neg = 0;
    uint64_t uv;
    if (n < 0) { neg = 1; uv = (uint64_t)(-n); } else { uv = (uint64_t)n; }
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

RuntimeValue rt_value_to_string(RuntimeValue val)
{
    /* 1. Tagged integer (BoxInt: low 3 bits = 0, TAG_INT) */
    if (IS_INT(val)) {
        return _int_to_string(DECODE_INT(val));
    }
    /* 2. Heap object (string, array, map) */
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) return val;
        if (h && h->type == HEAP_ARRAY) return rt_string_from_cstr("<array>");
        if (h && h->type == HEAP_MAP) return rt_string_from_cstr("<map>");
        return rt_string_from_cstr("<object>");
    }
    /* 3. nil (0x3) */
    if (val == NIL_VALUE) return rt_string_from_cstr("nil");
    /* 4. Everything else: treat as raw integer (cross-module return without BoxInt) */
    return _int_to_string((int64_t)val);
}

RuntimeValue rt_len(RuntimeValue v)
{
    /* Return ENCODE_INT — callers expect tagged integer */
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
        /* MIR lowering inserts BoxInt on indices (lowering_stmt.rs:866),
         * so idx arrives tagged (value << 3). DECODE_INT to get raw index. */
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
 * 8a-pci. PCI device cache + scan (moved here for NVMe forward ref)
 *
 * Originally in the syscall 80 section; hoisted so the NVMe C driver
 * can reference _pci_cache[] and _pci_scan() directly.
 * =================================================================== */

#define MAX_PCI_CACHED 64
static struct {
    uint8_t bus, dev, func;
    uint16_t vendor, devid;
    uint8_t cls, sub, progif, htype, irq;
} _pci_cache[MAX_PCI_CACHED];
static int _pci_cache_count = -1; /* -1 = not scanned yet */

static void _pci_scan(void)
{
    _pci_cache_count = 0;
    for (int bus = 0; bus < 256 && _pci_cache_count < MAX_PCI_CACHED; bus++) {
        for (int dev = 0; dev < 32 && _pci_cache_count < MAX_PCI_CACHED; dev++) {
            /* Read vendor ID at bus:dev.0 */
            uint32_t addr = 0x80000000 | ((uint32_t)bus << 16) | ((uint32_t)dev << 11);
            outl(0xCF8, addr);
            uint32_t reg0 = inl(0xCFC);
            uint16_t vendor = (uint16_t)(reg0 & 0xFFFF);
            if (vendor == 0xFFFF || vendor == 0) continue;

            uint16_t devid = (uint16_t)(reg0 >> 16);

            /* Read class/subclass/prog_if at offset 0x08 */
            outl(0xCF8, addr | 0x08);
            uint32_t reg2 = inl(0xCFC);
            uint8_t cls = (uint8_t)(reg2 >> 24);
            uint8_t sub = (uint8_t)(reg2 >> 16);
            uint8_t progif = (uint8_t)(reg2 >> 8);

            /* Read header type at offset 0x0C */
            outl(0xCF8, addr | 0x0C);
            uint32_t reg3 = inl(0xCFC);
            uint8_t htype = (uint8_t)(reg3 >> 16);

            /* Read IRQ line at offset 0x3C */
            outl(0xCF8, addr | 0x3C);
            uint32_t regF = inl(0xCFC);
            uint8_t irq = (uint8_t)(regF & 0xFF);

            int i = _pci_cache_count++;
            _pci_cache[i].bus = (uint8_t)bus;
            _pci_cache[i].dev = (uint8_t)dev;
            _pci_cache[i].func = 0;
            _pci_cache[i].vendor = vendor;
            _pci_cache[i].devid = devid;
            _pci_cache[i].cls = cls;
            _pci_cache[i].sub = sub;
            _pci_cache[i].progif = progif;
            _pci_cache[i].htype = htype;
            _pci_cache[i].irq = irq;
        }
    }
}

/* ===================================================================
 * 8b-nvme. NVMe controller init + sector read (pure C, polling)
 *
 * The Simple-compiled NVMe driver calls MMIO read/write via extern fns,
 * but those are auto-stubbed and return 0.  This C implementation does
 * the full NVMe init + sector read directly with volatile pointers.
 * Exposed as syscall 85: NvmeReadSector(device_idx, lba, buf_addr).
 *
 * NVMe register layout (BAR0 offsets):
 *   0x00 CAP     Controller Capabilities (64-bit)
 *   0x08 VS      Version
 *   0x14 CC      Controller Configuration
 *   0x1C CSTS    Controller Status
 *   0x24 AQA     Admin Queue Attributes
 *   0x28 ASQ     Admin SQ Base Address (64-bit)
 *   0x30 ACQ     Admin CQ Base Address (64-bit)
 *   0x1000+      Doorbells
 * =================================================================== */

/* --- MMIO helpers (volatile, raw physical addresses) --- */
#define nvme_rd32(addr) (*(volatile uint32_t *)(uintptr_t)(addr))
#define nvme_wr32(addr, val) (*(volatile uint32_t *)(uintptr_t)(addr) = (val))
#define nvme_rd64(addr) (*(volatile uint64_t *)(uintptr_t)(addr))
#define nvme_wr64(addr, val) (*(volatile uint64_t *)(uintptr_t)(addr) = (val))

/* NVMe register offsets */
#define NVME_REG_CAP   0x00
#define NVME_REG_VS    0x08
#define NVME_REG_CC    0x14
#define NVME_REG_CSTS  0x1C
#define NVME_REG_AQA   0x24
#define NVME_REG_ASQ   0x28
#define NVME_REG_ACQ   0x30

/* CC bits */
#define NVME_CC_EN        (1u << 0)
#define NVME_CC_CSS_NVM   (0u << 4)
#define NVME_CC_MPS_4K    (0u << 7)
#define NVME_CC_IOSQES_6  (6u << 16)  /* log2(64) = 6 */
#define NVME_CC_IOCQES_4  (4u << 20)  /* log2(16) = 4 */

/* CSTS bits */
#define NVME_CSTS_RDY  (1u << 0)
#define NVME_CSTS_CFS  (1u << 1)

/* Queue sizes */
#define NVME_ADMIN_DEPTH  32
#define NVME_IO_DEPTH     64
#define NVME_SQE_SIZE     64
#define NVME_CQE_SIZE     16

/* NVMe SQE (Submission Queue Entry) — 64 bytes */
struct nvme_sqe {
    uint32_t cdw0;    /* opcode[7:0] | fuse[9:8] | psdt[15:14] | cid[31:16] */
    uint32_t nsid;
    uint64_t rsvd;
    uint64_t mptr;
    uint64_t prp1;
    uint64_t prp2;
    uint32_t cdw10;
    uint32_t cdw11;
    uint32_t cdw12;
    uint32_t cdw13;
    uint32_t cdw14;
    uint32_t cdw15;
};

/* NVMe CQE (Completion Queue Entry) — 16 bytes */
struct nvme_cqe {
    uint32_t dw0;
    uint32_t rsvd;
    uint16_t sq_head;
    uint16_t sq_id;
    uint16_t cid;
    uint16_t status;   /* bit 0 = phase, bits 1-15 = status code */
};

/* NVMe controller state (single device) */
static struct {
    uint64_t bar0;
    uint32_t db_stride;    /* doorbell stride in bytes = 4 << DSTRD */

    /* Admin queue (QID 0) */
    struct nvme_sqe *admin_sq;
    struct nvme_cqe *admin_cq;
    uint16_t admin_sq_tail;
    uint16_t admin_cq_head;
    uint8_t  admin_cq_phase;
    uint16_t admin_cid;

    /* I/O queue (QID 1) */
    struct nvme_sqe *io_sq;
    struct nvme_cqe *io_cq;
    uint16_t io_sq_tail;
    uint16_t io_cq_head;
    uint8_t  io_cq_phase;
    uint16_t io_cid;

    int initialized;
    uint32_t sector_size;
    uint64_t sector_count;
} _nvme;

/* Allocate page-aligned memory from the bump allocator.
 * NVMe requires queue and data buffers to be page-aligned (4KB).
 * We waste up to (alignment-1) bytes of padding to get the alignment. */
static void *nvme_alloc_aligned(size_t size, size_t alignment)
{
    /* Allocate extra space so we can align within it */
    size_t total = size + alignment;
    void *raw = malloc(total);
    if (!raw) return (void *)0;
    /* Align the pointer within the allocated region */
    uintptr_t addr = (uintptr_t)raw;
    uintptr_t aligned = (addr + alignment - 1) & ~(alignment - 1);
    return (void *)aligned;
}

/* Ring a doorbell: SQ tail doorbell = BAR0 + 0x1000 + (2*qid) * stride
 *                  CQ head doorbell = BAR0 + 0x1000 + (2*qid+1) * stride */
static void nvme_ring_sq_doorbell(uint16_t qid, uint16_t tail)
{
    uint64_t off = 0x1000 + (uint64_t)(2 * qid) * _nvme.db_stride;
    nvme_wr32(_nvme.bar0 + off, tail);
}

static void nvme_ring_cq_doorbell(uint16_t qid, uint16_t head)
{
    uint64_t off = 0x1000 + (uint64_t)(2 * qid + 1) * _nvme.db_stride;
    nvme_wr32(_nvme.bar0 + off, head);
}

/* Submit a command to the admin queue and poll for completion.
 * Returns 0 on success, negative on error. */
static int nvme_admin_cmd(uint8_t opcode, uint32_t nsid,
                          uint64_t prp1, uint64_t prp2,
                          uint32_t cdw10, uint32_t cdw11, uint32_t cdw12)
{
    int idx = _nvme.admin_sq_tail;
    struct nvme_sqe *sqe = &_nvme.admin_sq[idx];

    __builtin_memset(sqe, 0, sizeof(*sqe));
    sqe->cdw0 = (uint32_t)opcode | ((uint32_t)_nvme.admin_cid << 16);
    sqe->nsid = nsid;
    sqe->prp1 = prp1;
    sqe->prp2 = prp2;
    sqe->cdw10 = cdw10;
    sqe->cdw11 = cdw11;
    sqe->cdw12 = cdw12;

    _nvme.admin_sq_tail = (_nvme.admin_sq_tail + 1) % NVME_ADMIN_DEPTH;
    nvme_ring_sq_doorbell(0, _nvme.admin_sq_tail);

    /* Poll CQ for completion */
    volatile struct nvme_cqe *cqe = &_nvme.admin_cq[_nvme.admin_cq_head];
    uint32_t timeout = 5000000;
    while (timeout--) {
        uint16_t status_raw = cqe->status;
        uint8_t phase = status_raw & 1;
        if (phase == _nvme.admin_cq_phase) {
            /* Completion arrived */
            uint16_t sc = (status_raw >> 1) & 0x7FFF;
            _nvme.admin_cq_head = (_nvme.admin_cq_head + 1) % NVME_ADMIN_DEPTH;
            if (_nvme.admin_cq_head == 0)
                _nvme.admin_cq_phase ^= 1;
            nvme_ring_cq_doorbell(0, _nvme.admin_cq_head);
            _nvme.admin_cid++;
            if (sc != 0) {
                serial_puts("[nvme-c] admin cmd failed, status=0x");
                serial_put_hex(sc);
                serial_puts("\r\n");
                return -5; /* EIO */
            }
            return 0;
        }
        /* Tiny delay to avoid hammering the bus */
        __asm__ volatile("pause" ::: "memory");
    }
    serial_puts("[nvme-c] admin cmd timeout\r\n");
    return -110; /* ETIMEDOUT */
}

/* Submit a command to the I/O queue and poll for completion.
 * Returns 0 on success, negative on error. */
static int nvme_io_cmd(uint8_t opcode, uint32_t nsid,
                       uint64_t prp1, uint64_t prp2,
                       uint32_t cdw10, uint32_t cdw11, uint32_t cdw12)
{
    int idx = _nvme.io_sq_tail;
    struct nvme_sqe *sqe = &_nvme.io_sq[idx];

    __builtin_memset(sqe, 0, sizeof(*sqe));
    sqe->cdw0 = (uint32_t)opcode | ((uint32_t)_nvme.io_cid << 16);
    sqe->nsid = nsid;
    sqe->prp1 = prp1;
    sqe->prp2 = prp2;
    sqe->cdw10 = cdw10;
    sqe->cdw11 = cdw11;
    sqe->cdw12 = cdw12;

    _nvme.io_sq_tail = (_nvme.io_sq_tail + 1) % NVME_IO_DEPTH;
    nvme_ring_sq_doorbell(1, _nvme.io_sq_tail);

    /* Poll CQ for completion */
    volatile struct nvme_cqe *cqe = &_nvme.io_cq[_nvme.io_cq_head];
    uint32_t timeout = 5000000;
    while (timeout--) {
        uint16_t status_raw = cqe->status;
        uint8_t phase = status_raw & 1;
        if (phase == _nvme.io_cq_phase) {
            uint16_t sc = (status_raw >> 1) & 0x7FFF;
            _nvme.io_cq_head = (_nvme.io_cq_head + 1) % NVME_IO_DEPTH;
            if (_nvme.io_cq_head == 0)
                _nvme.io_cq_phase ^= 1;
            nvme_ring_cq_doorbell(1, _nvme.io_cq_head);
            _nvme.io_cid++;
            if (sc != 0) {
                serial_puts("[nvme-c] I/O cmd failed, status=0x");
                serial_put_hex(sc);
                serial_puts("\r\n");
                return -5; /* EIO */
            }
            return 0;
        }
        __asm__ volatile("pause" ::: "memory");
    }
    serial_puts("[nvme-c] I/O cmd timeout\r\n");
    return -110;
}

/* ---------------------------------------------------------------
 * _nvme_init_and_read_sector0 — full NVMe init + BPB sector read
 * --------------------------------------------------------------- */
static int _nvme_init_controller(void)
{
    if (_nvme.initialized) return 0;

    /* Ensure PCI cache is populated */
    if (_pci_cache_count < 0) _pci_scan();

    /* Find NVMe device: class=0x01, subclass=0x08 */
    int nvme_idx = -1;
    for (int i = 0; i < _pci_cache_count; i++) {
        if (_pci_cache[i].cls == 0x01 && _pci_cache[i].sub == 0x08) {
            nvme_idx = i;
            break;
        }
    }
    if (nvme_idx < 0) {
        serial_puts("[nvme-c] No NVMe device found on PCI bus\r\n");
        return -19; /* ENODEV */
    }

    /* Step 1: Read BAR0 from PCI config space */
    uint32_t pci_addr = 0x80000000
        | ((uint32_t)_pci_cache[nvme_idx].bus << 16)
        | ((uint32_t)_pci_cache[nvme_idx].dev << 11)
        | 0x10; /* BAR0 offset */
    outl(0xCF8, pci_addr);
    uint32_t bar0_lo = inl(0xCFC);

    /* Check if 64-bit BAR */
    uint64_t bar0_phys;
    if ((bar0_lo & 0x6) == 0x4) {
        /* 64-bit memory BAR: read high 32 bits from BAR1 (offset 0x14) */
        outl(0xCF8, pci_addr + 4);
        uint32_t bar0_hi = inl(0xCFC);
        bar0_phys = ((uint64_t)bar0_hi << 32) | (uint64_t)(bar0_lo & ~0xFu);
    } else {
        bar0_phys = (uint64_t)(bar0_lo & ~0xFu);
    }

    /* Enable bus mastering + memory space in PCI command register */
    uint32_t cmd_addr = 0x80000000
        | ((uint32_t)_pci_cache[nvme_idx].bus << 16)
        | ((uint32_t)_pci_cache[nvme_idx].dev << 11)
        | 0x04; /* Command register offset */
    outl(0xCF8, cmd_addr);
    uint32_t cmd_reg = inl(0xCFC);
    cmd_reg |= (1 << 1) | (1 << 2); /* Memory Space + Bus Master */
    outl(0xCF8, cmd_addr);
    outl(0xCFC, cmd_reg);

    _nvme.bar0 = bar0_phys; /* Identity mapped: phys == virt */

    serial_puts("[nvme-c] BAR0=");
    serial_put_hex(bar0_phys);
    serial_puts("\r\n");

    /* Step 2: Read CAP register (64-bit) */
    uint64_t cap = nvme_rd64(_nvme.bar0 + NVME_REG_CAP);
    serial_puts("[nvme-c] CAP=");
    serial_put_hex(cap);
    serial_puts("\r\n");

    /* Extract doorbell stride: CAP bits [35:32] = DSTRD */
    uint32_t dstrd = (uint32_t)((cap >> 32) & 0xF);
    _nvme.db_stride = 4u << dstrd;

    /* Step 3: Disable controller — clear CC.EN, wait CSTS.RDY=0 */
    uint32_t cc = nvme_rd32(_nvme.bar0 + NVME_REG_CC);
    nvme_wr32(_nvme.bar0 + NVME_REG_CC, cc & ~NVME_CC_EN);

    for (uint32_t i = 0; i < 1000000; i++) {
        uint32_t csts = nvme_rd32(_nvme.bar0 + NVME_REG_CSTS);
        if (!(csts & NVME_CSTS_RDY)) goto disabled;
        if (csts & NVME_CSTS_CFS) {
            serial_puts("[nvme-c] Controller fatal status during disable\r\n");
            return -5;
        }
        __asm__ volatile("pause" ::: "memory");
    }
    serial_puts("[nvme-c] Timeout waiting for controller disable\r\n");
    return -110;
disabled:
    serial_puts("[nvme-c] Controller disabled\r\n");

    /* Step 4: Allocate admin queues (4KB-aligned for NVMe compliance) */
    size_t admin_sq_bytes = NVME_ADMIN_DEPTH * NVME_SQE_SIZE; /* 2048 */
    size_t admin_cq_bytes = NVME_ADMIN_DEPTH * NVME_CQE_SIZE; /* 512  */

    _nvme.admin_sq = (struct nvme_sqe *)nvme_alloc_aligned(admin_sq_bytes, 4096);
    _nvme.admin_cq = (struct nvme_cqe *)nvme_alloc_aligned(admin_cq_bytes, 4096);
    if (!_nvme.admin_sq || !_nvme.admin_cq) {
        serial_puts("[nvme-c] Failed to allocate admin queues\r\n");
        return -12; /* ENOMEM */
    }
    __builtin_memset(_nvme.admin_sq, 0, admin_sq_bytes);
    __builtin_memset(_nvme.admin_cq, 0, admin_cq_bytes);
    _nvme.admin_sq_tail = 0;
    _nvme.admin_cq_head = 0;
    _nvme.admin_cq_phase = 1;
    _nvme.admin_cid = 0;

    /* Step 5: Configure AQA, ASQ, ACQ */
    uint32_t aqa = ((NVME_ADMIN_DEPTH - 1) << 16) | (NVME_ADMIN_DEPTH - 1);
    nvme_wr32(_nvme.bar0 + NVME_REG_AQA, aqa);
    nvme_wr64(_nvme.bar0 + NVME_REG_ASQ, (uint64_t)(uintptr_t)_nvme.admin_sq);
    nvme_wr64(_nvme.bar0 + NVME_REG_ACQ, (uint64_t)(uintptr_t)_nvme.admin_cq);

    serial_puts("[nvme-c] Admin queues configured: SQ=");
    serial_put_hex((uint64_t)(uintptr_t)_nvme.admin_sq);
    serial_puts(" CQ=");
    serial_put_hex((uint64_t)(uintptr_t)_nvme.admin_cq);
    serial_puts("\r\n");

    /* Step 6: Enable controller
     * CC: EN=1, CSS=0 (NVM), MPS=0 (4KB), IOSQES=6 (64B), IOCQES=4 (16B) */
    uint32_t cc_val = NVME_CC_EN | NVME_CC_CSS_NVM | NVME_CC_MPS_4K
                    | NVME_CC_IOSQES_6 | NVME_CC_IOCQES_4;
    nvme_wr32(_nvme.bar0 + NVME_REG_CC, cc_val);

    /* Step 7: Wait for CSTS.RDY=1 */
    for (uint32_t i = 0; i < 1000000; i++) {
        uint32_t csts = nvme_rd32(_nvme.bar0 + NVME_REG_CSTS);
        if (csts & NVME_CSTS_RDY) goto enabled;
        if (csts & NVME_CSTS_CFS) {
            serial_puts("[nvme-c] Controller fatal status during enable\r\n");
            return -5;
        }
        __asm__ volatile("pause" ::: "memory");
    }
    serial_puts("[nvme-c] Timeout waiting for CSTS.RDY\r\n");
    return -110;
enabled:
    serial_puts("[nvme-c] Controller enabled (CSTS.RDY=1)\r\n");

    /* Step 8: Identify Controller (admin opcode 0x06, CNS=1) */
    {
        void *id_buf = nvme_alloc_aligned(4096, 4096);
        if (!id_buf) return -12;
        __builtin_memset(id_buf, 0, 4096);
        int rc = nvme_admin_cmd(0x06, 0,
                                (uint64_t)(uintptr_t)id_buf, 0,
                                1 /* CNS=1: controller */, 0, 0);
        if (rc < 0) {
            serial_puts("[nvme-c] Identify Controller failed\r\n");
            /* Non-fatal: continue anyway */
        } else {
            serial_puts("[nvme-c] Identify Controller OK\r\n");
        }
    }

    /* Step 9: Identify Namespace 1 (admin opcode 0x06, CNS=0, NSID=1) */
    {
        void *ns_buf = nvme_alloc_aligned(4096, 4096);
        if (!ns_buf) return -12;
        __builtin_memset(ns_buf, 0, 4096);
        int rc = nvme_admin_cmd(0x06, 1,
                                (uint64_t)(uintptr_t)ns_buf, 0,
                                0 /* CNS=0: namespace */, 0, 0);
        if (rc < 0) {
            serial_puts("[nvme-c] Identify Namespace failed\r\n");
            _nvme.sector_size = 512;
            _nvme.sector_count = 0;
        } else {
            /* Parse NSZE at offset 0 (64-bit) */
            _nvme.sector_count = *(volatile uint64_t *)((uintptr_t)ns_buf + 0);
            /* Parse FLBAS at offset 26 (1 byte, lower 4 bits = LBA format index) */
            uint8_t flbas = *(volatile uint8_t *)((uintptr_t)ns_buf + 26);
            uint8_t fmt_idx = flbas & 0x0F;
            /* LBAF starts at offset 128, each 4 bytes; LBADS is bits [23:16] */
            uint32_t lbaf = *(volatile uint32_t *)((uintptr_t)ns_buf + 128 + (uint32_t)fmt_idx * 4);
            uint32_t lbads = (lbaf >> 16) & 0xFF;
            if (lbads >= 9 && lbads <= 16)
                _nvme.sector_size = 1u << lbads;
            else
                _nvme.sector_size = 512;

            serial_puts("[nvme-c] NS1: sectors=");
            serial_put_dec((int64_t)_nvme.sector_count);
            serial_puts(", sector_size=");
            serial_put_dec((int64_t)_nvme.sector_size);
            serial_puts("\r\n");
        }
    }

    /* Step 10: Set Number of Queues (Feature 0x07) — request 1 I/O SQ + 1 I/O CQ */
    {
        /* CDW10 = feature ID (0x07) for Set Features */
        /* CDW11 = NCQR[31:16] | NSQR[15:0], each 0-based */
        int rc = nvme_admin_cmd(0x09 /* Set Features */, 0,
                                0, 0,
                                0x07 /* Feature ID: Number of Queues */,
                                (0u << 16) | 0u /* 1 SQ, 1 CQ (0-based) */,
                                0);
        if (rc < 0)
            serial_puts("[nvme-c] Set Number of Queues failed (non-fatal)\r\n");
    }

    /* Step 11: Create I/O Completion Queue (QID 1) */
    size_t io_cq_bytes = NVME_IO_DEPTH * NVME_CQE_SIZE; /* 1024 */
    _nvme.io_cq = (struct nvme_cqe *)nvme_alloc_aligned(io_cq_bytes, 4096);
    if (!_nvme.io_cq) return -12;
    __builtin_memset(_nvme.io_cq, 0, io_cq_bytes);
    _nvme.io_cq_head = 0;
    _nvme.io_cq_phase = 1;
    _nvme.io_cid = 0;
    {
        /* Create I/O CQ: admin opcode 0x05
         * CDW10: QSIZE[31:16] (0-based) | QID[15:0]
         * CDW11: IV[31:16] | IEN[1] | PC[0]
         * PRP1 = CQ physical address */
        uint32_t cdw10 = ((uint32_t)(NVME_IO_DEPTH - 1) << 16) | 1u; /* QID=1 */
        uint32_t cdw11 = 1u; /* PC=1 (physically contiguous), IEN=0, IV=0 */
        int rc = nvme_admin_cmd(0x05, 0,
                                (uint64_t)(uintptr_t)_nvme.io_cq, 0,
                                cdw10, cdw11, 0);
        if (rc < 0) {
            serial_puts("[nvme-c] Create I/O CQ failed\r\n");
            return rc;
        }
    }

    /* Step 12: Create I/O Submission Queue (QID 1) */
    size_t io_sq_bytes = NVME_IO_DEPTH * NVME_SQE_SIZE; /* 4096 */
    _nvme.io_sq = (struct nvme_sqe *)nvme_alloc_aligned(io_sq_bytes, 4096);
    if (!_nvme.io_sq) return -12;
    __builtin_memset(_nvme.io_sq, 0, io_sq_bytes);
    _nvme.io_sq_tail = 0;
    {
        /* Create I/O SQ: admin opcode 0x01
         * CDW10: QSIZE[31:16] (0-based) | QID[15:0]
         * CDW11: CQID[31:16] | QPRIO[2:1] | PC[0]
         * PRP1 = SQ physical address */
        uint32_t cdw10 = ((uint32_t)(NVME_IO_DEPTH - 1) << 16) | 1u; /* QID=1 */
        uint32_t cdw11 = (1u << 16) | 1u; /* CQID=1, PC=1 */
        int rc = nvme_admin_cmd(0x01, 0,
                                (uint64_t)(uintptr_t)_nvme.io_sq, 0,
                                cdw10, cdw11, 0);
        if (rc < 0) {
            serial_puts("[nvme-c] Create I/O SQ failed\r\n");
            return rc;
        }
    }

    serial_puts("[nvme-c] I/O queues created\r\n");
    _nvme.initialized = 1;
    return 0;
}

/* Read one sector from NVMe namespace 1.
 * lba     = logical block address
 * buf     = destination buffer (must be large enough for one sector)
 * Returns 0 on success, negative on error. */
static int _nvme_read_sector_impl(uint64_t lba, void *buf)
{
    if (!_nvme.initialized) {
        int rc = _nvme_init_controller();
        if (rc < 0) return rc;
    }

    /* Allocate a 4KB-aligned DMA buffer for the read */
    void *dma_buf = nvme_alloc_aligned(4096, 4096);
    if (!dma_buf) return -12;
    __builtin_memset(dma_buf, 0, 4096);

    /* NVMe I/O Read: opcode 0x02
     * NSID = 1
     * PRP1 = DMA buffer physical address
     * CDW10 = LBA[31:0]
     * CDW11 = LBA[63:32]
     * CDW12 = NLB[15:0] (0-based, so 0 = 1 sector) */
    uint32_t cdw10 = (uint32_t)(lba & 0xFFFFFFFF);
    uint32_t cdw11 = (uint32_t)(lba >> 32);
    uint32_t cdw12 = 0; /* 1 sector (0-based) */

    int rc = nvme_io_cmd(0x02, 1,
                         (uint64_t)(uintptr_t)dma_buf, 0,
                         cdw10, cdw11, cdw12);
    if (rc < 0) return rc;

    /* Copy from DMA buffer to caller's buffer */
    __builtin_memcpy(buf, dma_buf, _nvme.sector_size);
    return 0;
}

/* Syscall 85 handler: NvmeReadSector
 * a0 = device index (ignored, only one NVMe device supported)
 * a1 = LBA
 * a2 = destination buffer address (caller-provided, must be >= sector_size)
 * Returns 0 on success, negative errno on failure. */
static int64_t _nvme_read_sector(uint64_t device_idx, uint64_t lba, uint64_t buf_addr)
{
    (void)device_idx;
    void *buf = (void *)(uintptr_t)buf_addr;
    if (!buf) return -14; /* EFAULT */
    return (int64_t)_nvme_read_sector_impl(lba, buf);
}

/* _nvme_init_and_read_sector0 — callable from Simple code or early boot
 * Initializes NVMe and reads sector 0 (FAT32 BPB).
 * Returns 0 on success, prints diagnostics to serial. */
static int _nvme_init_and_read_sector0(void)
{
    serial_puts("[nvme-c] === NVMe Init + Sector 0 Read ===\r\n");

    int rc = _nvme_init_controller();
    if (rc < 0) {
        serial_puts("[nvme-c] Controller init failed, rc=");
        serial_put_dec(rc);
        serial_puts("\r\n");
        return rc;
    }

    /* Read sector 0 (FAT32 BPB / boot sector) */
    serial_puts("[nvme-c] Reading sector 0...\r\n");
    uint8_t sector_buf[512];
    __builtin_memset(sector_buf, 0, sizeof(sector_buf));
    rc = _nvme_read_sector_impl(0, sector_buf);
    if (rc < 0) {
        serial_puts("[nvme-c] Sector 0 read failed, rc=");
        serial_put_dec(rc);
        serial_puts("\r\n");
        return rc;
    }

    /* Print first 16 bytes */
    serial_puts("[nvme-c] Sector 0 read OK, first bytes:");
    for (int i = 0; i < 16; i++) {
        serial_putchar(' ');
        static const char hex[] = "0123456789ABCDEF";
        serial_putchar(hex[(sector_buf[i] >> 4) & 0xF]);
        serial_putchar(hex[sector_buf[i] & 0xF]);
    }
    serial_puts("\r\n");

    /* Check FAT32 BPB signature at bytes 510-511: must be 0x55 0xAA */
    uint16_t sig = (uint16_t)sector_buf[510] | ((uint16_t)sector_buf[511] << 8);
    serial_puts("[nvme-c] FAT32 signature at offset 510: 0x");
    serial_put_hex(sig);
    serial_puts("\r\n");
    if (sig == 0xAA55) {
        serial_puts("[nvme-c] FAT32 BPB signature valid!\r\n");
    } else {
        serial_puts("[nvme-c] WARNING: invalid BPB signature (expected 0xAA55)\r\n");
    }

    return 0;
}

/* ===================================================================
 * 8b-fat32. FAT32 file system driver (C implementation)
 *
 * Bypasses the auto-stubbed Simple FAT32 driver (shift operators >>/<<
 * cause "Compose operator should be desugared" errors in Simple).
 * Uses _nvme_read_sector_impl() for sector reads.
 * =================================================================== */

/* Public FAT32 API — callable from Simple via extern fn */
int fat32_find_file(const char *name, uint32_t *out_cluster, uint32_t *out_size);
int fat32_read_file(const char *name, uint8_t *buf, uint32_t max_size, uint32_t *bytes_read);
int fat32_list_dir(void);

/* RuntimeValue wrappers — Simple passes text as tagged heap pointers.
 * These extract the C string from RuntimeValue and call the real functions. */
RuntimeValue spl_fat32_find_file(RuntimeValue name_rv, RuntimeValue out_cluster, RuntimeValue out_size) {
    const char *name = "";
    if (IS_HEAP(name_rv)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(name_rv);
        if (s) name = s->data;
    }
    uint32_t *cluster_ptr = (uint32_t *)(uintptr_t)DECODE_INT(out_cluster);
    uint32_t *size_ptr    = (uint32_t *)(uintptr_t)DECODE_INT(out_size);
    int result = fat32_find_file(name, cluster_ptr, size_ptr);
    return ENCODE_INT(result);
}

RuntimeValue spl_fat32_read_file(RuntimeValue name_rv, RuntimeValue buf_rv, RuntimeValue max_size_rv, RuntimeValue bytes_read_rv) {
    const char *name = "";
    if (IS_HEAP(name_rv)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(name_rv);
        if (s) name = s->data;
    }
    uint8_t  *buf        = (uint8_t *)(uintptr_t)DECODE_INT(buf_rv);
    uint32_t  max_size   = (uint32_t)DECODE_INT(max_size_rv);
    uint32_t *bytes_read = (uint32_t *)(uintptr_t)DECODE_INT(bytes_read_rv);
    int result = fat32_read_file(name, buf, max_size, bytes_read);
    return ENCODE_INT(result);
}

static struct {
    uint32_t bytes_per_sector;
    uint32_t sectors_per_cluster;
    uint32_t reserved_sectors;
    uint32_t num_fats;
    uint32_t fat_size;          /* sectors per FAT */
    uint32_t root_cluster;
    uint32_t data_start_sector; /* first data sector */
    uint32_t total_clusters;
    int initialized;
} _fat32;

/* Helper: print a uint32_t in hex without 0x prefix (compact BPB dump) */
static void _fat32_puthex(uint32_t v) {
    static const char hex[] = "0123456789abcdef";
    if (v > 0xFFFF) { serial_putchar(hex[(v>>28)&0xF]); serial_putchar(hex[(v>>24)&0xF]); serial_putchar(hex[(v>>20)&0xF]); serial_putchar(hex[(v>>16)&0xF]); }
    if (v > 0xFF) { serial_putchar(hex[(v>>12)&0xF]); serial_putchar(hex[(v>>8)&0xF]); }
    serial_putchar(hex[(v>>4)&0xF]); serial_putchar(hex[v&0xF]);
}

/* Parse BPB from sector 0 and initialize FAT32 state.
 * Returns 0 on success, -1 on failure. */
static int _fat32_init(void) {
    if (_fat32.initialized) return 0;

    /* Read sector 0 (BPB) into a DMA-safe buffer */
    uint8_t *bpb = (uint8_t *)nvme_alloc_aligned(512, 512);
    if (!bpb) return -1;
    __builtin_memset(bpb, 0, 512);

    if (_nvme_read_sector_impl(0, bpb) != 0) {
        serial_puts("[fat32-c] Failed to read sector 0\r\n");
        return -1;
    }

    /* Check boot signature at bytes 510-511 */
    if (bpb[510] != 0x55 || bpb[511] != 0xAA) {
        serial_puts("[fat32-c] Invalid BPB signature\r\n");
        return -1;
    }

    /* Parse BPB fields (all little-endian) */
    _fat32.bytes_per_sector    = (uint32_t)bpb[11] | ((uint32_t)bpb[12] << 8);
    _fat32.sectors_per_cluster = bpb[13];
    _fat32.reserved_sectors    = (uint32_t)bpb[14] | ((uint32_t)bpb[15] << 8);
    _fat32.num_fats            = bpb[16];
    _fat32.fat_size            = (uint32_t)bpb[36] | ((uint32_t)bpb[37] << 8)
                               | ((uint32_t)bpb[38] << 16) | ((uint32_t)bpb[39] << 24);
    _fat32.root_cluster        = (uint32_t)bpb[44] | ((uint32_t)bpb[45] << 8)
                               | ((uint32_t)bpb[46] << 16) | ((uint32_t)bpb[47] << 24);
    _fat32.data_start_sector   = _fat32.reserved_sectors
                               + (_fat32.num_fats * _fat32.fat_size);

    /* Print BPB info for diagnostics */
    serial_puts("[fat32-c] BPS=");    _fat32_puthex(_fat32.bytes_per_sector);
    serial_puts(" SPC=");             _fat32_puthex(_fat32.sectors_per_cluster);
    serial_puts(" reserved=");        _fat32_puthex(_fat32.reserved_sectors);
    serial_puts(" FATs=");            _fat32_puthex(_fat32.num_fats);
    serial_puts(" FAT_size=");        _fat32_puthex(_fat32.fat_size);
    serial_puts(" root_cluster=");    _fat32_puthex(_fat32.root_cluster);
    serial_puts(" data_start=");      _fat32_puthex(_fat32.data_start_sector);
    serial_puts("\r\n");

    _fat32.initialized = 1;
    return 0;
}

/* Convert a cluster number to a sector number (clusters are 2-based). */
static uint32_t _fat32_cluster_to_sector(uint32_t cluster) {
    return _fat32.data_start_sector + (cluster - 2) * _fat32.sectors_per_cluster;
}

/* Read one cluster into buf. buf must be at least sectors_per_cluster * 512 bytes.
 * Returns 0 on success, -1 on error. */
static int _fat32_read_cluster(uint32_t cluster, uint8_t *buf) {
    uint32_t sector = _fat32_cluster_to_sector(cluster);
    for (uint32_t i = 0; i < _fat32.sectors_per_cluster; i++) {
        if (_nvme_read_sector_impl(sector + i, buf + i * 512) != 0)
            return -1;
    }
    return 0;
}

/* Follow the FAT chain: return the next cluster number, or >= 0x0FFFFFF8 for EOC. */
static uint32_t _fat32_next_cluster(uint32_t cluster) {
    /* Each FAT entry is 4 bytes, located in the reserved area */
    uint32_t fat_offset = cluster * 4;
    uint32_t fat_sector = _fat32.reserved_sectors + (fat_offset / 512);
    uint32_t fat_offset_in_sector = fat_offset % 512;

    uint8_t *sector_buf = (uint8_t *)nvme_alloc_aligned(512, 512);
    if (!sector_buf) return 0x0FFFFFFF; /* treat alloc failure as EOC */
    __builtin_memset(sector_buf, 0, 512);

    if (_nvme_read_sector_impl(fat_sector, sector_buf) != 0)
        return 0x0FFFFFFF; /* treat read failure as EOC */

    uint32_t entry = (uint32_t)sector_buf[fat_offset_in_sector]
                   | ((uint32_t)sector_buf[fat_offset_in_sector + 1] << 8)
                   | ((uint32_t)sector_buf[fat_offset_in_sector + 2] << 16)
                   | ((uint32_t)sector_buf[fat_offset_in_sector + 3] << 24);
    entry &= 0x0FFFFFFF; /* mask upper 4 bits (reserved in FAT32) */
    return entry;
}

/* Convert a filename like "hello.txt" to FAT32 8.3 format (uppercase, space-padded).
 * out must be at least 11 bytes. */
static void _fat32_make_8_3_name(const char *name, char out[11]) {
    __builtin_memset(out, ' ', 11);
    const char *dot = (const char *)0;
    for (const char *p = name; *p; p++) {
        if (*p == '.') dot = p;
    }

    int base_len = dot ? (int)(dot - name) : (int)strlen(name);
    for (int i = 0; i < 8 && i < base_len; i++) {
        out[i] = (name[i] >= 'a' && name[i] <= 'z') ? name[i] - 32 : name[i];
    }

    if (dot) {
        const char *ext = dot + 1;
        for (int i = 0; i < 3 && ext[i]; i++) {
            out[8 + i] = (ext[i] >= 'a' && ext[i] <= 'z') ? ext[i] - 32 : ext[i];
        }
    }
}

/* Find a file by name in the root directory.
 * Returns 0 on success and fills out_cluster/out_size, -1 if not found. */
int fat32_find_file(const char *name, uint32_t *out_cluster, uint32_t *out_size) {
    if (!_fat32.initialized) {
        if (_fat32_init() != 0) return -1;
    }

    /* Build 8.3 name for comparison */
    char name83[11];
    _fat32_make_8_3_name(name, name83);

    /* Allocate a cluster-sized buffer for reading directory entries */
    uint32_t cluster_bytes = _fat32.sectors_per_cluster * 512;
    uint8_t *dir_buf = (uint8_t *)nvme_alloc_aligned(cluster_bytes, 512);
    if (!dir_buf) return -1;

    uint32_t cluster = _fat32.root_cluster;

    while (cluster >= 2 && cluster < 0x0FFFFFF8) {
        if (_fat32_read_cluster(cluster, dir_buf) != 0)
            return -1;

        int entries_per_cluster = (int)(cluster_bytes / 32);
        for (int i = 0; i < entries_per_cluster; i++) {
            uint8_t *entry = dir_buf + i * 32;

            if (entry[0] == 0x00) return -1; /* end of directory */
            if (entry[0] == 0xE5) continue;  /* deleted entry */
            if ((entry[11] & 0x0F) == 0x0F) continue; /* LFN entry, skip */

            if (memcmp(entry, name83, 11) == 0) {
                /* Found: extract first cluster (high word at offset 20, low at 26) and size */
                uint32_t lo = (uint32_t)entry[26] | ((uint32_t)entry[27] << 8);
                uint32_t hi = (uint32_t)entry[20] | ((uint32_t)entry[21] << 8);
                *out_cluster = lo | (hi << 16);
                *out_size = (uint32_t)entry[28] | ((uint32_t)entry[29] << 8)
                          | ((uint32_t)entry[30] << 16) | ((uint32_t)entry[31] << 24);
                return 0;
            }
        }
        cluster = _fat32_next_cluster(cluster);
    }
    return -1; /* not found */
}

/* Read an entire file by name into buf (up to max_size bytes).
 * Returns 0 on success, -1 on failure. *bytes_read is set to actual bytes read. */
int fat32_read_file(const char *name, uint8_t *buf, uint32_t max_size,
                    uint32_t *bytes_read) {
    uint32_t cluster, file_size;
    if (fat32_find_file(name, &cluster, &file_size) != 0) return -1;

    uint32_t to_read = file_size < max_size ? file_size : max_size;
    uint32_t remaining = to_read;
    uint32_t cluster_bytes = _fat32.sectors_per_cluster * 512;
    uint8_t *cluster_buf = (uint8_t *)nvme_alloc_aligned(cluster_bytes, 512);
    if (!cluster_buf) return -1;
    uint32_t offset = 0;

    while (remaining > 0 && cluster >= 2 && cluster < 0x0FFFFFF8) {
        if (_fat32_read_cluster(cluster, cluster_buf) != 0) return -1;

        uint32_t copy = remaining < cluster_bytes ? remaining : cluster_bytes;
        __builtin_memcpy(buf + offset, cluster_buf, copy);
        offset += copy;
        remaining -= copy;
        cluster = _fat32_next_cluster(cluster);
    }

    *bytes_read = offset;
    return 0;
}

/* List root directory entries to serial (for diagnostics). */
int fat32_list_dir(void) {
    if (!_fat32.initialized) {
        if (_fat32_init() != 0) return -1;
    }

    serial_puts("[fat32-c] Root directory listing:\r\n");

    uint32_t cluster_bytes = _fat32.sectors_per_cluster * 512;
    uint8_t *dir_buf = (uint8_t *)nvme_alloc_aligned(cluster_bytes, 512);
    if (!dir_buf) return -1;

    uint32_t cluster = _fat32.root_cluster;
    int count = 0;

    while (cluster >= 2 && cluster < 0x0FFFFFF8) {
        if (_fat32_read_cluster(cluster, dir_buf) != 0) return -1;

        int entries_per_cluster = (int)(cluster_bytes / 32);
        for (int i = 0; i < entries_per_cluster; i++) {
            uint8_t *entry = dir_buf + i * 32;

            if (entry[0] == 0x00) goto done; /* end of directory */
            if (entry[0] == 0xE5) continue;  /* deleted */
            if ((entry[11] & 0x0F) == 0x0F) continue; /* LFN */

            /* Print 8.3 name */
            serial_puts("  ");
            for (int j = 0; j < 8; j++) {
                if (entry[j] != ' ') serial_putchar((char)entry[j]);
            }
            if (entry[8] != ' ') {
                serial_putchar('.');
                for (int j = 8; j < 11; j++) {
                    if (entry[j] != ' ') serial_putchar((char)entry[j]);
                }
            }

            /* Print attributes and size */
            uint8_t attr = entry[11];
            if (attr & 0x10) serial_puts("  <DIR>");
            else {
                uint32_t sz = (uint32_t)entry[28] | ((uint32_t)entry[29] << 8)
                            | ((uint32_t)entry[30] << 16) | ((uint32_t)entry[31] << 24);
                serial_puts("  size=");
                serial_put_dec((int64_t)sz);
            }
            serial_puts("\r\n");
            count++;
        }
        cluster = _fat32_next_cluster(cluster);
    }
done:
    serial_puts("[fat32-c] ");
    serial_put_dec((int64_t)count);
    serial_puts(" entries\r\n");
    return 0;
}

/* Syscall wrapper: Fat32ReadFile
 * a0 = pointer to null-terminated filename string
 * a1 = destination buffer address
 * a2 = max buffer size
 * Returns bytes read on success, negative on failure. */
static int64_t _fat32_read_file_syscall(uint64_t name_addr, uint64_t buf_addr,
                                         uint64_t max_size) {
    const char *name = (const char *)(uintptr_t)name_addr;
    uint8_t *buf = (uint8_t *)(uintptr_t)buf_addr;
    if (!name || !buf || max_size == 0) return -14; /* EFAULT */

    uint32_t bytes_read = 0;
    if (fat32_read_file(name, buf, (uint32_t)max_size, &bytes_read) != 0)
        return -2; /* ENOENT */
    return (int64_t)bytes_read;
}

/* Forward declaration for serial_puthex (defined in section 9d) */
static void serial_puthex(uint32_t v);

/* ===================================================================
 * 8c-net. VirtIO-net driver + ARP/ICMP (ping) responder
 *
 * Supports VirtIO-net PCI legacy transport (vendor 0x1AF4, device
 * 0x1000 with subsystem for network, or any device with PCI class
 * 02.00 from vendor 0x1AF4).
 *
 * Legacy BAR0 (I/O port) register layout:
 *   0x00  host_features   (u32, R)
 *   0x04  guest_features  (u32, W)
 *   0x08  queue_pfn       (u32, W)  — page frame number of virtqueue
 *   0x0C  queue_size      (u16, R)
 *   0x0E  queue_sel       (u16, W)
 *   0x10  queue_notify    (u16, W)
 *   0x12  status          (u8, RW)
 *   0x13  isr             (u8, R)
 *   0x14  mac[6]          (R)       — device MAC address
 *
 * Virtqueue memory layout (contiguous, page-aligned):
 *   Descriptors:   16 bytes * queue_size
 *   Available ring: 2+2+2*queue_size bytes
 *   (pad to 4096 boundary)
 *   Used ring:      2+2+8*queue_size bytes
 * =================================================================== */

/* --- VirtIO status bits --- */
#define VIRTIO_STATUS_ACK        1
#define VIRTIO_STATUS_DRIVER     2
#define VIRTIO_STATUS_FEATURES_OK 8
#define VIRTIO_STATUS_DRIVER_OK  4
#define VIRTIO_STATUS_FAILED     128

/* --- VirtIO feature bits --- */
#define VIRTIO_NET_F_MAC         (1u << 5)
#define VIRTIO_NET_F_STATUS      (1u << 16)
#define VIRTIO_NET_F_CSUM        (1u << 0)

/* --- Virtqueue descriptor flags --- */
#define VRING_DESC_F_NEXT     1
#define VRING_DESC_F_WRITE    2

/* --- VirtIO-net header (legacy, 10 bytes) --- */
struct virtio_net_hdr {
    uint8_t  flags;
    uint8_t  gso_type;
    uint16_t hdr_len;
    uint16_t gso_size;
    uint16_t csum_start;
    uint16_t csum_offset;
} __attribute__((packed));

#define VIRTIO_NET_HDR_SIZE 10

/* --- Virtqueue structures --- */
struct vring_desc {
    uint64_t addr;
    uint32_t len;
    uint16_t flags;
    uint16_t next;
} __attribute__((packed));

struct vring_avail {
    uint16_t flags;
    uint16_t idx;
    uint16_t ring[];
} __attribute__((packed));

struct vring_used_elem {
    uint32_t id;
    uint32_t len;
} __attribute__((packed));

struct vring_used {
    uint16_t flags;
    uint16_t idx;
    struct vring_used_elem ring[];
} __attribute__((packed));

/* --- Ethernet / ARP / IP / ICMP protocol constants --- */
#define ETH_ALEN       6
#define ETH_HLEN       14
#define ETH_P_IP       0x0800
#define ETH_P_ARP      0x0806

#define ARP_HW_ETHER   1
#define ARP_OP_REQUEST  1
#define ARP_OP_REPLY    2

#define IP_PROTO_ICMP   1
#define ICMP_ECHO_REQ   8
#define ICMP_ECHO_REPLY 0

/* --- Ethernet header --- */
struct eth_hdr {
    uint8_t  dst[ETH_ALEN];
    uint8_t  src[ETH_ALEN];
    uint16_t ethertype;   /* big-endian */
} __attribute__((packed));

/* --- ARP packet (Ethernet + IPv4) --- */
struct arp_pkt {
    uint16_t hw_type;     /* big-endian */
    uint16_t proto_type;  /* big-endian */
    uint8_t  hw_len;
    uint8_t  proto_len;
    uint16_t opcode;      /* big-endian */
    uint8_t  sender_mac[ETH_ALEN];
    uint8_t  sender_ip[4];
    uint8_t  target_mac[ETH_ALEN];
    uint8_t  target_ip[4];
} __attribute__((packed));

/* --- IPv4 header (minimal, no options) --- */
struct ipv4_hdr {
    uint8_t  ver_ihl;     /* version(4) + IHL(4) */
    uint8_t  tos;
    uint16_t total_len;   /* big-endian */
    uint16_t id;
    uint16_t frag_off;
    uint8_t  ttl;
    uint8_t  protocol;
    uint16_t checksum;    /* big-endian */
    uint8_t  src_ip[4];
    uint8_t  dst_ip[4];
} __attribute__((packed));

/* --- ICMP header --- */
struct icmp_hdr {
    uint8_t  type;
    uint8_t  code;
    uint16_t checksum;    /* big-endian */
    uint16_t id;
    uint16_t seq;
} __attribute__((packed));

/* --- Byte-order helpers --- */
static inline uint16_t _net_htons(uint16_t h) {
    return (uint16_t)((h >> 8) | (h << 8));
}
static inline uint16_t _net_ntohs(uint16_t n) {
    return _net_htons(n);
}
static inline uint32_t _net_htonl(uint32_t h) {
    return ((h & 0xFF) << 24) | ((h & 0xFF00) << 8)
         | ((h >> 8) & 0xFF00) | ((h >> 24) & 0xFF);
}
static inline uint32_t __attribute__((unused)) _net_ntohl(uint32_t n) {
    return _net_htonl(n);
}

/* --- Internet checksum (RFC 1071) --- */
static uint16_t _inet_checksum(const void *data, size_t len)
{
    const uint8_t *p = (const uint8_t *)data;
    uint32_t sum = 0;
    for (size_t i = 0; i + 1 < len; i += 2) {
        sum += (uint32_t)((uint16_t)p[i] << 8 | p[i+1]);
    }
    if (len & 1) {
        sum += (uint32_t)((uint16_t)p[len-1] << 8);
    }
    while (sum >> 16)
        sum = (sum & 0xFFFF) + (sum >> 16);
    return _net_htons((uint16_t)~sum);
}

/* --- MAC address print helper --- */
static void _net_print_mac(const uint8_t *mac) {
    static const char hex[] = "0123456789abcdef";
    for (int i = 0; i < 6; i++) {
        if (i) serial_putchar(':');
        serial_putchar(hex[(mac[i] >> 4) & 0xF]);
        serial_putchar(hex[mac[i] & 0xF]);
    }
}

/* --- IP address print helper --- */
static void _net_print_ip(const uint8_t *ip) {
    for (int i = 0; i < 4; i++) {
        if (i) serial_putchar('.');
        serial_put_dec((int64_t)ip[i]);
    }
}

/* --- VirtIO-net driver state --- */
#define VIRTIO_NET_QUEUE_SIZE 128  /* max descriptors per queue */
#define VIRTIO_NET_BUF_SIZE  2048  /* per-buffer size for RX/TX */

static struct {
    uint16_t iobase;         /* BAR0 I/O port base */
    uint8_t  mac[6];
    uint8_t  our_ip[4];     /* 10.0.2.15 */
    uint8_t  gateway_ip[4]; /* 10.0.2.2  */

    /* RX queue (queue 0) */
    uint16_t rx_qsize;
    struct vring_desc  *rx_desc;
    struct vring_avail *rx_avail;
    struct vring_used  *rx_used;
    uint8_t *rx_buffers;    /* rx_qsize * VIRTIO_NET_BUF_SIZE contiguous */
    uint16_t rx_last_used;

    /* TX queue (queue 1) */
    uint16_t tx_qsize;
    struct vring_desc  *tx_desc;
    struct vring_avail *tx_avail;
    struct vring_used  *tx_used;
    uint8_t *tx_buffers;    /* tx_qsize * VIRTIO_NET_BUF_SIZE contiguous */
    uint16_t tx_last_used;
    uint16_t tx_next_desc;  /* next free TX descriptor index */

    int initialized;
    uint32_t rx_count;      /* total frames received */
    uint32_t tx_count;      /* total frames sent */
    uint32_t arp_replies;   /* ARP replies sent */
    uint32_t icmp_replies;  /* ICMP echo replies sent */
} _vnet;

/* --- VirtIO BAR0 I/O register access --- */
static inline uint32_t _vnet_rd32(uint16_t off) {
    return inl(_vnet.iobase + off);
}
static inline void _vnet_wr32(uint16_t off, uint32_t val) {
    outl(_vnet.iobase + off, val);
}
static inline uint16_t _vnet_rd16(uint16_t off) {
    return inw(_vnet.iobase + off);
}
static inline void _vnet_wr16(uint16_t off, uint16_t val) {
    outw(_vnet.iobase + off, val);
}
static inline uint8_t _vnet_rd8(uint16_t off) {
    return inb(_vnet.iobase + off);
}
static inline void _vnet_wr8(uint16_t off, uint8_t val) {
    outb(_vnet.iobase + off, val);
}

/* -----------------------------------------------------------
 * _vnet_setup_queue — allocate and configure one virtqueue
 *
 * VirtIO legacy layout for a queue of size N:
 *   Descriptors: N * 16 bytes
 *   Available:   2 + 2 + N*2 bytes  (+ 2 bytes used_event, optional)
 *   Padding to 4096-byte boundary
 *   Used:        2 + 2 + N*8 bytes  (+ 2 bytes avail_event, optional)
 *
 * The device wants the physical page frame number (addr >> 12).
 * ----------------------------------------------------------- */
static int _vnet_setup_queue(uint16_t qsel,
                             uint16_t *out_qsize,
                             struct vring_desc  **out_desc,
                             struct vring_avail **out_avail,
                             struct vring_used  **out_used)
{
    /* Select queue */
    _vnet_wr16(0x0E, qsel);

    /* Read queue size (max descriptors) */
    uint16_t qsize = _vnet_rd16(0x0C);
    if (qsize == 0) {
        serial_puts("[net] queue ");
        serial_put_dec(qsel);
        serial_puts(" size=0, not available\r\n");
        return -1;
    }
    /* Clamp to our max */
    if (qsize > VIRTIO_NET_QUEUE_SIZE) qsize = VIRTIO_NET_QUEUE_SIZE;

    serial_puts("[net] queue ");
    serial_put_dec(qsel);
    serial_puts(" size=");
    serial_put_dec(qsize);
    serial_puts("\r\n");

    /* Calculate memory layout sizes */
    size_t desc_sz  = (size_t)qsize * 16;
    size_t avail_sz = 2 + 2 + (size_t)qsize * 2 + 2; /* +2 for used_event */
    size_t desc_avail_sz = desc_sz + avail_sz;
    /* Round up to 4096 boundary */
    size_t desc_avail_aligned = (desc_avail_sz + 4095) & ~(size_t)4095;
    size_t used_sz = 2 + 2 + (size_t)qsize * 8 + 2; /* +2 for avail_event */
    size_t total = desc_avail_aligned + used_sz;

    /* Allocate page-aligned memory */
    void *mem = nvme_alloc_aligned(total, 4096);
    if (!mem) {
        serial_puts("[net] failed to alloc queue memory\r\n");
        return -12;
    }
    __builtin_memset(mem, 0, total);

    uint8_t *base = (uint8_t *)mem;
    *out_desc  = (struct vring_desc *)base;
    *out_avail = (struct vring_avail *)(base + desc_sz);
    *out_used  = (struct vring_used *)(base + desc_avail_aligned);
    *out_qsize = qsize;

    /* Tell device the page frame number */
    uint32_t pfn = (uint32_t)((uintptr_t)mem >> 12);
    _vnet_wr32(0x08, pfn);

    return 0;
}

/* -----------------------------------------------------------
 * _vnet_rx_fill — populate RX queue with empty buffers
 *
 * Each RX buffer gets a 2-descriptor chain:
 *   desc[2i]   = virtio_net_hdr (device-writable, 10 bytes)
 *   desc[2i+1] = frame payload  (device-writable, rest of buffer)
 *
 * For simplicity we use a single descriptor per buffer that
 * covers the whole buffer (header + frame). The device writes
 * the virtio-net header first, then the ethernet frame.
 * ----------------------------------------------------------- */
static void _vnet_rx_fill(void)
{
    for (uint16_t i = 0; i < _vnet.rx_qsize; i++) {
        uint8_t *buf = _vnet.rx_buffers + (size_t)i * VIRTIO_NET_BUF_SIZE;
        _vnet.rx_desc[i].addr  = (uint64_t)(uintptr_t)buf;
        _vnet.rx_desc[i].len   = VIRTIO_NET_BUF_SIZE;
        _vnet.rx_desc[i].flags = VRING_DESC_F_WRITE; /* device writes */
        _vnet.rx_desc[i].next  = 0;

        _vnet.rx_avail->ring[i] = i;
    }
    /* Memory barrier: ensure descriptors + ring entries are visible */
    __asm__ volatile("mfence" ::: "memory");
    _vnet.rx_avail->idx = _vnet.rx_qsize;
    _vnet.rx_last_used = 0;

    /* Memory barrier: ensure idx is visible before we notify */
    __asm__ volatile("mfence" ::: "memory");

    /* Notify device about RX buffers (queue 0) */
    _vnet_wr16(0x10, 0);
}

/* -----------------------------------------------------------
 * _vnet_send_frame — transmit one Ethernet frame
 *
 * Prepends a 10-byte virtio-net header (all zeros = no offload).
 * Copies frame data into a TX buffer, adds to TX avail ring,
 * notifies device.
 *
 * Returns 0 on success, negative on error.
 * ----------------------------------------------------------- */
static int _vnet_send_frame(const void *frame, uint16_t frame_len)
{
    if (!_vnet.initialized) return -19; /* ENODEV */
    if (frame_len + VIRTIO_NET_HDR_SIZE > VIRTIO_NET_BUF_SIZE) return -90;

    uint16_t di = _vnet.tx_next_desc;
    if (di >= _vnet.tx_qsize) {
        /* Wrap around — in a real driver we'd track free descs properly */
        di = 0;
    }
    _vnet.tx_next_desc = di + 1;

    uint8_t *buf = _vnet.tx_buffers + (size_t)di * VIRTIO_NET_BUF_SIZE;

    /* Virtio-net header: all zeros (no checksum offload, no GSO) */
    __builtin_memset(buf, 0, VIRTIO_NET_HDR_SIZE);
    /* Ethernet frame right after header */
    __builtin_memcpy(buf + VIRTIO_NET_HDR_SIZE, frame, frame_len);

    uint32_t total_len = VIRTIO_NET_HDR_SIZE + frame_len;

    /* Fill descriptor */
    _vnet.tx_desc[di].addr  = (uint64_t)(uintptr_t)buf;
    _vnet.tx_desc[di].len   = total_len;
    _vnet.tx_desc[di].flags = 0; /* device reads */
    _vnet.tx_desc[di].next  = 0;

    /* Add to available ring */
    uint16_t avail_idx = _vnet.tx_avail->idx;
    _vnet.tx_avail->ring[avail_idx % _vnet.tx_qsize] = di;
    __asm__ volatile("mfence" ::: "memory");
    _vnet.tx_avail->idx = avail_idx + 1;

    /* Notify device (queue 1 = TX) */
    _vnet_wr16(0x10, 1);
    _vnet.tx_count++;

    return 0;
}

/* -----------------------------------------------------------
 * _vnet_handle_arp — respond to ARP request for our IP
 * ----------------------------------------------------------- */
static void _vnet_handle_arp(const uint8_t *frame, uint16_t frame_len)
{
    if (frame_len < (uint16_t)(ETH_HLEN + sizeof(struct arp_pkt))) return;

    const struct arp_pkt *arp = (const struct arp_pkt *)(frame + ETH_HLEN);

    /* Only handle Ethernet/IPv4 ARP requests */
    if (_net_ntohs(arp->hw_type) != ARP_HW_ETHER) return;
    if (_net_ntohs(arp->proto_type) != ETH_P_IP) return;
    if (_net_ntohs(arp->opcode) != ARP_OP_REQUEST) return;

    /* Check if target IP is ours */
    if (__builtin_memcmp(arp->target_ip, _vnet.our_ip, 4) != 0) return;

    serial_puts("[net] ARP request for ");
    _net_print_ip(arp->target_ip);
    serial_puts(" from ");
    _net_print_mac(arp->sender_mac);
    serial_puts("\r\n");

    /* Build ARP reply */
    uint8_t reply[ETH_HLEN + sizeof(struct arp_pkt)];
    struct eth_hdr *reth = (struct eth_hdr *)reply;
    struct arp_pkt *rarp = (struct arp_pkt *)(reply + ETH_HLEN);

    /* Ethernet header: send back to requester */
    __builtin_memcpy(reth->dst, arp->sender_mac, ETH_ALEN);
    __builtin_memcpy(reth->src, _vnet.mac, ETH_ALEN);
    reth->ethertype = _net_htons(ETH_P_ARP);

    /* ARP reply */
    rarp->hw_type    = _net_htons(ARP_HW_ETHER);
    rarp->proto_type = _net_htons(ETH_P_IP);
    rarp->hw_len     = ETH_ALEN;
    rarp->proto_len  = 4;
    rarp->opcode     = _net_htons(ARP_OP_REPLY);
    __builtin_memcpy(rarp->sender_mac, _vnet.mac, ETH_ALEN);
    __builtin_memcpy(rarp->sender_ip, _vnet.our_ip, 4);
    __builtin_memcpy(rarp->target_mac, arp->sender_mac, ETH_ALEN);
    __builtin_memcpy(rarp->target_ip, arp->sender_ip, 4);

    _vnet_send_frame(reply, sizeof(reply));
    _vnet.arp_replies++;

    serial_puts("[net] ARP reply sent\r\n");
}

/* -----------------------------------------------------------
 * _vnet_handle_icmp — respond to ICMP echo requests (ping)
 * ----------------------------------------------------------- */
static void _vnet_handle_icmp(const uint8_t *frame, uint16_t frame_len)
{
    if (frame_len < (uint16_t)(ETH_HLEN + sizeof(struct ipv4_hdr) + sizeof(struct icmp_hdr)))
        return;

    const struct eth_hdr  *eth  = (const struct eth_hdr *)frame;
    const struct ipv4_hdr *ip   = (const struct ipv4_hdr *)(frame + ETH_HLEN);

    /* Only handle IPv4 */
    if ((ip->ver_ihl >> 4) != 4) return;
    uint16_t ihl = (uint16_t)(ip->ver_ihl & 0x0F) * 4;
    if (ihl < 20) return;

    /* Only handle ICMP */
    if (ip->protocol != IP_PROTO_ICMP) return;

    /* Check destination is our IP */
    if (__builtin_memcmp(ip->dst_ip, _vnet.our_ip, 4) != 0) return;

    const struct icmp_hdr *icmp = (const struct icmp_hdr *)(frame + ETH_HLEN + ihl);

    /* Only respond to echo requests */
    if (icmp->type != ICMP_ECHO_REQ || icmp->code != 0) return;

    uint16_t ip_total = _net_ntohs(ip->total_len);
    uint16_t icmp_len = (uint16_t)(ip_total - ihl);

    serial_puts("[net] ICMP echo request from ");
    _net_print_ip(ip->src_ip);
    serial_puts(" id=");
    serial_put_dec(_net_ntohs(icmp->id));
    serial_puts(" seq=");
    serial_put_dec(_net_ntohs(icmp->seq));
    serial_puts("\r\n");

    /* Build ICMP echo reply — same frame with swapped addresses and type=0 */
    uint16_t reply_len = ETH_HLEN + ip_total;
    if (reply_len > VIRTIO_NET_BUF_SIZE - VIRTIO_NET_HDR_SIZE) return;

    uint8_t reply[VIRTIO_NET_BUF_SIZE];
    __builtin_memcpy(reply, frame, reply_len);

    struct eth_hdr  *reth  = (struct eth_hdr *)reply;
    struct ipv4_hdr *rip   = (struct ipv4_hdr *)(reply + ETH_HLEN);
    struct icmp_hdr *ricmp = (struct icmp_hdr *)(reply + ETH_HLEN + ihl);

    /* Swap Ethernet addresses */
    __builtin_memcpy(reth->dst, eth->src, ETH_ALEN);
    __builtin_memcpy(reth->src, _vnet.mac, ETH_ALEN);

    /* Swap IP addresses */
    __builtin_memcpy(rip->dst_ip, ip->src_ip, 4);
    __builtin_memcpy(rip->src_ip, _vnet.our_ip, 4);
    rip->ttl = 64;

    /* Recalculate IP checksum */
    rip->checksum = 0;
    rip->checksum = _inet_checksum(rip, ihl);

    /* Change ICMP type from echo request (8) to echo reply (0) */
    ricmp->type = ICMP_ECHO_REPLY;

    /* Recalculate ICMP checksum */
    ricmp->checksum = 0;
    ricmp->checksum = _inet_checksum(ricmp, icmp_len);

    _vnet_send_frame(reply, reply_len);
    _vnet.icmp_replies++;

    serial_puts("[net] ICMP echo reply sent\r\n");
}

/* -----------------------------------------------------------
 * _vnet_handle_frame — dispatch incoming Ethernet frame
 * ----------------------------------------------------------- */
static void _vnet_handle_frame(const uint8_t *frame, uint16_t frame_len)
{
    if (frame_len < ETH_HLEN) return;

    const struct eth_hdr *eth = (const struct eth_hdr *)frame;
    uint16_t ethertype = _net_ntohs(eth->ethertype);

    switch (ethertype) {
        case ETH_P_ARP:
            _vnet_handle_arp(frame, frame_len);
            break;
        case ETH_P_IP:
            _vnet_handle_icmp(frame, frame_len);
            break;
        default:
            /* Ignore unknown ethertype */
            break;
    }
}

/* -----------------------------------------------------------
 * _virtio_net_poll — check RX used ring, process frames
 *
 * Returns: number of frames processed (0 if none available)
 * ----------------------------------------------------------- */
static int _virtio_net_poll(void)
{
    if (!_vnet.initialized) return -19;

    int processed = 0;

    while (1) {
        /* Read used ring idx (device updates this) */
        __asm__ volatile("mfence" ::: "memory");
        uint16_t used_idx = _vnet.rx_used->idx;

        if (_vnet.rx_last_used == used_idx) break; /* no new frames */

        /* Get the used element */
        uint16_t slot = _vnet.rx_last_used % _vnet.rx_qsize;
        uint32_t desc_id  = _vnet.rx_used->ring[slot].id;
        uint32_t used_len = _vnet.rx_used->ring[slot].len;

        _vnet.rx_last_used++;

        if (desc_id >= _vnet.rx_qsize) continue; /* safety */

        /* The buffer contains: virtio_net_hdr (10 bytes) + ethernet frame */
        uint8_t *buf = _vnet.rx_buffers + (size_t)desc_id * VIRTIO_NET_BUF_SIZE;
        if (used_len <= VIRTIO_NET_HDR_SIZE) {
            /* Runt — no frame data */
        } else {
            uint16_t frame_len = (uint16_t)(used_len - VIRTIO_NET_HDR_SIZE);
            uint8_t *frame = buf + VIRTIO_NET_HDR_SIZE;
            _vnet.rx_count++;
            _vnet_handle_frame(frame, frame_len);
        }

        /* Recycle the buffer: re-add to available ring */
        _vnet.rx_desc[desc_id].addr  = (uint64_t)(uintptr_t)buf;
        _vnet.rx_desc[desc_id].len   = VIRTIO_NET_BUF_SIZE;
        _vnet.rx_desc[desc_id].flags = VRING_DESC_F_WRITE;
        _vnet.rx_desc[desc_id].next  = 0;

        uint16_t avail_idx = _vnet.rx_avail->idx;
        _vnet.rx_avail->ring[avail_idx % _vnet.rx_qsize] = (uint16_t)desc_id;
        __asm__ volatile("mfence" ::: "memory");
        _vnet.rx_avail->idx = avail_idx + 1;

        processed++;
    }

    /* Notify device if we recycled any buffers (queue 0 = RX) */
    if (processed > 0) {
        _vnet_wr16(0x10, 0);
    }

    return processed;
}

/* -----------------------------------------------------------
 * _vnet_send_gratuitous_arp — announce our MAC/IP to the network
 *
 * Sends a gratuitous ARP request (sender = target = our IP)
 * so QEMU's user-mode networking and any switches learn our MAC.
 * ----------------------------------------------------------- */
static void _vnet_send_gratuitous_arp(void)
{
    uint8_t frame[ETH_HLEN + sizeof(struct arp_pkt)];
    struct eth_hdr *eth = (struct eth_hdr *)frame;
    struct arp_pkt *arp = (struct arp_pkt *)(frame + ETH_HLEN);

    /* Broadcast Ethernet header */
    __builtin_memset(eth->dst, 0xFF, ETH_ALEN); /* broadcast */
    __builtin_memcpy(eth->src, _vnet.mac, ETH_ALEN);
    eth->ethertype = _net_htons(ETH_P_ARP);

    /* Gratuitous ARP: who-has our_ip, tell our_ip */
    arp->hw_type    = _net_htons(ARP_HW_ETHER);
    arp->proto_type = _net_htons(ETH_P_IP);
    arp->hw_len     = ETH_ALEN;
    arp->proto_len  = 4;
    arp->opcode     = _net_htons(ARP_OP_REQUEST);
    __builtin_memcpy(arp->sender_mac, _vnet.mac, ETH_ALEN);
    __builtin_memcpy(arp->sender_ip, _vnet.our_ip, 4);
    __builtin_memset(arp->target_mac, 0x00, ETH_ALEN);
    __builtin_memcpy(arp->target_ip, _vnet.our_ip, 4);

    _vnet_send_frame(frame, sizeof(frame));
    serial_puts("[net] Gratuitous ARP sent\r\n");
}

/* -----------------------------------------------------------
 * _vnet_send_arp_request — ARP who-has for a specific IP
 * ----------------------------------------------------------- */
static void _vnet_send_arp_request(const uint8_t *target_ip)
{
    uint8_t frame[ETH_HLEN + sizeof(struct arp_pkt)];
    struct eth_hdr *eth = (struct eth_hdr *)frame;
    struct arp_pkt *arp = (struct arp_pkt *)(frame + ETH_HLEN);

    __builtin_memset(eth->dst, 0xFF, ETH_ALEN);
    __builtin_memcpy(eth->src, _vnet.mac, ETH_ALEN);
    eth->ethertype = _net_htons(ETH_P_ARP);

    arp->hw_type    = _net_htons(ARP_HW_ETHER);
    arp->proto_type = _net_htons(ETH_P_IP);
    arp->hw_len     = ETH_ALEN;
    arp->proto_len  = 4;
    arp->opcode     = _net_htons(ARP_OP_REQUEST);
    __builtin_memcpy(arp->sender_mac, _vnet.mac, ETH_ALEN);
    __builtin_memcpy(arp->sender_ip, _vnet.our_ip, 4);
    __builtin_memset(arp->target_mac, 0x00, ETH_ALEN);
    __builtin_memcpy(arp->target_ip, target_ip, 4);

    _vnet_send_frame(frame, sizeof(frame));
    serial_puts("[net] ARP request sent for ");
    _net_print_ip(target_ip);
    serial_puts("\r\n");
}

/* -----------------------------------------------------------
 * _virtio_net_init — find VirtIO-net on PCI, init driver
 *
 * Scans PCI for vendor 0x1AF4 with network class (02.00) or
 * device IDs 0x1000 (legacy transitional network).
 *
 * Returns 0 on success, negative errno on failure.
 * ----------------------------------------------------------- */
static int _virtio_net_init(void)
{
    if (_vnet.initialized) return 0;

    /* Ensure PCI cache is populated */
    if (_pci_cache_count < 0) _pci_scan();

    /* Find VirtIO-net device:
     *   VirtIO vendor = 0x1AF4
     *   Legacy device IDs: 0x1000 (net), 0x1041 (modern net)
     *   Or any 0x1AF4 device with class=02 (network controller)
     */
    int net_idx = -1;
    for (int i = 0; i < _pci_cache_count; i++) {
        if (_pci_cache[i].vendor == 0x1AF4) {
            /* VirtIO vendor — check if it's a network device */
            if (_pci_cache[i].cls == 0x02 ||
                _pci_cache[i].devid == 0x1000 ||
                _pci_cache[i].devid == 0x1041) {
                net_idx = i;
                break;
            }
        }
    }

    if (net_idx < 0) {
        serial_puts("[net] No VirtIO-net device found on PCI bus\r\n");
        serial_puts("[net] PCI devices:\r\n");
        for (int i = 0; i < _pci_cache_count; i++) {
            serial_puts("[net]   ");
            serial_put_hex(_pci_cache[i].bus); serial_puts(":");
            serial_put_hex(_pci_cache[i].dev); serial_puts(".");
            serial_put_hex(_pci_cache[i].func);
            serial_puts(" vendor="); serial_put_hex(_pci_cache[i].vendor);
            serial_puts(" device="); serial_put_hex(_pci_cache[i].devid);
            serial_puts(" class="); serial_put_hex(_pci_cache[i].cls);
            serial_puts("."); serial_put_hex(_pci_cache[i].sub);
            serial_puts("\r\n");
        }
        return -19; /* ENODEV */
    }

    serial_puts("[net] Found VirtIO-net at PCI ");
    serial_put_hex(_pci_cache[net_idx].bus); serial_puts(":");
    serial_put_hex(_pci_cache[net_idx].dev); serial_puts(".");
    serial_put_hex(_pci_cache[net_idx].func);
    serial_puts(" (vendor="); serial_put_hex(_pci_cache[net_idx].vendor);
    serial_puts(" device="); serial_put_hex(_pci_cache[net_idx].devid);
    serial_puts(")\r\n");

    /* Step 1: Read BAR0 — must be an I/O BAR for legacy VirtIO */
    uint32_t pci_addr = 0x80000000
        | ((uint32_t)_pci_cache[net_idx].bus << 16)
        | ((uint32_t)_pci_cache[net_idx].dev << 11)
        | 0x10; /* BAR0 offset in PCI config */
    outl(0xCF8, pci_addr);
    uint32_t bar0 = inl(0xCFC);

    if (!(bar0 & 1)) {
        serial_puts("[net] BAR0 is MMIO, not I/O — not legacy VirtIO\r\n");
        serial_puts("[net] BAR0 raw = ");
        serial_put_hex(bar0);
        serial_puts("\r\n");
        return -19;
    }

    _vnet.iobase = (uint16_t)(bar0 & ~0x3u);
    serial_puts("[net] BAR0 I/O base = 0x");
    serial_put_hex(_vnet.iobase);
    serial_puts("\r\n");

    /* Enable bus mastering + I/O space in PCI command register */
    uint32_t cmd_addr = 0x80000000
        | ((uint32_t)_pci_cache[net_idx].bus << 16)
        | ((uint32_t)_pci_cache[net_idx].dev << 11)
        | 0x04;
    outl(0xCF8, cmd_addr);
    uint32_t cmd_reg = inl(0xCFC);
    cmd_reg |= (1 << 0) | (1 << 2); /* I/O Space + Bus Master */
    outl(0xCF8, cmd_addr);
    outl(0xCFC, cmd_reg);

    /* Step 2: Reset device */
    _vnet_wr8(0x12, 0);
    /* Small delay for reset to take effect */
    for (volatile int i = 0; i < 10000; i++) {}

    /* Step 3: Acknowledge */
    _vnet_wr8(0x12, VIRTIO_STATUS_ACK);

    /* Step 4: Driver */
    _vnet_wr8(0x12, VIRTIO_STATUS_ACK | VIRTIO_STATUS_DRIVER);

    /* Step 5: Negotiate features */
    uint32_t host_features = _vnet_rd32(0x00);
    serial_puts("[net] Host features: 0x");
    serial_put_hex(host_features);
    serial_puts("\r\n");

    /* We only need MAC read capability */
    uint32_t guest_features = 0;
    if (host_features & VIRTIO_NET_F_MAC)
        guest_features |= VIRTIO_NET_F_MAC;
    if (host_features & VIRTIO_NET_F_STATUS)
        guest_features |= VIRTIO_NET_F_STATUS;
    _vnet_wr32(0x04, guest_features);

    /* Step 6: Features OK (for legacy, set DRIVER_OK which includes this) */
    uint8_t status = _vnet_rd8(0x12);
    _vnet_wr8(0x12, status | VIRTIO_STATUS_FEATURES_OK);

    /* Verify features were accepted */
    status = _vnet_rd8(0x12);
    if (!(status & VIRTIO_STATUS_FEATURES_OK)) {
        serial_puts("[net] Features not accepted by device\r\n");
        _vnet_wr8(0x12, VIRTIO_STATUS_FAILED);
        return -5;
    }

    /* Step 7: Read MAC address from BAR0 + 0x14..0x19 */
    for (int i = 0; i < 6; i++) {
        _vnet.mac[i] = _vnet_rd8(0x14 + (uint16_t)i);
    }
    serial_puts("[net] MAC address: ");
    _net_print_mac(_vnet.mac);
    serial_puts("\r\n");

    /* Step 8: Set up RX queue (queue 0) */
    if (_vnet_setup_queue(0, &_vnet.rx_qsize,
                          &_vnet.rx_desc, &_vnet.rx_avail, &_vnet.rx_used) < 0) {
        _vnet_wr8(0x12, VIRTIO_STATUS_FAILED);
        return -12;
    }

    /* Allocate RX buffers (contiguous block) */
    _vnet.rx_buffers = (uint8_t *)nvme_alloc_aligned(
        (size_t)_vnet.rx_qsize * VIRTIO_NET_BUF_SIZE, 4096);
    if (!_vnet.rx_buffers) {
        serial_puts("[net] Failed to allocate RX buffers\r\n");
        _vnet_wr8(0x12, VIRTIO_STATUS_FAILED);
        return -12;
    }
    __builtin_memset(_vnet.rx_buffers, 0, (size_t)_vnet.rx_qsize * VIRTIO_NET_BUF_SIZE);

    /* Step 9: Set up TX queue (queue 1) */
    if (_vnet_setup_queue(1, &_vnet.tx_qsize,
                          &_vnet.tx_desc, &_vnet.tx_avail, &_vnet.tx_used) < 0) {
        _vnet_wr8(0x12, VIRTIO_STATUS_FAILED);
        return -12;
    }

    /* Allocate TX buffers */
    _vnet.tx_buffers = (uint8_t *)nvme_alloc_aligned(
        (size_t)_vnet.tx_qsize * VIRTIO_NET_BUF_SIZE, 4096);
    if (!_vnet.tx_buffers) {
        serial_puts("[net] Failed to allocate TX buffers\r\n");
        _vnet_wr8(0x12, VIRTIO_STATUS_FAILED);
        return -12;
    }
    __builtin_memset(_vnet.tx_buffers, 0, (size_t)_vnet.tx_qsize * VIRTIO_NET_BUF_SIZE);
    _vnet.tx_last_used = 0;
    _vnet.tx_next_desc = 0;

    /* Step 10: Set our IP address (QEMU user-mode default) */
    _vnet.our_ip[0] = 10; _vnet.our_ip[1] = 0;
    _vnet.our_ip[2] = 2;  _vnet.our_ip[3] = 15;
    _vnet.gateway_ip[0] = 10; _vnet.gateway_ip[1] = 0;
    _vnet.gateway_ip[2] = 2;  _vnet.gateway_ip[3] = 2;

    /* Step 11: Set DRIVER_OK *before* filling RX queue.
     * The VirtIO spec says the device MUST NOT process virtqueue entries
     * until DRIVER_OK is set. If we fill the RX queue first and then set
     * DRIVER_OK, the device never sees the already-posted buffers because
     * there is no new notification after the status change.
     * Fix: set DRIVER_OK first, then fill RX buffers and notify. */
    status = _vnet_rd8(0x12);
    _vnet_wr8(0x12, status | VIRTIO_STATUS_DRIVER_OK);

    _vnet.initialized = 1;
    _vnet.rx_count = 0;
    _vnet.tx_count = 0;
    _vnet.arp_replies = 0;
    _vnet.icmp_replies = 0;

    /* Now fill RX queue — device is live and will see the notify */
    _vnet_rx_fill();

    serial_puts("[net] VirtIO-net initialized: MAC=");
    _net_print_mac(_vnet.mac);
    serial_puts(" IP=");
    _net_print_ip(_vnet.our_ip);
    serial_puts(" GW=");
    _net_print_ip(_vnet.gateway_ip);
    serial_puts("\r\n");

    /* Send gratuitous ARP so QEMU learns our MAC */
    _vnet_send_gratuitous_arp();

    /* Also ARP for the gateway to trigger QEMU's ARP response */
    _vnet_send_arp_request(_vnet.gateway_ip);

    return 0;
}

/* -----------------------------------------------------------
 * _virtio_net_get_stats — print network statistics
 * ----------------------------------------------------------- */
static void _virtio_net_get_stats(void)
{
    serial_puts("[net] Stats: rx=");
    serial_put_dec(_vnet.rx_count);
    serial_puts(" tx=");
    serial_put_dec(_vnet.tx_count);
    serial_puts(" arp_replies=");
    serial_put_dec(_vnet.arp_replies);
    serial_puts(" icmp_replies=");
    serial_put_dec(_vnet.icmp_replies);
    serial_puts("\r\n");
}

/* ===================================================================
 * 8b. Bare-metal syscall stub
 *
 * On bare-metal, there is no kernel to syscall into. This stub handles
 * the syscall IDs that make sense on bare-metal (DebugWrite for serial)
 * and returns -ENOSYS for everything else. This allows POSIX layer code
 * to be compiled and linked without crashing on import.
 * =================================================================== */

int64_t _pci_enumerate(uint64_t mode, uint64_t index, uint64_t buf_addr);

int64_t userlib__syscall_raw__syscall(uint64_t id, uint64_t a0, uint64_t a1,
                                       uint64_t a2, uint64_t a3, uint64_t a4)
{
    (void)a3; (void)a4;
    switch (id) {
        case 0:  /* Exit */
            outb(0xf4, (uint8_t)((a0 << 1) | 1)); /* isa-debug-exit */
            for (;;) __asm__ volatile("cli; hlt");
            return 0;
        case 4:  /* GetPid */
            return 1; /* bare-metal: PID 1 */
        case 60: /* DebugWrite */
            serial_putchar((char)(a0 & 0xFF));
            return 0;
        case 80: /* DevEnumerate — PCI bus scan via direct port I/O */
            return _pci_enumerate(a0, a1, a2);
        case 82: /* DeviceGrant — read PCI BAR0 via _pci_enumerate mode 5 */
            return _pci_enumerate(5, a0, 0);
        case 83: { /* MapBar — identity map on baremetal (no-op, return same addr) */
            return (int64_t)a0; /* On baremetal, phys == virt (identity mapped) */
        }
        case 84: { /* AllocDma — allocate DMA buffer (use heap) */
            uint64_t size = a0;
            void *p = malloc(size);
            if (!p) return -12; /* ENOMEM */
            return (int64_t)(uintptr_t)p; /* Return virtual address (= physical on identity map) */
        }
        case 85: /* NvmeReadSector: a0=device_idx, a1=lba, a2=buf_addr */
            return _nvme_read_sector(a0, a1, a2);
        case 86: /* NvmeInit: initialize NVMe controller + read sector 0 for diag */
            return (int64_t)_nvme_init_and_read_sector0();
        case 87: /* Fat32Init: parse BPB and initialize FAT32 state */
            return (int64_t)_fat32_init();
        case 88: /* Fat32ReadFile: a0=name_ptr, a1=buf_ptr, a2=max_size */
            return _fat32_read_file_syscall(a0, a1, a2);
        case 89: /* Fat32ListDir: list root directory entries to serial */
            return (int64_t)fat32_list_dir();
        case 90: /* NetInit: initialize VirtIO-net, set IP 10.0.2.15 */
            return (int64_t)_virtio_net_init();
        case 91: /* NetPoll: process incoming frames (ARP/ICMP auto-reply) */
            return (int64_t)_virtio_net_poll();
        case 92: /* NetSendFrame: a0=buf_addr, a1=frame_len (raw Ethernet) */
            return (int64_t)_vnet_send_frame((const void *)(uintptr_t)a0,
                                              (uint16_t)a1);
        case 93: /* NetStats: print network statistics to serial */
            _virtio_net_get_stats();
            return 0;
        default:
            return -38; /* ENOSYS */
    }
}

/* ===================================================================
 * PCI enumeration via direct port I/O (syscall 80 handler)
 *
 * _pci_cache[] and _pci_scan() are defined in section 8a-pci above.
 *
 * Mode 0 (a0=0): Count PCI devices. Returns device count.
 * Mode 1 (a0=1): Get device info at index a1 into DeviceInfoBuf at a2.
 *                 DeviceInfoBuf layout (from device_mem_types.spl):
 *                   offset 0:  u8  bus
 *                   offset 1:  u8  device
 *                   offset 2:  u8  func
 *                   offset 3:  u8  padding
 *                   offset 4:  u16 vendor_id
 *                   offset 6:  u16 device_id
 *                   offset 8:  u8  class_code
 *                   offset 9:  u8  subclass
 *                   offset 10: u8  prog_if
 *                   offset 11: u8  header_type
 *                   offset 12: u8  irq_line
 * =================================================================== */

int64_t _pci_enumerate(uint64_t mode, uint64_t index, uint64_t buf_addr)
{
    if (_pci_cache_count < 0) _pci_scan();

    if (mode == 0) {
        /* Mode 0: return device count */
        return (int64_t)_pci_cache_count;
    }
    if (mode == 1) {
        /* Mode 1: fill DeviceInfoBuf at buf_addr for device[index] */
        if ((int)index >= _pci_cache_count) return -22; /* EINVAL */
        uint8_t *buf = (uint8_t *)(uintptr_t)buf_addr;
        int i = (int)index;
        buf[0] = _pci_cache[i].bus;
        buf[1] = _pci_cache[i].dev;
        buf[2] = _pci_cache[i].func;
        buf[3] = 0; /* padding */
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
        /* Mode 2: return packed device info for device[index] — no buffer needed.
         * Return value layout (i64):
         *   bits [7:0]   = bus
         *   bits [15:8]  = device
         *   bits [23:16] = func
         *   bits [31:24] = class_code
         *   bits [39:32] = subclass
         *   bits [55:40] = vendor_id
         *   bits [63:56] = 0 (reserved)
         * Second call with mode 3 returns device_id + extras:
         *   bits [15:0]  = device_id
         *   bits [23:16] = prog_if
         *   bits [31:24] = irq_line
         */
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
        /* Mode 3: return device_id + extras for device[index] */
        if ((int)index >= _pci_cache_count) return -22;
        int i = (int)index;
        return (int64_t)(
            ((uint64_t)_pci_cache[i].devid) |
            ((uint64_t)_pci_cache[i].progif << 16) |
            ((uint64_t)_pci_cache[i].irq << 24)
        );
    }
    if (mode == 4) {
        /* Mode 4: return single field for device[index].
         * buf_addr = field selector:
         *   0=bus, 1=device, 2=func, 3=class, 4=subclass, 5=vendor, 6=devid, 7=irq
         */
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
        /* Mode 5: Read PCI BAR0 for device at index.
         * Returns physical base address of BAR0 (type bits masked off). */
        if ((int)index >= _pci_cache_count) return -22;
        int i = (int)index;
        uint32_t addr = 0x80000000 | ((uint32_t)_pci_cache[i].bus << 16)
                      | ((uint32_t)_pci_cache[i].dev << 11) | 0x10;
        outl(0xCF8, addr);
        uint32_t bar0 = inl(0xCFC);
        if (bar0 & 1) return (int64_t)(bar0 & ~0x3u); /* I/O BAR */
        return (int64_t)(bar0 & ~0xFu); /* Memory BAR */
    }
    return -38; /* ENOSYS */
}

/* Also provide the unmangled name for direct extern fn calls */
int64_t syscall(uint64_t id, uint64_t a0, uint64_t a1,
                uint64_t a2, uint64_t a3, uint64_t a4)
{
    return userlib__syscall_raw__syscall(id, a0, a1, a2, a3, a4);
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
    bga_write(0x06, (uint16_t)w);    /* VIRT_WIDTH = XRES (set pitch) */
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

static void serial_hex(uint64_t v) {
    char hex[] = "0123456789abcdef";
    serial_putchar('0'); serial_putchar('x');
    for (int i = 60; i >= 0; i -= 4)
        serial_putchar(hex[(v >> i) & 0xF]);
}

RuntimeValue rt_gui_set_fb(RuntimeValue addr, RuntimeValue w)
{
    g_fb_addr = (uint64_t)addr;
    g_fb_w = (uint64_t)w;
    /* Ensure BGA VIRT_WIDTH matches XRES so pitch = width * bpp/8 */
    bga_write(0x06, (uint16_t)(uint64_t)w);
    /* Diagnostic: print fb address and width */
    serial_puts("[GUI] fb_addr=0x");
    serial_hex(g_fb_addr);
    serial_puts(" fb_w=");
    serial_hex(g_fb_w);
    serial_puts("\r\n");
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

static void gui_fill(uint32_t x, uint32_t y, uint32_t w, uint32_t h, uint32_t c)
{
    for (uint32_t row = 0; row < h; row++) {
        uint64_t base = g_fb_addr + ((uint64_t)(y + row) * g_fb_w + x) * 4;
        for (uint32_t col = 0; col < w; col++) {
            *(volatile uint32_t *)(uintptr_t)(base + col * 4) = c;
        }
    }
}

/* Full desktop rendering — called from Simple code via extern fn.
 * Draws everything in C to avoid Cranelift stack frame issues. */
RuntimeValue rt_gui_render_desktop(RuntimeValue unused1, RuntimeValue unused2)
{
    (void)unused1; (void)unused2;

    /* Title bar (top) */
    gui_fill(0, 0, 1024, 28, 0x001E1E2E);
    serial_puts("[GUI] title bar\r\n");

    /* Taskbar (bottom) */
    gui_fill(0, 736, 1024, 32, 0x001E1E2E);
    serial_puts("[GUI] taskbar\r\n");

    /* Dock icons */
    gui_fill(10, 742, 20, 20, 0x003498DB);
    gui_fill(36, 742, 20, 20, 0x0027AE60);
    gui_fill(62, 742, 20, 20, 0x00E74C3C);
    gui_fill(88, 742, 20, 20, 0x00F39C12);
    gui_fill(114, 742, 20, 20, 0x009B59B6);
    gui_fill(944, 742, 70, 20, 0x002C2C3E);
    serial_puts("[GUI] dock\r\n");

    /* Window title bar (blue, 300x24) */
    gui_fill(200, 100, 300, 24, 0x00007ACC);
    serial_puts("[GUI] win title\r\n");

    /* Close button (red) */
    gui_fill(480, 104, 16, 16, 0x00E74C3C);

    /* Window body (white, 300x120) */
    gui_fill(200, 124, 300, 120, 0x00FFFFFF);
    serial_puts("[GUI] win body\r\n");

    /* "Hello World!" text */
    fb_draw_text(220, 140, "Hello World!", 0x00333333, 0x00FFFFFF);
    serial_puts("[GUI] text\r\n");

    /* RGB blocks (smaller) */
    gui_fill(220, 170, 60, 24, 0x00FF4444);
    gui_fill(290, 170, 60, 24, 0x0044CC44);
    gui_fill(360, 170, 60, 24, 0x004488FF);

    /* Status bar (300x20) */
    gui_fill(200, 224, 300, 20, 0x00E0E0E0);
    fb_draw_text(210, 228, "SimpleOS", 0x00666666, 0x00E0E0E0);
    serial_puts("[GUI] status\r\n");

    serial_puts("[GUI] render complete\r\n");
    return 0;
}

/* ===================================================================
 * 9d. _start — serial init, then spl_start
 * =================================================================== */

/* ===================================================================
 * Additional runtime stubs for OS boot path (PCI, VFS, NVMe)
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

/* Comparison operator — called by <= >= < > on non-trivial values */
RuntimeValue rt_value_compare(RuntimeValue a, RuntimeValue b) {
    /* Simple integer comparison for tagged values */
    int64_t va = (int64_t)a;
    int64_t vb = (int64_t)b;
    if (va < vb) return ENCODE_INT(-1);
    if (va > vb) return ENCODE_INT(1);
    return ENCODE_INT(0);
}

/* rt_native_eq/neq already defined at line ~759 */
RuntimeValue rt_profiler_record_call(RuntimeValue a, RuntimeValue b) { (void)a;(void)b; return NIL_VALUE; }
RuntimeValue rt_profiler_record_return(RuntimeValue a) { (void)a; return NIL_VALUE; }

/* serial_println — called by compiled Simple code (extern fn serial_println) */
RuntimeValue serial_println(RuntimeValue val) {
    rt_print(val);
    serial_puts("\r\n");
    return NIL_VALUE;
}

static void serial_puthex(uint32_t v) {
    static const char hex[] = "0123456789abcdef";
    if (v > 0xFFFF) { serial_putchar(hex[(v>>28)&0xF]); serial_putchar(hex[(v>>24)&0xF]); serial_putchar(hex[(v>>20)&0xF]); serial_putchar(hex[(v>>16)&0xF]); }
    if (v > 0xFF) { serial_putchar(hex[(v>>12)&0xF]); serial_putchar(hex[(v>>8)&0xF]); }
    serial_putchar(hex[(v>>4)&0xF]); serial_putchar(hex[v&0xF]);
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

    /* PCI hardware test — verify devices are visible before entering Simple code */
    {
        if (_pci_cache_count < 0) _pci_scan();
        serial_puts("[BOOT] PCI: ");
        serial_puthex(_pci_cache_count);
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
    }

    /* Read VGA BAR0 and set framebuffer address (PCI bus 0, dev 1, BAR0 at offset 0x10) */
    {
        uint32_t vga_addr = 0x80000000 | (1 << 11) | 0x10;
        outl(0xCF8, vga_addr);
        uint32_t bar0 = inl(0xCFC);
        if (bar0 & 0xFFFFFFF0) {
            g_fb_addr = (uint64_t)(bar0 & 0xFFFFFFF0);
        }
    }

    /* FAT32 file read test — read hello.txt from NVMe disk */
    if (_fat32_init() == 0) {
        serial_puts("[BOOT] FAT32 initialized\r\n");
        fat32_list_dir();
        char fbuf[256];
        __builtin_memset(fbuf, 0, sizeof(fbuf));
        uint32_t bytes_read = 0;
        if (fat32_read_file("hello.txt", (uint8_t *)fbuf, 255, &bytes_read) == 0) {
            fbuf[bytes_read] = '\0';
            serial_puts("[BOOT] hello.txt: ");
            serial_puts(fbuf);
            serial_puts("\r\n");
        } else {
            serial_puts("[BOOT] hello.txt: not found\r\n");
        }
    } else {
        serial_puts("[BOOT] FAT32 init failed\r\n");
    }

    /* VirtIO-net initialization + ARP/ICMP polling test */
    {
        int net_rc = _virtio_net_init();
        if (net_rc == 0) {
            serial_puts("[BOOT] Network initialized: MAC=");
            _net_print_mac(_vnet.mac);
            serial_puts(" IP=10.0.2.15\r\n");

            /* Poll for incoming frames for ~2 seconds.
             * This allows QEMU user-mode networking to:
             *   1. Receive our gratuitous ARP
             *   2. Send ARP requests for 10.0.2.15 (which we reply to)
             *   3. Potentially send ICMP echo requests (which we reply to)
             * The loop processes ARP and ICMP automatically. */
            serial_puts("[BOOT] Polling network for 2 seconds...\r\n");
            int total_frames = 0;
            for (int i = 0; i < 2000; i++) {
                int n = _virtio_net_poll();
                if (n > 0) total_frames += n;
                /* ~1ms delay */
                for (volatile int j = 0; j < 10000; j++) {}
            }
            serial_puts("[BOOT] Network poll done, frames processed: ");
            serial_put_dec(total_frames);
            serial_puts("\r\n");
            _virtio_net_get_stats();
        } else {
            serial_puts("[BOOT] VirtIO-net init failed (rc=");
            serial_put_dec(net_rc);
            serial_puts(") — no network device or not VirtIO\r\n");
        }
    }

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

/* rt_array_new: create a new array with given capacity.
 * Cranelift codegen passes RAW capacity (iconst.i64 N), NOT tagged.
 * Must use raw value, not DECODE_INT. */
RuntimeValue rt_array_new(RuntimeValue cap_val)
{
    int64_t cap = (int64_t)cap_val;  /* RAW — not DECODE_INT */
    if (cap <= 0) cap = 64; /* default capacity — generous for bare metal */
    /* Ensure minimum capacity for OS use (PCI scan needs ~32, string ops need ~16) */
    if (cap < 64) cap = 64;
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

/* rt_array_push: push element, no growth (matching Rust runtime).
 * Returns ENCODE_PTR of same array. If at capacity, item is silently dropped.
 * Callers must pre-allocate sufficient capacity (compiler uses 16 for empty []). */
RuntimeValue rt_array_push(RuntimeValue arr, RuntimeValue val)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    if (a->len >= a->cap) {
        /* At capacity — cannot grow (flexible array member can't be resized in-place).
         * Silently drop. Initial capacity should be large enough for the use case. */
        return ENCODE_PTR(a);
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

/* rt_array_len: return ENCODE_INT — callers expect tagged integer */
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

/* ===================================================================
 * Enum / Optional / Result runtime
 *
 * The compiler generates rt_enum_new / rt_enum_discriminant /
 * rt_enum_payload calls for Optional<T> (PciDevice?, Result, etc.).
 * Without these, --unresolved-symbols=ignore-all resolves them to 0
 * and Optional wrapping silently corrupts pointers.
 * =================================================================== */

/* rt_enum_new(enum_id, discriminant, payload) → heap-allocated RuntimeEnum.
 * Calling convention: (i32, i32, i64) → i64 (ENCODE_PTR).
 * Matches Rust runtime RuntimeEnum layout (24 bytes). */
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

/* rt_enum_discriminant(value) → discriminant as i64 */
RuntimeValue rt_enum_discriminant(RuntimeValue value)
{
    if (!IS_HEAP(value)) return -1;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return -1;
    return (RuntimeValue)(int64_t)e->discriminant;
}

/* rt_enum_payload(value) → payload RuntimeValue */
RuntimeValue rt_enum_payload(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return value;
    return e->payload;
}

/* rt_enum_check_discriminant(value, expected) → 1 if match, 0 otherwise */
RuntimeValue rt_enum_check_discriminant(RuntimeValue value, RuntimeValue expected)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return (e->discriminant == (uint32_t)(int32_t)expected) ? 1 : 0;
}

/* rt_is_none(value) → 1 if nil or None enum, 0 otherwise */
RuntimeValue rt_is_none(RuntimeValue value)
{
    if (IS_NIL(value)) return 1;
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    /* None variant has nil payload */
    return IS_NIL(e->payload) ? 1 : 0;
}

/* rt_is_some(value) → 1 if Some enum (non-nil payload), 0 otherwise */
RuntimeValue rt_is_some(RuntimeValue value)
{
    return rt_is_none(value) ? 0 : 1;
}

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

/* rt_function_not_found — called when cross-module method resolution fails.
 * Prints the unresolved function name to serial and returns NIL.
 * The Cranelift backend calls this with (name_ptr, name_len) when a method
 * cannot be resolved at compile time. */
RuntimeValue rt_function_not_found(RuntimeValue name_ptr, RuntimeValue name_len)
{
    serial_puts("[WARN] unresolved fn: ");
    if (name_ptr) {
        const char *p = (const char *)(uintptr_t)name_ptr;
        int64_t len = (int64_t)name_len;
        for (int64_t i = 0; i < len && i < 128; i++) serial_putchar(p[i]);
    }
    serial_puts("\r\n");
    return NIL_VALUE;
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

/* Port I/O: Cranelift passes RAW (untagged) i64 for extern fn args.
 * PCI enumeration uses kernel syscall 80 (not port I/O), so these
 * are only called for serial I/O and direct hardware access. */

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

/* --- MMIO: real x86_64 implementations (raw i64 args) --- */

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
    uintptr_t a = (uintptr_t)DECODE_INT(addr);
    *(volatile uint16_t *)a = (uint16_t)DECODE_INT(val);
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
