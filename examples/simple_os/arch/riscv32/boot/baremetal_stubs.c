/*
 * baremetal_stubs.c -- RISC-V 32 baremetal runtime stubs
 *
 * Provides heap allocator (malloc/free/realloc/calloc), rt_alloc,
 * memory primitives (memcpy/memset/memmove/memcmp/strlen),
 * and rt_framebuffer_copy for the Simple runtime on bare metal.
 *
 * NOTE: On RV32, pointers are 32-bit. The heap is 4MB (not 16MB)
 * to fit in typical RV32 QEMU virt RAM (128MB at 0x80000000).
 */

#include <stddef.h>
#include <stdint.h>

/* ================================================================
 * Heap allocator -- 4MB bump allocator, 16-byte aligned
 * (Smaller than 64-bit targets to fit RV32 memory constraints)
 * ================================================================ */

static char _heap[4 * 1024 * 1024]; /* 4 MB */
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

void *realloc(void *ptr, size_t old_size, size_t new_size) {
    void *new_ptr = malloc(new_size);
    if (ptr && new_ptr) {
        size_t copy = old_size < new_size ? old_size : new_size;
        __builtin_memcpy(new_ptr, ptr, copy);
    }
    return new_ptr;
}

void *calloc(size_t n, size_t size) {
    size_t total = n * size;
    void *ptr = malloc(total);
    if (ptr) __builtin_memset(ptr, 0, total);
    return ptr;
}

/* ================================================================
 * Simple runtime allocator -- rt_alloc
 * ================================================================ */

void *rt_alloc(int64_t size) {
    return malloc((size_t)size);
}

/* ================================================================
 * Memory primitives -- required by compiler-generated code
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

/* ================================================================
 * Framebuffer bulk copy -- rt_framebuffer_copy
 *
 * On RV32 the framebuffer address is passed as uint64_t but
 * truncated to 32-bit uintptr_t for MMIO access.
 * ================================================================ */

void rt_framebuffer_copy(uint64_t dst_addr, int64_t *src, uint32_t count) {
    volatile uint32_t *dst = (volatile uint32_t *)(uintptr_t)dst_addr;
    for (uint32_t i = 0; i < count; i++) {
        dst[i] = (uint32_t)src[i];
    }
}

/* ================================================================
 * MMIO Accessors — required by os.kernel.boot.mmio
 *
 * All addresses passed as uint64_t but truncated to 32-bit on RV32.
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
    volatile uint32_t *p = (volatile uint32_t *)(uintptr_t)addr;
    p[0] = (uint32_t)val;
    p[1] = (uint32_t)(val >> 32);
}

uint64_t rt_mmio_read_u64(uint64_t addr) {
    volatile uint32_t *p = (volatile uint32_t *)(uintptr_t)addr;
    return (uint64_t)p[0] | ((uint64_t)p[1] << 32);
}

/* ================================================================
 * Simple Runtime — String/Array/Comparison Stubs
 *
 * Minimal implementations for baremetal. Strings are stored as
 * {length, data[]} structs in heap memory.
 * ================================================================ */

/* Tagged value layout (Simple runtime ABI):
 *   i64 value where:
 *     - integers: raw i64
 *     - strings: pointer to {i64 len, char data[]}
 *     - arrays: pointer to {i64 len, i64 cap, i64 data[]}
 *     - nil: 0
 */

typedef struct {
    int64_t len;
    char data[];
} SimpleString;

typedef struct {
    int64_t len;
    int64_t cap;
    int64_t data[];
} SimpleArray;

int64_t rt_string_new(const char *data, int64_t len) {
    SimpleString *s = (SimpleString *)malloc(sizeof(SimpleString) + (size_t)len + 1);
    if (!s) return 0;
    s->len = len;
    for (int64_t i = 0; i < len; i++) s->data[i] = data[i];
    s->data[len] = 0;
    return (int64_t)(uintptr_t)s;
}

int64_t rt_array_new(int64_t initial_cap) {
    if (initial_cap < 4) initial_cap = 4;
    SimpleArray *a = (SimpleArray *)malloc(sizeof(SimpleArray) + (size_t)initial_cap * sizeof(int64_t));
    if (!a) return 0;
    a->len = 0;
    a->cap = initial_cap;
    return (int64_t)(uintptr_t)a;
}

void rt_array_push(int64_t *arr_ptr, int64_t value) {
    SimpleArray *a = (SimpleArray *)(uintptr_t)(*arr_ptr);
    if (!a) return;
    if (a->len >= a->cap) {
        int64_t new_cap = a->cap * 2;
        SimpleArray *na = (SimpleArray *)malloc(sizeof(SimpleArray) + (size_t)new_cap * sizeof(int64_t));
        if (!na) return;
        na->len = a->len;
        na->cap = new_cap;
        for (int64_t i = 0; i < a->len; i++) na->data[i] = a->data[i];
        *arr_ptr = (int64_t)(uintptr_t)na;
        a = na;
    }
    a->data[a->len++] = value;
}

int64_t rt_len(int64_t obj) {
    if (!obj) return 0;
    /* Check if it looks like a SimpleString or SimpleArray —
     * both have len as first field */
    SimpleString *s = (SimpleString *)(uintptr_t)obj;
    return s->len;
}

int64_t rt_string_char_at(int64_t str, int64_t idx) {
    if (!str) return 0;
    SimpleString *s = (SimpleString *)(uintptr_t)str;
    if (idx < 0 || idx >= s->len) return 0;
    return (int64_t)(uint8_t)s->data[idx];
}

int64_t rt_string_concat(int64_t a, int64_t b) {
    SimpleString *sa = (SimpleString *)(uintptr_t)a;
    SimpleString *sb = (SimpleString *)(uintptr_t)b;
    int64_t la = sa ? sa->len : 0;
    int64_t lb = sb ? sb->len : 0;
    SimpleString *r = (SimpleString *)malloc(sizeof(SimpleString) + (size_t)(la + lb) + 1);
    if (!r) return 0;
    r->len = la + lb;
    for (int64_t i = 0; i < la; i++) r->data[i] = sa->data[i];
    for (int64_t i = 0; i < lb; i++) r->data[la + i] = sb->data[i];
    r->data[la + lb] = 0;
    return (int64_t)(uintptr_t)r;
}

/* Convert an i64 to decimal string */
static int64_t _i64_to_string(int64_t val) {
    char buf[21];
    int neg = 0;
    int pos = 20;
    buf[pos] = 0;
    if (val < 0) { neg = 1; val = -val; }
    if (val == 0) { buf[--pos] = '0'; }
    else {
        while (val > 0) { buf[--pos] = '0' + (int)(val % 10); val /= 10; }
    }
    if (neg) buf[--pos] = '-';
    return rt_string_new(&buf[pos], 20 - pos);
}

int64_t rt_value_to_string(int64_t val) {
    return _i64_to_string(val);
}

int64_t rt_native_eq(int64_t a, int64_t b) {
    return a == b ? 1 : 0;
}

int64_t rt_native_neq(int64_t a, int64_t b) {
    return a != b ? 1 : 0;
}

/* ================================================================
 * Compiler builtins — 64-bit div/mod on 32-bit RISC-V
 *
 * These are normally provided by libgcc/compiler-rt but are not
 * available in freestanding mode.
 * ================================================================ */

int64_t __divdi3(int64_t a, int64_t b) {
    if (b == 0) return 0;
    int neg = 0;
    uint64_t ua = (uint64_t)a, ub = (uint64_t)b;
    if (a < 0) { neg = !neg; ua = (uint64_t)(-a); }
    if (b < 0) { neg = !neg; ub = (uint64_t)(-b); }
    uint64_t q = 0, r = 0;
    for (int i = 63; i >= 0; i--) {
        r = (r << 1) | ((ua >> i) & 1);
        if (r >= ub) { r -= ub; q |= ((uint64_t)1 << i); }
    }
    return neg ? -(int64_t)q : (int64_t)q;
}

int64_t __moddi3(int64_t a, int64_t b) {
    if (b == 0) return 0;
    return a - __divdi3(a, b) * b;
}
