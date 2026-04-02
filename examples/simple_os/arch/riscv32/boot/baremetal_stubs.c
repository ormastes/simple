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
