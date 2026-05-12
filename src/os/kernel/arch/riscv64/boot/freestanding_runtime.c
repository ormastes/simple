/* RISC-V freestanding runtime bridge.
 *
 * This file is compiled as a boot object by native-build for the RV64 entry.
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;

extern spl_i64 kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(spl_i64 size);

void *rt_alloc(spl_i64 size) {
    if (size <= 0) {
        return (void *)0;
    }
    return (void *)(spl_u64)kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(size);
}

void rt_free(void *ptr) {
    (void)ptr;
}

void *rt_memcpy(void *dst, const void *src, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = s[i];
    }
    return dst;
}

void *rt_memset(void *dst, signed char val, spl_i64 n) {
    unsigned char *d = (unsigned char *)dst;
    if (n <= 0) {
        return dst;
    }
    for (spl_i64 i = 0; i < n; i = i + 1) {
        d[i] = (unsigned char)val;
    }
    return dst;
}
