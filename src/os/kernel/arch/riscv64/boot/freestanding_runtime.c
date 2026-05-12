/* RISC-V freestanding runtime bridge.
 *
 * This file is compiled as a boot object by native-build for the RV64 entry.
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;

__asm__(
    ".section .text.entry,\"ax\",@progbits\n"
    ".globl _start\n"
    "_start:\n"
    "j spl_start\n"
);

extern spl_i64 kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(spl_i64 size) __attribute__((weak));

static spl_u64 g_freestanding_heap_next = 0x87000000ULL;
static spl_u64 g_freestanding_heap_limit = 0x88000000ULL;

static spl_u64 rt_align8(spl_u64 value) {
    return (value + 7ULL) & ~7ULL;
}

void *rt_alloc(spl_i64 size) {
    spl_u64 next;
    spl_u64 bytes;
    if (size <= 0) {
        return (void *)0;
    }
    if (kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc) {
        return (void *)(spl_u64)kernel__boot__riscv_noalloc_heap__riscv_noalloc_heap_alloc(size);
    }
    bytes = rt_align8((spl_u64)size);
    next = rt_align8(g_freestanding_heap_next);
    if (next + bytes > g_freestanding_heap_limit) {
        return (void *)0;
    }
    g_freestanding_heap_next = next + bytes;
    return (void *)next;
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

spl_i64 rt_native_eq(spl_i64 lhs, spl_i64 rhs) {
    return lhs == rhs ? 1 : 0;
}

spl_i64 rt_native_neq(spl_i64 lhs, spl_i64 rhs) {
    return lhs != rhs ? 1 : 0;
}

spl_i64 rt_mmio_read_u8(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned char *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u16(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned short *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u32(spl_i64 addr) {
    return (spl_i64)(*(volatile unsigned int *)(spl_u64)addr);
}

spl_i64 rt_mmio_read_u64(spl_i64 addr) {
    return (spl_i64)(*(volatile spl_u64 *)(spl_u64)addr);
}

void rt_mmio_write_u8(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned char *)(spl_u64)addr = (unsigned char)value;
}

void rt_mmio_write_u16(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned short *)(spl_u64)addr = (unsigned short)value;
}

void rt_mmio_write_u32(spl_i64 addr, spl_i64 value) {
    *(volatile unsigned int *)(spl_u64)addr = (unsigned int)value;
}

void rt_mmio_write_u64(spl_i64 addr, spl_i64 value) {
    *(volatile spl_u64 *)(spl_u64)addr = (spl_u64)value;
}

void log_raw_println(spl_i64 msg) {
    (void)msg;
}

spl_i64 rt_pci_device_count(void) {
    return 0;
}

spl_i64 rt_pci_get_field(spl_i64 index, spl_i64 field) {
    (void)index;
    (void)field;
    return -1;
}

spl_i64 rt_net_init(void) {
    return -1;
}

spl_i64 rt_net_tx_test(void) {
    return -1;
}

spl_i64 rt_net_stats(void) {
    return -1;
}

spl_i64 rt_display_init(void) {
    return -1;
}

spl_i64 rt_display_flush_test(void) {
    return -1;
}

spl_i64 rt_display_width(void) {
    return 0;
}

spl_i64 rt_display_height(void) {
    return 0;
}
