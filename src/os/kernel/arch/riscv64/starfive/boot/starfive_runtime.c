#define RT_RISCV_UART_MMIO32 1
#define SIMPLE_FREESTANDING_RUNTIME_NO_ENTRY 1

__asm__(
    ".section .text.entry,\"ax\",@progbits\n"
    ".globl _start\n"
    "_start:\n"
    "mv s0, a0\n"
    "mv s1, a1\n"
    "la sp, _stack_top\n"
    "la t0, _sbss\n"
    "la t1, _ebss\n"
    "1:\n"
    "bgeu t0, t1, 2f\n"
    "sd zero, 0(t0)\n"
    "addi t0, t0, 8\n"
    "j 1b\n"
    "2:\n"
    "mv a0, s0\n"
    "mv a1, s1\n"
    "call starfive_boot_main\n"
    "3:\n"
    "wfi\n"
    "j 3b\n"
);

#include "../../boot/freestanding_runtime.c"

spl_i64 rt_starfive_uart_read(void) {
    volatile spl_u32 *uart = (volatile spl_u32 *)RT_RISCV_UART_BASE;
    if ((uart[5] & 0x01U) == 0U) return -1;
    return (spl_i64)(uart[0] & 0xffU);
}

spl_u64 rt_starfive_resolve_dtb(spl_u64 candidate) {
    const spl_u8 *dtb = (const spl_u8 *)candidate;
    if (candidate != 0ULL && dtb[0] == 0xd0U && dtb[1] == 0x0dU &&
        dtb[2] == 0xfeU && dtb[3] == 0xedU) return candidate;
    candidate = 0x42200000ULL;
    dtb = (const spl_u8 *)candidate;
    if (dtb[0] == 0xd0U && dtb[1] == 0x0dU && dtb[2] == 0xfeU &&
        dtb[3] == 0xedU) return candidate;
    return 0ULL;
}

spl_i64 rt_string_to_int_lenient(spl_i64 value) {
    RtString *string = rt_as_string(value);
    if (!string) return 0;
    spl_u64 i = 0;
    while (i < string->len && (string->data[i] == ' ' || string->data[i] == '\t' ||
           string->data[i] == '\r' || string->data[i] == '\n')) i = i + 1;
    spl_i64 sign = 1;
    if (i < string->len && (string->data[i] == '-' || string->data[i] == '+')) {
        if (string->data[i] == '-') sign = -1;
        i = i + 1;
    }
    spl_u64 result = 0;
    spl_u64 digits = 0;
    while (i < string->len && string->data[i] >= '0' && string->data[i] <= '9') {
        spl_u64 digit = (spl_u64)(string->data[i] - '0');
        if (result > 922337203685477580ULL ||
            (result == 922337203685477580ULL && digit > (sign < 0 ? 8ULL : 7ULL))) {
            return sign < 0 ? (-9223372036854775807LL - 1LL) : 9223372036854775807LL;
        }
        result = result * 10ULL + digit;
        digits = digits + 1;
        i = i + 1;
    }
    if (digits == 0) return 0;
    if (sign < 0 && result == 9223372036854775808ULL) return (-9223372036854775807LL - 1LL);
    return sign < 0 ? -(spl_i64)result : (spl_i64)result;
}

spl_u64 rt_mem_read_u8(spl_u64 address) {
    return *(volatile const spl_u8 *)address;
}

spl_u64 rt_starfive_mmio_read32(spl_u64 address) {
    __asm__ volatile("fence iorw, iorw" ::: "memory");
    spl_u32 value = *(volatile const spl_u32 *)address;
    __asm__ volatile("fence iorw, iorw" ::: "memory");
    return (spl_u64)value;
}

void rt_starfive_mmio_write32(spl_u64 address, spl_u64 value) {
    __asm__ volatile("fence iorw, iorw" ::: "memory");
    *(volatile spl_u32 *)address = (spl_u32)value;
    __asm__ volatile("fence iorw, iorw" ::: "memory");
}

void rt_starfive_delay_ms(spl_u64 milliseconds) {
    /* U74 time CSR runs at the JH7110 4 MHz timebase used by OpenSBI. */
    spl_u64 start;
    spl_u64 now;
    __asm__ volatile("rdtime %0" : "=r"(start));
    do {
        __asm__ volatile("rdtime %0" : "=r"(now));
    } while ((now - start) < (milliseconds * 4000ULL));
}

/* Bare-metal service fallback: there is no userspace syscall ABI in this
 * single-image StarFive lane, so common drivers fall through to their explicit
 * runtime providers. */
spl_i64 syscall(spl_u64 id, spl_u64 arg0, spl_u64 arg1, spl_u64 arg2,
                spl_u64 arg3, spl_u64 arg4) {
    (void)id; (void)arg0; (void)arg1; (void)arg2; (void)arg3; (void)arg4;
    return -38;
}

#define STARFIVE_DMA_PAGE_SIZE 4096ULL
#define STARFIVE_DMA_POOL_SIZE (1024ULL * 1024ULL)
#define STARFIVE_DMA_SLOT_COUNT 32
#define JH7110_CCACHE_BASE 0x02010000ULL
#define JH7110_CCACHE_FLUSH64 (JH7110_CCACHE_BASE + 0x200ULL)
#define JH7110_CCACHE_LINE_SIZE 64ULL

static spl_u8 g_starfive_dma_pool[STARFIVE_DMA_POOL_SIZE]
    __attribute__((aligned(STARFIVE_DMA_PAGE_SIZE)));
static spl_u64 g_starfive_dma_used;
struct starfive_dma_slot {
    spl_u8 *address;
    spl_u64 size;
    int active;
};
static struct starfive_dma_slot g_starfive_dma_slots[STARFIVE_DMA_SLOT_COUNT];

static spl_u64 starfive_align_up(spl_u64 value, spl_u64 alignment) {
    return (value + alignment - 1ULL) & ~(alignment - 1ULL);
}

static void starfive_ccache_flush_range(spl_u64 start, spl_u64 size) {
    if (size == 0ULL) return;
    spl_u64 line = start & ~(JH7110_CCACHE_LINE_SIZE - 1ULL);
    const spl_u64 end = start + size;
    volatile spl_u64 *flush64 = (volatile spl_u64 *)JH7110_CCACHE_FLUSH64;
    __asm__ volatile("fence rw, rw" ::: "memory");
    while (line < end) {
        *flush64 = line;
        line += JH7110_CCACHE_LINE_SIZE;
    }
    __asm__ volatile("fence rw, rw" ::: "memory");
}

spl_i64 rt_dma_alloc(spl_i64 size, int direction) {
    (void)direction;
    if (size <= 0) return -1;
    const spl_u64 rounded = starfive_align_up((spl_u64)size, STARFIVE_DMA_PAGE_SIZE);
    if (rounded > STARFIVE_DMA_POOL_SIZE - g_starfive_dma_used) return -1;
    int slot = -1;
    for (int index = 0; index < STARFIVE_DMA_SLOT_COUNT; index++) {
        if (!g_starfive_dma_slots[index].active) { slot = index; break; }
    }
    if (slot < 0) return -1;
    spl_u8 *address = &g_starfive_dma_pool[g_starfive_dma_used];
    g_starfive_dma_used += rounded;
    g_starfive_dma_slots[slot].address = address;
    g_starfive_dma_slots[slot].size = rounded;
    g_starfive_dma_slots[slot].active = 1;
    for (spl_u64 offset = 0; offset < rounded; offset++) address[offset] = 0;
    starfive_ccache_flush_range((spl_u64)address, rounded);
    return (spl_i64)slot;
}

spl_i64 rt_dma_virt_of(spl_i64 handle) {
    if (handle < 0 || handle >= STARFIVE_DMA_SLOT_COUNT ||
        !g_starfive_dma_slots[handle].active) return 0;
    return (spl_i64)(spl_u64)g_starfive_dma_slots[handle].address;
}

spl_i64 rt_dma_phys_of(spl_i64 handle) {
    return rt_dma_virt_of(handle); /* OpenSBI S-mode boot retains identity map. */
}

void rt_dma_sync_for_device(spl_i64 handle, int direction) {
    (void)direction;
    if (handle < 0 || handle >= STARFIVE_DMA_SLOT_COUNT ||
        !g_starfive_dma_slots[handle].active) return;
    starfive_ccache_flush_range((spl_u64)g_starfive_dma_slots[handle].address,
                                g_starfive_dma_slots[handle].size);
}

void rt_dma_sync_for_cpu(spl_i64 handle, int direction) {
    rt_dma_sync_for_device(handle, direction);
}

spl_i64 rt_dma_cache_line_size(void) {
    return (spl_i64)JH7110_CCACHE_LINE_SIZE;
}

spl_i64 rt_string_new_literal(const spl_u8 *bytes, spl_u64 len) {
    return rt_string_new((spl_i64)(spl_u64)bytes, (spl_i64)len);
}

spl_i64 rt_value_unbox_int(spl_i64 value) {
    if ((((spl_u64)value) & RT_VALUE_TAG_MASK) == RT_VALUE_TAG_INT) {
        return value >> 3;
    }
    if (value == rt_special(RT_VALUE_SPECIAL_TRUE)) return 1;
    if (value == rt_special(RT_VALUE_SPECIAL_FALSE)) return 0;
    return value;
}

spl_i64 rt_native_cmp(spl_i64 left, spl_i64 right) {
    RtString *a = rt_as_string(left);
    RtString *b = rt_as_string(right);
    if (a && b) {
        spl_u64 common = a->len < b->len ? a->len : b->len;
        for (spl_u64 i = 0; i < common; i = i + 1) {
            if (a->data[i] < b->data[i]) return -1;
            if (a->data[i] > b->data[i]) return 1;
        }
        if (a->len < b->len) return -1;
        if (a->len > b->len) return 1;
        return 0;
    }
    if (left < right) return -1;
    if (left > right) return 1;
    return 0;
}

spl_i64 rt_enum_id(spl_i64 value) {
    RtEnum *e = rt_as_enum(value);
    return e ? (spl_i64)e->enum_id : -1;
}

spl_i64 rt_unwrap_or_trap(spl_i64 value) {
    RtEnum *e = rt_as_enum(value);
    if (!e) return value;
    if (e->enum_id == 1U && (e->discriminant == 0U || e->discriminant == 4053299545U)) {
        return e->payload;
    }
    if (e->discriminant == 2405352012U) return e->payload;
    for (;;) {
        __asm__ volatile("wfi");
    }
    return rt_nil();
}
