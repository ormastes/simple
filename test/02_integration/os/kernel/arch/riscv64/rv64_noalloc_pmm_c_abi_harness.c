#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int64_t rt_riscv_noalloc_pmm_init(uint64_t, uint64_t, uint64_t, uint64_t);
extern int64_t rt_riscv_noalloc_pmm_init_default(void);
extern uint64_t rt_riscv_noalloc_alloc_page(void);
extern int64_t rt_riscv_noalloc_pmm_is_ready(void);
extern uint64_t rt_riscv_noalloc_pmm_free_pages(void);
extern uint64_t rt_riscv_noalloc_pmm_total_pages(void);
extern uint64_t rt_riscv_qemu_ram_base(void);
extern uint64_t rt_riscv_qemu_ram_size(void);
extern uint64_t rt_riscv_qemu_reserved_end(void);
extern uint64_t rt_riscv_qemu_heap_start(void);
extern uint64_t rt_riscv_qemu_heap_size(void);

static char uart_bytes[64];
static size_t uart_length;

void rt_riscv_uart_put(uint64_t byte) {
    if (uart_length < sizeof uart_bytes)
        uart_bytes[uart_length++] = (char)(byte & UINT64_C(0xff));
}

static int require_i64(const char *name, int64_t actual, int64_t expected) {
    if (actual == expected) return 1;
    fprintf(stderr, "%s: expected %lld, got %lld\n", name,
            (long long)expected, (long long)actual);
    return 0;
}

static int require_u64(const char *name, uint64_t actual, uint64_t expected) {
    if (actual == expected) return 1;
    fprintf(stderr, "%s: expected %llu, got %llu\n", name,
            (unsigned long long)expected, (unsigned long long)actual);
    return 0;
}

static int require_uart(const char *expected) {
    const size_t length = strlen(expected);
    if (uart_length == length && memcmp(uart_bytes, expected, length) == 0)
        return 1;
    fprintf(stderr, "uart marker mismatch: expected %zu bytes, got %zu\n",
            length, uart_length);
    return 0;
}

int main(void) {
    int ok = 1;

    ok &= require_i64("initial ready", rt_riscv_noalloc_pmm_is_ready(), 0);
    ok &= require_u64("ram base", rt_riscv_qemu_ram_base(), UINT64_C(0x80000000));
    ok &= require_u64("ram size", rt_riscv_qemu_ram_size(), UINT64_C(128) * 1024 * 1024);
    ok &= require_u64("reserved end", rt_riscv_qemu_reserved_end(), UINT64_C(0x80400000));
    ok &= require_u64("heap start", rt_riscv_qemu_heap_start(), UINT64_C(0x87000000));
    ok &= require_u64("heap size", rt_riscv_qemu_heap_size(), UINT64_C(16) * 1024 * 1024);

    uart_length = 0;
    ok &= require_i64("invalid init", rt_riscv_noalloc_pmm_init(
        UINT64_C(0x80000000), UINT64_C(4096), UINT64_C(0x80200000),
        UINT64_C(0x80400000)), 0);
    ok &= require_uart("PMM FAIL\r\n");

    uart_length = 0;
    ok &= require_i64("valid init", rt_riscv_noalloc_pmm_init(
        UINT64_C(0x80000000), UINT64_C(0x08000000), UINT64_C(0x80200001),
        UINT64_C(0x80203000)), 1);
    ok &= require_uart("PMM OK\r\n");
    ok &= require_i64("ready after init", rt_riscv_noalloc_pmm_is_ready(), 1);
    ok &= require_u64("total pages", rt_riscv_noalloc_pmm_total_pages(), 2);
    ok &= require_u64("first page", rt_riscv_noalloc_alloc_page(), UINT64_C(0x80201000));
    ok &= require_u64("free pages", rt_riscv_noalloc_pmm_free_pages(), 1);

    uart_length = 0;
    ok &= require_i64("default init", rt_riscv_noalloc_pmm_init_default(), 1);
    ok &= require_uart("PMM OK\r\n");

    if (!ok) return 1;
    puts("rv64_noalloc_pmm_c_abi status=PASS integer_predicates=0/1");
    return 0;
}
