/* Independent host-only oracle for the scalar RV32 direct-boot layout policy. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static int oracle_valid(
    uint64_t ram_base,
    uint64_t ram_size,
    uint64_t reserved_end,
    uint64_t heap_start,
    uint64_t heap_size
) {
    const uint64_t page_size = 4096U;
    uint64_t alloc_base;
    if (ram_size <= page_size || reserved_end <= ram_base ||
        heap_start <= reserved_end || heap_size < 8U) return 0;
    if (ram_size > UINT64_MAX - ram_base ||
        heap_size > UINT64_MAX - heap_start) return 0;
    if (heap_start + heap_size > ram_base + ram_size) return 0;
    alloc_base = ((reserved_end + page_size - 1U) / page_size) * page_size;
    return alloc_base < heap_start;
}

int main(int argc, char **argv) {
    uint64_t ram_base, ram_size, reserved_end, heap_start, heap_size, pages = 0;
    if (argc != 6) return 2;
    ram_base = strtoull(argv[1], 0, 0);
    ram_size = strtoull(argv[2], 0, 0);
    reserved_end = strtoull(argv[3], 0, 0);
    heap_start = strtoull(argv[4], 0, 0);
    heap_size = strtoull(argv[5], 0, 0);
    if (oracle_valid(ram_base, ram_size, reserved_end, heap_start, heap_size)) {
        uint64_t alloc_base = ((reserved_end + 4095U) / 4096U) * 4096U;
        pages = (heap_start - alloc_base) / 4096U;
        printf("1:%llu\n", (unsigned long long)pages);
    } else {
        printf("0:0\n");
    }
    return 0;
}
