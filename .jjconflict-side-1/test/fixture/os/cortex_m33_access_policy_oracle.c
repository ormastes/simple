#include <stdint.h>
#include <stdio.h>

enum {
    ACCESS_OK = 0,
    ACCESS_UNALIGNED = 1,
    ACCESS_UNREADABLE = 2,
    ACCESS_UNWRITABLE = 3
};

static uint32_t receipt(uint32_t outcome, uint32_t decision_mask) {
    return (decision_mask << 8) | outcome;
}

static int old_addr_readable(uint32_t addr,
                             uint32_t flash_base,
                             uint32_t flash_size,
                             uint32_t ram_base,
                             uint32_t ram_size) {
    if (addr >= flash_base && addr < flash_base + flash_size) return 1;
    if (addr >= ram_base && addr < ram_base + ram_size) return 1;
    if (addr >= 0x40000000u && addr < 0x60000000u) return 1;
    if (addr >= 0xE000E000u && addr < 0xE0100000u) return 1;
    return 0;
}

static int old_addr_writable(uint32_t addr,
                             uint32_t ram_base,
                             uint32_t ram_size) {
    if (addr >= ram_base && addr < ram_base + ram_size) return 1;
    if (addr >= 0x40000000u && addr < 0x60000000u) return 1;
    return 0;
}

static uint32_t oracle_read(uint32_t addr,
                            uint32_t flash_base,
                            uint32_t flash_size,
                            uint32_t ram_base,
    uint32_t ram_size) {
    if ((addr & 3u) != 0) return receipt(ACCESS_UNALIGNED, 1u);
    if (!old_addr_readable(addr, flash_base, flash_size, ram_base, ram_size)) {
        return receipt(ACCESS_UNREADABLE, 32u);
    }
    if (addr >= flash_base && addr < flash_base + flash_size) return receipt(ACCESS_OK, 2u);
    if (addr >= ram_base && addr < ram_base + ram_size) return receipt(ACCESS_OK, 4u);
    if (addr >= 0x40000000u && addr < 0x60000000u) return receipt(ACCESS_OK, 8u);
    if (addr >= 0xE000E000u && addr < 0xE0100000u) return receipt(ACCESS_OK, 16u);
    return receipt(ACCESS_OK, 0u);
}

static uint32_t oracle_write(uint32_t addr,
                             uint32_t ram_base,
                             uint32_t ram_size) {
    if ((addr & 3u) != 0) return receipt(ACCESS_UNALIGNED, 64u);
    if (!old_addr_writable(addr, ram_base, ram_size)) return receipt(ACCESS_UNWRITABLE, 512u);
    if (addr >= ram_base && addr < ram_base + ram_size) return receipt(ACCESS_OK, 128u);
    if (addr >= 0x40000000u && addr < 0x60000000u) return receipt(ACCESS_OK, 256u);
    return receipt(ACCESS_OK, 0u);
}

static uint32_t emit_case(const char *board,
                          const char *case_name,
                          uint32_t addr,
                          uint32_t flash_base,
                          uint32_t flash_size,
                          uint32_t ram_base,
                          uint32_t ram_size,
                          uint32_t covered) {
    uint32_t read = oracle_read(addr, flash_base, flash_size, ram_base, ram_size);
    uint32_t write = oracle_write(addr, ram_base, ram_size);
    printf("board=%s case=%s addr=%u read=%u write=%u\n",
           board, case_name, addr, read, write);
    return covered | (read >> 8) | (write >> 8);
}

static uint32_t emit_board(const char *board,
                           uint32_t flash_base,
                           uint32_t flash_size,
                           uint32_t ram_base,
                           uint32_t ram_size,
                           uint32_t decisions) {
    decisions = emit_case(board, "flash-misaligned", flash_base + 1u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "flash-first", flash_base,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "flash-last", flash_base + flash_size - 4u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "flash-end", flash_base + flash_size,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ram-first", ram_base,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ram-last", ram_base + ram_size - 4u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ram-end", ram_base + ram_size,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "peripheral-first", 0x40000000u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "peripheral-last", 0x5FFFFFFCu,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "peripheral-end", 0x60000000u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ppb-first", 0xE000E000u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ppb-last", 0xE00FFFFCu,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    decisions = emit_case(board, "ppb-end", 0xE0100000u,
                          flash_base, flash_size, ram_base, ram_size, decisions);
    return decisions;
}

int main(void) {
    uint32_t decisions = 0;
    decisions = emit_board("an505-m33", 0x10000000u, 0x00400000u,
                           0x20000000u, 0x00008000u, decisions);
    decisions = emit_board("stm32u585-m33", 0x08000000u, 0x00200000u,
                           0x20000000u, 0x000C0000u, decisions);
    decisions = emit_board("ra4m1-m4", 0x00000000u, 0x00040000u,
                           0x20000000u, 0x00008000u, decisions);
    printf("decision_mask=%u\n", decisions);
    return decisions == 1023u ? 0 : 1;
}
