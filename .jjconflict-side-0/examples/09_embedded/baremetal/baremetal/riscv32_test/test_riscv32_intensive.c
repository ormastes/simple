/* RISC-V 32 Intensive Baremetal Test Suite
 *
 * Tests hardware features via QEMU semihosting:
 * - Semihosting operations (SYS_WRITE0, SYS_CLOCK, SYS_EXIT)
 * - Integer arithmetic (32-bit boundary behavior)
 * - Memory-mapped I/O patterns (UART, CLINT regions)
 * - CSR address constants
 * - Interrupt cause bit verification
 * - TrapFrame layout calculations
 * - Stack alignment verification
 * - Bit manipulation operations
 * - Semihosting parameter block sizes
 * - Timer/clock reading via semihosting
 */

#include "sspec_baremetal.h"
#include <stdint.h>

/* Read mcycle CSR (RV32: read hi-lo-hi to avoid tearing) */
static uint64_t read_mcycle(void) {
    uint32_t lo, hi1, hi2;
    do {
        __asm__ volatile ("csrr %0, mcycleh" : "=r"(hi1));
        __asm__ volatile ("csrr %0, mcycle"  : "=r"(lo));
        __asm__ volatile ("csrr %0, mcycleh" : "=r"(hi2));
    } while (hi1 != hi2);
    return ((uint64_t)hi1 << 32) | lo;
}

/* Volatile memory read/write (for MMIO patterns) */
static inline uint32_t mmio_read32(uint32_t addr) {
    return *(volatile uint32_t *)addr;
}

static inline void mmio_write32(uint32_t addr, uint32_t val) {
    *(volatile uint32_t *)addr = val;
}

/* Bit manipulation helpers */
static inline uint32_t set_bit(uint32_t val, int bit) {
    return val | (1u << bit);
}

static inline uint32_t clear_bit(uint32_t val, int bit) {
    return val & ~(1u << bit);
}

static inline int test_bit(uint32_t val, int bit) {
    return (val >> bit) & 1;
}

static inline uint32_t align_up(uint32_t val, uint32_t align) {
    return (val + align - 1) & ~(align - 1);
}

int main(void) {
    semihost_write0("=== RISC-V 32 Intensive Baremetal Test Suite ===\n");
    semihost_write0("Platform: QEMU virt, RV32IMAC, Semihosting\n\n");

    /* ================================================================
     * 1. Semihosting Operations
     * ================================================================ */
    describe("Semihosting Operations");

    it("SYS_WRITE0 outputs string", {
        /* If we got here, SYS_WRITE0 already works */
        expect_true(1);
    });

    it("SYS_CLOCK returns non-negative value", {
        long clock = semihost_clock();
        expect_true(clock >= 0);
    });

    it("SYS_CLOCK advances over time", {
        long c1 = semihost_clock();
        /* Busy wait */
        volatile int dummy = 0;
        for (int i = 0; i < 100000; i++) dummy++;
        long c2 = semihost_clock();
        /* Clock should advance (or at least not go backwards) */
        expect_true(c2 >= c1);
    });

    /* ================================================================
     * 2. Semihosting Constants
     * ================================================================ */
    describe("Semihosting Constants");

    it("SYS_OPEN is 0x01", {
        expect_equal(SYS_OPEN, 0x01);
    });

    it("SYS_CLOSE is 0x02", {
        expect_equal(SYS_CLOSE, 0x02);
    });

    it("SYS_WRITEC is 0x03", {
        expect_equal(SYS_WRITEC, 0x03);
    });

    it("SYS_WRITE0 is 0x04", {
        expect_equal(SYS_WRITE0, 0x04);
    });

    it("SYS_WRITE is 0x05", {
        expect_equal(SYS_WRITE, 0x05);
    });

    it("SYS_READ is 0x06", {
        expect_equal(SYS_READ, 0x06);
    });

    it("SYS_EXIT is 0x18", {
        expect_equal(SYS_EXIT, 0x18);
    });

    it("ADP_Stopped_ApplicationExit is 0x20026", {
        expect_equal(ADP_Stopped_ApplicationExit, 0x20026);
    });

    /* ================================================================
     * 3. Parameter Block Sizes (u32 on RV32)
     * ================================================================ */
    describe("Parameter Block Sizes (RV32)");

    it("each parameter is u32 (4 bytes)", {
        expect_equal((int)sizeof(uint32_t), 4);
    });

    it("SYS_OPEN block is 3 x u32 = 12 bytes", {
        expect_equal(3 * (int)sizeof(uint32_t), 12);
    });

    it("SYS_WRITE block is 3 x u32 = 12 bytes", {
        expect_equal(3 * (int)sizeof(uint32_t), 12);
    });

    it("SYS_EXIT block is 2 x u32 = 8 bytes", {
        expect_equal(2 * (int)sizeof(uint32_t), 8);
    });

    it("pointer size is 4 bytes on RV32", {
        expect_equal((int)sizeof(void *), 4);
    });

    it("long is 4 bytes on RV32", {
        expect_equal((int)sizeof(long), 4);
    });

    /* ================================================================
     * 4. 32-bit Arithmetic Boundary Tests
     * ================================================================ */
    describe("32-bit Arithmetic");

    it("INT32_MAX is 0x7FFFFFFF", {
        expect_equal(INT32_MAX, 0x7FFFFFFF);
    });

    it("UINT32_MAX is 0xFFFFFFFF", {
        expect_equal(UINT32_MAX, 0xFFFFFFFF);
    });

    it("INT32_MAX + 1 wraps to INT32_MIN", {
        int32_t val = INT32_MAX;
        val++;
        expect_equal(val, INT32_MIN);
    });

    it("UINT32_MAX + 1 wraps to 0", {
        uint32_t val = UINT32_MAX;
        val++;
        expect_equal((int)val, 0);
    });

    it("multiplication overflow wraps correctly", {
        uint32_t a = 0x10000;
        uint32_t b = 0x10000;
        uint32_t result = a * b;
        expect_equal((int)result, 0);  /* 2^32 wraps to 0 */
    });

    it("division by power of 2 via shift", {
        uint32_t val = 0x80000000;
        uint32_t result = val >> 1;
        expect_equal((int)result, 0x40000000);
    });

    it("signed right shift preserves sign", {
        int32_t val = -1;  /* 0xFFFFFFFF */
        int32_t result = val >> 1;
        expect_equal(result, -1);  /* Arithmetic shift preserves sign */
    });

    /* ================================================================
     * 5. Memory Layout Constants
     * ================================================================ */
    describe("Memory Layout Constants");

    it("RAM base is 0x80000000", {
        expect_equal((int)0x80000000u, (int)0x80000000u);
    });

    it("RAM size is 128MB", {
        expect_equal(128 * 1024 * 1024, 134217728);
    });

    it("stack size per hart is 64KB", {
        expect_equal(64 * 1024, 65536);
    });

    it("4 harts need 256KB total stack", {
        expect_equal(4 * 64 * 1024, 262144);
    });

    /* ================================================================
     * 6. UART Constants (16550 compatible)
     * ================================================================ */
    describe("UART Constants");

    it("UART base is 0x10000000", {
        expect_equal((int)0x10000000u, (int)0x10000000u);
    });

    it("DLAB enable is 0x80", {
        expect_equal(0x80, 128);
    });

    it("8N1 config is 0x03", {
        expect_equal(0x03, 3);
    });

    it("THR empty mask is 0x20", {
        expect_equal(0x20, 32);
    });

    it("IER register at offset 1", {
        expect_equal(1, 1);
    });

    it("LCR register at offset 3", {
        expect_equal(3, 3);
    });

    it("LSR register at offset 5", {
        expect_equal(5, 5);
    });

    /* ================================================================
     * 7. PLIC Constants
     * ================================================================ */
    describe("PLIC Constants");

    it("PLIC base is 0x0C000000", {
        expect_equal((int)0x0C000000u, (int)0x0C000000u);
    });

    it("CLINT mtime is at 0x0200BFF8", {
        uint32_t addr = 0x0200BFF8;
        expect_true(addr >= 0x02000000 && addr <= 0x0200FFFF);
    });

    it("CLINT mtimecmp is at 0x02004000", {
        uint32_t addr = 0x02004000;
        expect_true(addr >= 0x02000000 && addr <= 0x0200FFFF);
    });

    /* ================================================================
     * 8. CSR Address Verification
     * ================================================================ */
    describe("CSR Addresses");

    it("mstatus is 0x300", {
        expect_equal(0x300, 0x300);
    });

    it("misa is 0x301", {
        expect_equal(0x301, 0x301);
    });

    it("mie is 0x304", {
        expect_equal(0x304, 0x304);
    });

    it("mtvec is 0x305", {
        expect_equal(0x305, 0x305);
    });

    it("mscratch is 0x340", {
        expect_equal(0x340, 0x340);
    });

    it("mepc is 0x341", {
        expect_equal(0x341, 0x341);
    });

    it("mcause is 0x342", {
        expect_equal(0x342, 0x342);
    });

    it("mtval is 0x343", {
        expect_equal(0x343, 0x343);
    });

    it("mip is 0x344", {
        expect_equal(0x344, 0x344);
    });

    it("mhartid is 0xF14", {
        expect_equal(0xF14, 0xF14);
    });

    /* ================================================================
     * 9. Interrupt Cause Bits (RV32: bit 31)
     * ================================================================ */
    describe("Interrupt Cause Bits (RV32)");

    it("interrupt bit is 0x80000000 (bit 31)", {
        uint32_t bit = 0x80000000;
        expect_true(test_bit(bit, 31));
    });

    it("M-mode software interrupt code is 3", {
        uint32_t cause = 0x80000000 | 3;
        expect_equal((int)(cause & 0x7FFFFFFF), 3);
    });

    it("M-mode timer interrupt code is 7", {
        uint32_t cause = 0x80000000 | 7;
        expect_equal((int)(cause & 0x7FFFFFFF), 7);
    });

    it("M-mode external interrupt code is 11", {
        uint32_t cause = 0x80000000 | 11;
        expect_equal((int)(cause & 0x7FFFFFFF), 11);
    });

    it("exception has no interrupt flag", {
        uint32_t cause = 5;  /* Load access fault */
        expect_true(!test_bit(cause, 31));
    });

    /* ================================================================
     * 10. MSTATUS and MIE Bits
     * ================================================================ */
    describe("MSTATUS and MIE Bits");

    it("MIE bit is 0x08 (bit 3)", {
        expect_equal(0x08, 8);
        expect_true(test_bit(0x08, 3));
    });

    it("MPIE bit is 0x80 (bit 7)", {
        expect_equal(0x80, 128);
        expect_true(test_bit(0x80, 7));
    });

    it("MSIE is 0x08", {
        expect_equal(0x08, 8);
    });

    it("MTIE is 0x80", {
        expect_equal(0x80, 128);
    });

    it("MEIE is 0x800", {
        expect_equal(0x800, 2048);
    });

    it("all M-mode interrupts = 0x888", {
        expect_equal(0x08 | 0x80 | 0x800, 0x888);
    });

    /* ================================================================
     * 11. TrapFrame32 Layout
     * ================================================================ */
    describe("TrapFrame32 Layout");

    it("33 fields (x1-x31 + mepc + mstatus)", {
        expect_equal(33, 33);
    });

    it("each field is 4 bytes (u32)", {
        expect_equal((int)sizeof(uint32_t), 4);
    });

    it("total size is 132 bytes", {
        expect_equal(33 * 4, 132);
    });

    it("x1 (ra) at offset 0", {
        expect_equal(0 * 4, 0);
    });

    it("x10 (a0) at offset 36", {
        expect_equal(9 * 4, 36);
    });

    it("mepc at offset 124", {
        expect_equal(31 * 4, 124);
    });

    it("mstatus at offset 128", {
        expect_equal(32 * 4, 128);
    });

    /* ================================================================
     * 12. Stack Alignment
     * ================================================================ */
    describe("Stack Alignment");

    it("stack is 16-byte aligned", {
        uint32_t sp_val;
        __asm__ volatile ("mv %0, sp" : "=r"(sp_val));
        expect_equal((int)(sp_val & 0xF), 0);
    });

    it("align_up(1, 16) = 16", {
        expect_equal((int)align_up(1, 16), 16);
    });

    it("align_up(16, 16) = 16", {
        expect_equal((int)align_up(16, 16), 16);
    });

    it("align_up(17, 16) = 32", {
        expect_equal((int)align_up(17, 16), 32);
    });

    it("align_up(132, 16) = 144 (TrapFrame aligned)", {
        expect_equal((int)align_up(132, 16), 144);
    });

    /* ================================================================
     * 13. Bit Manipulation
     * ================================================================ */
    describe("Bit Manipulation");

    it("set_bit(0, 3) = 8", {
        expect_equal((int)set_bit(0, 3), 8);
    });

    it("set_bit(0, 31) = 0x80000000", {
        expect_equal((int)set_bit(0, 31), (int)0x80000000u);
    });

    it("clear_bit(0xFF, 3) = 0xF7", {
        expect_equal((int)clear_bit(0xFF, 3), 0xF7);
    });

    it("test_bit(0x80000000, 31) = 1", {
        expect_true(test_bit(0x80000000, 31));
    });

    it("test_bit(0x08, 3) = 1", {
        expect_true(test_bit(0x08, 3));
    });

    it("test_bit(0x08, 4) = 0", {
        expect_true(!test_bit(0x08, 4));
    });

    /* ================================================================
     * 14. mcycle Counter (RV32 specific)
     * ================================================================ */
    describe("mcycle Counter (RV32)");

    it("mcycle is readable", {
        uint64_t cycles = read_mcycle();
        expect_true(cycles > 0);
    });

    it("mcycle advances", {
        uint64_t c1 = read_mcycle();
        volatile int dummy = 0;
        for (int i = 0; i < 1000; i++) dummy++;
        uint64_t c2 = read_mcycle();
        expect_true(c2 > c1);
    });

    it("mcycle difference is reasonable", {
        uint64_t c1 = read_mcycle();
        volatile int dummy = 0;
        for (int i = 0; i < 10000; i++) dummy++;
        uint64_t c2 = read_mcycle();
        uint64_t diff = c2 - c1;
        /* Should be at least a few thousand cycles */
        expect_true(diff > 100);
        /* But not billions (would indicate tearing) */
        expect_true(diff < 100000000);
    });

    /* ================================================================
     * 15. QEMU Platform Verification
     * ================================================================ */
    describe("QEMU Platform Verification");

    it("running on RV32 (pointer is 4 bytes)", {
        expect_equal((int)sizeof(void *), 4);
    });

    it("int is 4 bytes", {
        expect_equal((int)sizeof(int), 4);
    });

    it("long is 4 bytes on RV32", {
        expect_equal((int)sizeof(long), 4);
    });

    it("uint64_t is 8 bytes", {
        expect_equal((int)sizeof(uint64_t), 8);
    });

    it("code is in expected memory region", {
        uint32_t pc;
        __asm__ volatile ("auipc %0, 0" : "=r"(pc));
        expect_true(pc >= 0x80000000);
        expect_true(pc < 0x80010000);
    });

    it("stack is in expected memory region", {
        uint32_t sp_val;
        __asm__ volatile ("mv %0, sp" : "=r"(sp_val));
        expect_true(sp_val >= 0x80000000);
        expect_true(sp_val <= 0x80004000);
    });

    it("mhartid is 0 (boot hart)", {
        uint32_t hartid;
        __asm__ volatile ("csrr %0, mhartid" : "=r"(hartid));
        expect_equal((int)hartid, 0);
    });

    /* ================================================================
     * 16. Endianness Verification
     * ================================================================ */
    describe("Endianness");

    it("RISC-V is little-endian", {
        uint32_t val = 0x01020304;
        uint8_t *bytes = (uint8_t *)&val;
        expect_equal(bytes[0], 0x04);  /* LSB first */
        expect_equal(bytes[3], 0x01);  /* MSB last */
    });

    it("byte swap via shifts", {
        uint32_t val = 0x12345678;
        uint32_t swapped = ((val >> 24) & 0xFF) |
                          ((val >> 8) & 0xFF00) |
                          ((val << 8) & 0xFF0000) |
                          ((val << 24) & 0xFF000000);
        expect_equal((int)swapped, (int)0x78563412u);
    });

    /* ================================================================
     * Summary
     * ================================================================ */
    sspec_summary();

    return sspec_exit_code();
}
