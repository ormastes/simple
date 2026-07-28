/*
 * RV32 kernel-only native-build bridge.
 *
 * The native linker autodiscovers C runtime files from entry.parent()/boot,
 * and SIMPLE_BOOT_MINIMAL admits only baremetal_stubs.c. Reuse the shared
 * freestanding RISC-V runtime so build/os/simpleos_riscv32.elf links the
 * no-alloc boot support code instead of pulling the hosted allocator stack.
 */
#define rt_native_eq rt_native_eq_wide
#define rt_native_neq rt_native_neq_wide
#include "../../riscv64/boot/freestanding_runtime.c"
#undef rt_native_eq
#undef rt_native_neq

/* The pure RV32 backend lowers its native equality ABI as two 32-bit argument
 * registers even though the shared freestanding implementation stores tagged
 * values in spl_i64. Adapt once at the runtime boundary. */
spl_i64 rt_native_eq(spl_u32 lhs, spl_u32 rhs) {
    return rt_native_eq_wide((spl_i64)(int)lhs, (spl_i64)(int)rhs);
}

spl_i64 rt_native_neq(spl_u32 lhs, spl_u32 rhs) {
    return rt_native_neq_wide((spl_i64)(int)lhs, (spl_i64)(int)rhs);
}

/* SMP: per-hart atomic check-in counter, storage defined by linker.ld's .smp
 * section (outside the BSS-clear range). Each hart amoadd's it in _start;
 * hart 0 reads it via this accessor to report how many harts came online.
 * rv32-only — lives here (after the shared include) so the rv64 lane, which
 * has no _smp_online_count symbol, is unaffected. */
extern volatile unsigned int _smp_online_count;
unsigned long long rt_rv32_smp_online_count(void) {
    return (unsigned long long)_smp_online_count;
}

extern volatile unsigned int _nandram_start[];
unsigned int rt_rv32_nand_ram_load(unsigned int word) {
    return word < 64 ? _nandram_start[word] : 0;
}

void rt_rv32_nand_ram_store(unsigned int word, unsigned int value) {
    if (word < 64) {
        _nandram_start[word] = value;
    }
}

/* RV32 NVMe mailbox aperture.  The endpoint owns the register/DMA behavior;
 * this bridge deliberately exposes only aligned accesses inside its 0x00..0x64
 * contract so a malformed firmware offset cannot touch unrelated MMIO. */
static volatile unsigned int *const rt_rv32_nvme_mmio =
    (volatile unsigned int *)(unsigned long)0x20000000U;

unsigned int rt_rv32_nvme_mmio_load(unsigned int offset) {
    if ((offset & 3U) != 0U || offset > 0x64U) {
        return 0U;
    }
    return rt_rv32_nvme_mmio[offset >> 2];
}

void rt_rv32_nvme_mmio_store(unsigned int offset, unsigned int value) {
    if ((offset & 3U) != 0U || offset > 0x64U) {
        return;
    }
    rt_rv32_nvme_mmio[offset >> 2] = value;
}

long long rt_rv32_boot_optional_nvme_fw_selftest(void) __attribute__((weak));
long long rt_rv32_boot_optional_nvme_fw_selftest(void) {
    return 0;
}
