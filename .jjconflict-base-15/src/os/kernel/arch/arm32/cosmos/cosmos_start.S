/* CRZ Cosmos+ OpenSSD (Xilinx Zynq-7000, dual Cortex-A9 / ARMv7-A) bare-metal entry.
 *
 * Direct M-... (ARM has no M-mode; this is the FSBL-less bring-up entry used under
 * `qemu-system-arm -M xilinx-zynq-a9 -kernel`). On real Cosmos+ hardware the Zynq BootROM
 * + FSBL would run first; this entry is the minimal "kernel loaded into DDR, jump here"
 * bring-up that validates the Cadence UART / memory map binding.
 */
    .section .text.start,"ax",%progbits
    .global _start
    .arm
_start:
    /* CPU1 (and any secondary) parks; CPU0 boots. MPIDR low bits = CPU id. */
    mrc     p15, 0, r1, c0, c0, 5      /* read MPIDR */
    and     r1, r1, #3
    cmp     r1, #0
    bne     .Lpark
    ldr     sp, =_stack_top
    bl      cosmos_boot_main
.Lhalt:
    wfi
    b       .Lhalt
.Lpark:
    wfi
    b       .Lpark
