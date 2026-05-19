/* RISC-V 64 SimpleOS Linker Script — FPGA Bare-Metal (M-mode)
 *
 * Kernel is loaded at 0x80000000 (DDR base) directly by JTAG/OpenOCD.
 * No OpenSBI reservation — this is a bare-metal M-mode image.
 *
 * Memory layout (ML Carrier Card, 64 MiB DDR):
 *   0x00000000 - 0x0000FFFF : BRAM (64 KiB boot ROM staging)
 *   0x80000000 - 0x83FFFFFF : DDR (64 MiB)
 *
 * Key difference from QEMU virt (linker.ld):
 *   QEMU: ORIGIN = 0x80200000 (after 2MB OpenSBI reservation)
 *   FPGA: ORIGIN = 0x80000000 (no SBI firmware, M-mode entry at DDR base)
 *
 * Sections are 4KB-aligned for page table compatibility (Sv39 future use).
 */
OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

MEMORY {
    BRAM (rwx) : ORIGIN = 0x00000000, LENGTH = 64K
    DDR  (rwx) : ORIGIN = 0x80000000, LENGTH = 64M
}

SECTIONS {
    /* Boot init code — placed at DDR base (M-mode entry) */
    .text.init : ALIGN(4K) {
        KEEP(*(.text.init))             /* _start bare-metal entry */
        KEEP(*(.text.entry))            /* alternate entry section name */
    } > DDR

    /* Executable code */
    .text : ALIGN(4K) {
        *(.text.trap)                   /* Trap vector (must be 4-byte aligned) */
        *(.text*)
    } > DDR

    /* Read-only data */
    .rodata : ALIGN(4K) {
        *(.rodata*)
        *(.srodata*)
    } > DDR

    /* Initialized read-write data */
    .data : ALIGN(4K) {
        *(.data*)
        *(.sdata*)
        PROVIDE(__global_pointer$ = . + 0x800);
    } > DDR

    /* Uninitialized data (zeroed by startup code) */
    .bss (NOLOAD) : ALIGN(4K) {
        _bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _bss_end = .;
    } > DDR

    /* Kernel stack (per-hart, 64KB) */
    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 64K;
        _stack_top = .;
    } > DDR

    /* Kernel heap (remainder of DDR after image) */
    .heap (NOLOAD) : ALIGN(4K) {
        _heap_start = .;
        . += 16M;
        _heap_end = .;
    } > DDR

    _kernel_end = .;

    /DISCARD/ : {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
