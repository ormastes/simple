/* linker.ld — Fixed-address linker script for RV64 FPGA bare-metal hello
 *
 * Memory map (ML Carrier Card / Zynq-7020 with RV64 soft-core):
 *   DDR  : 0x80000000, 64 MB  — load target for code + data
 *   BRAM : 0x00000000, 64 KB  — optional tightly-coupled RAM (unused here)
 *
 * UART NS16550 MMIO : 0x10000000 (defined as macro in main.c)
 */

OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

MEMORY {
    BRAM (rwx) : ORIGIN = 0x00000000, LENGTH = 64K
    DDR  (rwx) : ORIGIN = 0x80000000, LENGTH = 64M
}

SECTIONS {
    /* ------------------------------------------------------------------ */
    /* Entry section first — must land exactly at DDR origin               */
    /* ------------------------------------------------------------------ */
    .text.entry : {
        KEEP(*(.text.entry))
    } > DDR

    .text : {
        *(.text*)
    } > DDR

    .rodata : ALIGN(8) {
        *(.rodata*)
        *(.srodata*)
    } > DDR

    .data : ALIGN(8) {
        __global_pointer$ = . + 0x800;  /* gp relaxation anchor */
        *(.data*)
        *(.sdata*)
    } > DDR

    /* ------------------------------------------------------------------ */
    /* BSS — zero-initialized, not stored in ELF image                    */
    /* ------------------------------------------------------------------ */
    .bss (NOLOAD) : ALIGN(8) {
        _bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _bss_end = .;
    } > DDR

    /* ------------------------------------------------------------------ */
    /* Stack — 16 KB, grows down from _stack_top                          */
    /* ------------------------------------------------------------------ */
    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 16K;
        _stack_top = .;
    } > DDR

    /* ------------------------------------------------------------------ */
    /* Discard unwanted sections                                           */
    /* ------------------------------------------------------------------ */
    /DISCARD/ : {
        *(.eh_frame)
        *(.note*)
        *(.comment)
    }
}
