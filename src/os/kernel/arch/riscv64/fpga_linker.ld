/* RISC-V 64 SimpleOS Linker Script — M-mode bare-metal for FPGA
 *
 * Kernel runs directly in M-mode at 0x80000000, no firmware.
 * Targeted at Kria K26 (XCZU5EV) with 64MB DDR for the RV64 softcore.
 * Also works on QEMU virt with -bios none -m 64M.
 *
 * Memory layout (64MB RAM):
 *   0x80000000 - onwards    : Kernel image (.text.start first)
 *   top - 8MB               : Heap (8MB)
 *   top - 8MB - 64KB        : Stack (64KB, grows down)
 */
OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 64M
}

SECTIONS {
    .text : ALIGN(4K) {
        KEEP(*(.text.start))
        *(.text.trap)
        *(.text*)
    } > RAM

    .rodata : ALIGN(4K) {
        *(.rodata*)
        *(.srodata*)
    } > RAM

    .data : ALIGN(4K) {
        *(.data*)
        *(.sdata*)
        PROVIDE(__global_pointer$ = . + 0x800);
    } > RAM

    .bss (NOLOAD) : ALIGN(4K) {
        _sbss = .;
        __bss_start = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _ebss = .;
        __bss_end = .;
    } > RAM

    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 64K;
        _stack_top = .;
    } > RAM

    .heap (NOLOAD) : ALIGN(4K) {
        __heap_start = .;
        . += 8M;
        __heap_end = .;
    } > RAM

    _kernel_end = .;

    /DISCARD/ : {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
