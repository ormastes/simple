/* RISC-V 32 FPGA Softcore Linker Script — direct M-mode boot
 *
 * Kernel loaded at 0x80000000 with `-bios none` (QEMU virt FPGA-softcore stand-in,
 * also valid for VexRiscv/NaxRiscv softcores using the 0x80000000 RAM base).
 * RAM: 0x80000000 .. 0x87FFFFFF (128MB).
 *
 * .text.start (the M-mode FPGA _start) is KEEP'd FIRST so the reset vector at
 * 0x80000000 is the real entry. Output: ELF32 little-endian RISC-V.
 */

OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf32-littleriscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS {
    .text : ALIGN(4K) {
        KEEP(*(.text.start))
        KEEP(*(.text.entry))
        *(.text.trap)
        *(.text*)
    } > RAM

    .rodata : ALIGN(4K) {
        *(.rodata*)
    } > RAM

    .data : ALIGN(4K) {
        *(.data*)
        *(.sdata*)
        PROVIDE(__global_pointer$ = . + 0x800);
    } > RAM

    .bss (NOLOAD) : ALIGN(4K) {
        _sbss = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _ebss = .;
    } > RAM

    /* SMP hart check-in counter, outside [_sbss,_ebss] (see linker.ld). */
    .smp (NOLOAD) : ALIGN(4) {
        _smp_online_count = .;
        . += 4;
    } > RAM

    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 32K;
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
