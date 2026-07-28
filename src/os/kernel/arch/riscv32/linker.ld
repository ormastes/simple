/* RISC-V 32 Linker Script — QEMU virt machine, direct M-mode boot
 *
 * Kernel loaded at 0x80000000 with `-bios none`.
 * RAM: 0x80000000 .. 0x87FFFFFF (128MB total).
 *
 * Output format: ELF32 little-endian RISC-V.
 */

OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf32-littleriscv")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS {
    .text : ALIGN(4K) {
        KEEP(*(.text.entry))
        *(.text.trap)
        *(.text*)
    } > RAM

    .rodata : ALIGN(4K) {
        *(.rodata*)
    } > RAM

    .simple_sandbox : ALIGN(4K) {
        __simple_sandbox_start = .;
        KEEP(*(.simple.sandbox*))
        KEEP(*(.simple.mpu*))
        __simple_sandbox_end = .;
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

    /* SMP hart check-in counter. Deliberately OUTSIDE [_sbss,_ebss] so hart 0's
     * BSS clear cannot wipe a secondary hart's atomic check-in. NOLOAD + QEMU
     * zeroing RAM at reset means it starts at 0 before any hart runs. */
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
