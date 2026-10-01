/* RISC-V common SECTIONS block — shared by riscv32 and riscv64.
 *
 * INCLUDE'd from each per-arch linker.ld after the MEMORY block.
 * Per-arch files supply the width-specific preamble:
 *   OUTPUT_ARCH(riscv)
 *   OUTPUT_FORMAT("elf32-littleriscv" | "elf64-littleriscv")
 *   ENTRY(_start)
 *   MEMORY { RAM (rwx) : ORIGIN = <arch-origin>, LENGTH = <arch-len> }
 *   INCLUDE "../../common/linker_riscv_common.ld"
 *
 * What stays per-arch:
 *   - OUTPUT_FORMAT (elf32 vs elf64)
 *   - MEMORY ORIGIN (0x80000000 rv32 M-mode vs 0x80200000 rv64 S-mode/OpenSBI)
 *   - MEMORY LENGTH (256M vs 510M)
 *
 * What lives here (identical for both widths):
 *   - Full SECTIONS block: .text, .rodata, .data, .bss, .stack, .heap
 *   - _kernel_end symbol
 *   - /DISCARD/ rule
 */

SECTIONS {
    /* Executable code — entry point first */
    .text : ALIGN(4K) {
        KEEP(*(.text.entry))        /* _start entry point */
        *(.text.trap)               /* Trap vector (must be 4-byte aligned) */
        *(.text*)
    } > RAM

    /* Read-only data */
    .rodata : ALIGN(4K) {
        *(.rodata*)
        *(.srodata*)
    } > RAM

    /* Initialized read-write data */
    .data : ALIGN(4K) {
        *(.data*)
        *(.sdata*)
        PROVIDE(__global_pointer$ = . + 0x800);
    } > RAM

    /* Uninitialized data (zeroed by startup code) */
    .bss (NOLOAD) : ALIGN(4K) {
        _sbss = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        _ebss = .;
    } > RAM

    /* Kernel stack (8MB — Simple code uses large stack frames) */
    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 8M;
        _stack_top = .;
    } > RAM

    /* Kernel heap (64MB for bump allocator) */
    .heap (NOLOAD) : ALIGN(4K) {
        __heap_start = .;
        . += 64M;
        __heap_end = .;
    } > RAM

    _kernel_end = .;

    /DISCARD/ : {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
