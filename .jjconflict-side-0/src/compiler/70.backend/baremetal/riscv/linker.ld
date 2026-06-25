/*
 * RISC-V Bare-Metal Linker Script
 *
 * Target: RV32/RV64 processors (QEMU virt, SiFive FU540)
 * Memory Layout (QEMU virt):
 *   0x80000000 - RAM start (2GB)
 *   0x80100000 - Kernel load address
 *   0x80200000 - Stack (grows down)
 *
 * Sections:
 *   .text  - Code and entry point
 *   .rodata - Read-only data
 *   .data  - Initialized data (copied from flash if needed)
 *   .bss   - Uninitialized data (zero-initialized)
 *   .heap  - Dynamic memory allocation
 *   .stack - Call stack
 *
 * Special Features:
 *   - Preserves device tree blob address
 *   - Supports multi-hart (SMP) initialization
 *   - Identity-mapped memory regions
 */

ENTRY(_start)

MEMORY
{
    RAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS
{
    /* Code starts at 1MB offset in RAM */
    . = 0x80000000;

    /* Entry point and startup code */
    .text : ALIGN(4K)
    {
        KEEP(*(.text.start))
        *(.text.trap)
        *(.text*)
        . = ALIGN(8);
    } > RAM

    /* Read-only data */
    .rodata : ALIGN(4K)
    {
        *(.rodata*)
        . = ALIGN(8);
    } > RAM

    /* Initialized data (may be copied from flash on some platforms) */
    _sidata = LOADADDR(.data);

    .data : ALIGN(4K)
    {
        _sdata = .;
        *(.data*)
        *(.sdata*)
        . = ALIGN(8);
        _edata = .;
    } > RAM

    /* Uninitialized data (zero-initialized at startup) */
    .bss : ALIGN(4K)
    {
        __bss_start = .;
        _sbss = .;
        *(.bss*)
        *(.sbss*)
        *(COMMON)
        . = ALIGN(8);
        _ebss = .;
        __bss_end = .;
    } > RAM

    /* Heap (grows upward) */
    .heap : ALIGN(4K)
    {
        __heap_start = .;
        . = . + 32M;  /* 32MB heap */
        __heap_end = .;
    } > RAM

    /* Stack (grows downward) */
    .stack : ALIGN(16)
    {
        . = . + 64K;  /* 64KB stack */
        _stack_top = .;
    } > RAM

    /* Device tree blob storage (preserved from bootloader) */
    .dtb : ALIGN(4K)
    {
        __dtb_start = .;
        . = . + 4K;   /* Reserve 4KB for DTB pointer */
        __dtb_end = .;
    } > RAM

    /* End of kernel */
    _kernel_end = .;

    /* Ensure memory doesn't overflow */
    ASSERT(_kernel_end <= ORIGIN(RAM) + LENGTH(RAM), "Kernel overflows RAM")

    /* RISC-V specific sections */
    .riscv.attributes 0 : { *(.riscv.attributes) }

    /* Debug sections */
    .debug_info 0 : { *(.debug_info .zdebug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev .zdebug_abbrev) }
    .debug_line 0 : { *(.debug_line .zdebug_line) }
    .debug_str 0 : { *(.debug_str .zdebug_str) }
    .debug_frame 0 : { *(.debug_frame) }
    .debug_loc 0 : { *(.debug_loc .zdebug_loc) }
    .debug_ranges 0 : { *(.debug_ranges .zdebug_ranges) }

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
    }
}
