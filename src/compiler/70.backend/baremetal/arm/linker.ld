/*
 * ARM Cortex-M Linker Script
 *
 * Target: ARM Cortex-M4F (STM32F4xx, LM3S6965)
 * Memory Layout:
 *   Flash: 0x08000000 - 0x08080000 (512KB)
 *   RAM:   0x20000000 - 0x20020000 (128KB)
 *
 * Sections:
 *   .vector_table - Interrupt vector table (512 bytes)
 *   .text         - Code and read-only data
 *   .data         - Initialized data (flash -> RAM)
 *   .bss          - Uninitialized data (zero-initialized)
 *   .heap         - Dynamic memory allocation
 *   .stack        - Call stack (grows downward)
 */

ENTRY(reset_handler)

MEMORY
{
    FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 512K
    RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 128K
}

SECTIONS
{
    /* Vector table must be at 0x08000000 */
    .vector_table :
    {
        . = ALIGN(512);
        KEEP(*(.vector_table))
        . = ALIGN(4);
    } > FLASH

    /* Code and read-only data */
    .text :
    {
        . = ALIGN(4);
        *(.text.reset_handler)
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
        _etext = .;
    } > FLASH

    /* ARM EABI sections */
    .ARM.extab :
    {
        *(.ARM.extab* .gnu.linkonce.armextab.*)
    } > FLASH

    .ARM.exidx :
    {
        __exidx_start = .;
        *(.ARM.exidx* .gnu.linkonce.armexidx.*)
        __exidx_end = .;
    } > FLASH

    /* Initialized data (copied from flash to RAM at startup) */
    _sidata = LOADADDR(.data);

    .data : AT(_sidata)
    {
        . = ALIGN(4);
        _sdata = .;
        *(.data*)
        . = ALIGN(4);
        _edata = .;
    } > RAM

    /* Uninitialized data (zero-initialized at startup) */
    .bss :
    {
        . = ALIGN(4);
        _sbss = .;
        *(.bss*)
        *(COMMON)
        *(.bss.fault_info)
        . = ALIGN(4);
        _ebss = .;
    } > RAM

    /* Heap (grows upward) */
    .heap :
    {
        . = ALIGN(8);
        __heap_start = .;
        . = . + 32K;  /* 32KB heap */
        __heap_end = .;
    } > RAM

    /* Stack (grows downward from end of RAM) */
    .stack :
    {
        . = ALIGN(8);
        . = . + 8K;   /* 8KB stack */
        _stack_top = .;
    } > RAM

    /* Ensure stack doesn't overflow into heap */
    ASSERT(_stack_top <= ORIGIN(RAM) + LENGTH(RAM), "Stack overflows RAM")

    /* Debug sections */
    .comment 0 : { *(.comment) }
    .debug_info 0 : { *(.debug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev) }
    .debug_line 0 : { *(.debug_line) }
    .debug_str 0 : { *(.debug_str) }
    .debug_frame 0 : { *(.debug_frame) }

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.eh_frame*)
    }
}
