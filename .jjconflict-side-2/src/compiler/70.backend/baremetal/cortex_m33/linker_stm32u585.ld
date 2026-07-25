/*
 * Cortex-M33 Linker Script — STM32U585 (Arduino UNO Q)
 *
 * Memory Layout:
 *   FLASH: 0x08000000 - 0x08200000 (2 MB)
 *   RAM:   0x20000000 - 0x200C0000 (768 KB)
 *
 * PMSAv8-M partition (non-overlapping):
 *   0x20000000 – 0x2003FFFF  Kernel data  (256K)
 *   0x20040000 – 0x2005FFFF  App sandbox  (128K)
 *   0x20060000 – 0x200BFFFF  Kernel stack (384K)
 */

ENTRY(Reset_Handler)

MEMORY
{
    FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 2M
    RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 768K
}

SECTIONS
{
    .vector_table :
    {
        . = ALIGN(512);
        KEEP(*(.vector_table))
        . = ALIGN(4);
    } > FLASH

    .text :
    {
        . = ALIGN(4);
        *(.text.Reset_Handler)
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
        _etext = .;
    } > FLASH

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

    _sidata = LOADADDR(.data);

    .data :
    {
        . = ALIGN(4);
        _sdata = .;
        *(.data*)
        . = ALIGN(4);
        _edata = .;
    } > RAM AT> FLASH

    .bss (NOLOAD) :
    {
        . = ALIGN(4);
        __bss_start = .;
        _sbss = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        _ebss = .;
        __bss_end = .;
    } > RAM

    _heap_start = .;

    ASSERT(_heap_start <= 0x20040000, "BSS overflows into app sandbox at 0x20040000")

    .app_sandbox 0x20040000 (NOLOAD) :
    {
        . = ALIGN(32);
        _app_sandbox_start = .;
        *(.app_sandbox)
        . = ALIGN(32);
        _app_sandbox_end = .;
    } > RAM

    ASSERT(_app_sandbox_end <= 0x20060000, "App sandbox overflows into kernel stack zone")

    _stack_top = ORIGIN(RAM) + LENGTH(RAM);

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.debug_*)
    }
}
