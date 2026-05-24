/*
 * Cortex-M33 Linker Script — QEMU MPS2-AN505
 *
 * Memory Layout:
 *   FLASH (SSRAM1 secure): 0x10000000 - 0x10400000 (4 MB)
 *   RAM   (SRAM):           0x20000000 - 0x20008000 (32 KB)
 *
 * For STM32U585 (Arduino UNO Q), change to:
 *   FLASH: 0x08000000, LENGTH = 2M
 *   RAM:   0x20000000, LENGTH = 786K
 */

ENTRY(Reset_Handler)

MEMORY
{
    FLASH (rx)  : ORIGIN = 0x10000000, LENGTH = 4M
    RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 32K
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

    ASSERT(_heap_start <= 0x20006000, "BSS overflows into app sandbox at 0x20006000")

    /* App sandbox at fixed address — non-overlapping with kernel RAM.
     * QEMU AN505 ignores ARMv8-M MPU region priority for AP/XN bits,
     * so we must avoid region overlaps entirely.
     *   0x20000000 – 0x20005FFF  Kernel data (Region 1, priv-only during exec)
     *   0x20006000 – 0x200069FF  App sandbox  (Region 5, any-priv during exec)
     *   0x20006A00 – 0x20007FFF  Kernel stack (Region 4, priv-only during exec)
     */
    .app_sandbox 0x20006000 (NOLOAD) :
    {
        . = ALIGN(32);
        _app_sandbox_start = .;
        *(.app_sandbox)
        . = ALIGN(32);
        _app_sandbox_end = .;
    } > RAM

    ASSERT(_app_sandbox_end <= 0x20006A00, "App sandbox overflows into kernel stack zone")

    _stack_top = ORIGIN(RAM) + LENGTH(RAM);

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.debug_*)
    }
}
