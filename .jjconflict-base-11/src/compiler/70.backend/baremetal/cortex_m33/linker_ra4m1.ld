/*
 * Cortex-M4 Linker Script — Arduino UNO R4 WiFi (Renesas RA4M1)
 *
 * Memory Layout:
 *   FLASH (Code Flash): 0x00000000 - 0x00040000 (256 KB)
 *   RAM   (SRAM):       0x20000000 - 0x20008000 (32 KB)
 *
 * PMSAv7 partition (power-of-2, overlapping priority):
 *   0x20000000 – 0x20005FFF  Kernel data  (24K, Region 1 priv-only)
 *   0x20006000 – 0x20006FFF  App sandbox  (4K, Region 5 overrides)
 *   0x20007000 – 0x20007FFF  Kernel stack (4K, covered by Region 1)
 */

ENTRY(Reset_Handler)

MEMORY
{
    FLASH (rx)  : ORIGIN = 0x00000000, LENGTH = 256K
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

    /* App sandbox at 0x20006000 — 4KB, power-of-2 aligned for PMSAv7.
     * Region 5 (higher number) overrides Region 1 (full RAM priv-only)
     * by ARMv7-M priority rules on real hardware.
     */
    .app_sandbox 0x20006000 (NOLOAD) :
    {
        . = ALIGN(32);
        _app_sandbox_start = .;
        *(.app_sandbox)
        . = ALIGN(32);
        _app_sandbox_end = .;
    } > RAM

    ASSERT(_app_sandbox_end <= 0x20007000, "App sandbox overflows into kernel stack zone")

    _stack_top = ORIGIN(RAM) + LENGTH(RAM);

    /DISCARD/ :
    {
        *(.comment)
        *(.note*)
        *(.eh_frame*)
        *(.debug_*)
    }
}
