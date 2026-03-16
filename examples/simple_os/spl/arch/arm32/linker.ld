/*
 * linker.ld — Linker script for ARM32 SimpleOS kernel (QEMU virt)
 *
 * Part of the SimpleOS L4 microkernel Simple language implementation.
 *
 * Kernel is loaded at 0x40000000 (RAM base for QEMU -M virt).
 */

ENTRY(_start)

SECTIONS
{
    /* Load address: QEMU virt RAM base */
    . = 0x40000000;

    _kernel_start = .;

    /* ── Exception vector table (must be 32-byte aligned) ──────── */
    .vectors ALIGN(32) :
    {
        *(.vectors)
    }

    /* ── Code ──────────────────────────────────────────────────── */
    .text ALIGN(4096) :
    {
        *(.text)
        *(.text.*)
    }

    /* ── Read-only data ────────────────────────────────────────── */
    .rodata ALIGN(4096) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    /* ── Initialised data ──────────────────────────────────────── */
    .data ALIGN(4096) :
    {
        *(.data)
        *(.data.*)
    }

    /* ── Uninitialised data (BSS) ──────────────────────────────── */
    .bss ALIGN(4096) :
    {
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(COMMON)
        _bss_end = .;
    }

    /* ── Kernel stacks (SVC + IRQ + ABT + UND + FIQ) ───────────── */
    .stack ALIGN(4096) :
    {
        _stack_bottom = .;
        . += 16384;     /* SVC stack  */
        . += 4096;      /* IRQ stack  */
        . += 4096;      /* ABT stack  */
        . += 4096;      /* UND stack  */
        . += 4096;      /* FIQ stack  */
        _stack_top = .;
    }

    /* ── Page table storage (L1 must be 16 KB aligned) ─────────── */
    .page_tables ALIGN(16384) :
    {
        _page_tables_start = .;
        *(.page_tables)
        _page_tables_end = .;
    }

    _kernel_end = .;

    /* ── Discard unwanted sections ─────────────────────────────── */
    /DISCARD/ :
    {
        *(.comment)
        *(.note)
        *(.note.*)
        *(.eh_frame)
        *(.ARM.exidx*)
        *(.ARM.attributes*)
    }
}
