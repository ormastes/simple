/*
 * linker.ld — Linker script for AArch64 SimpleOS kernel
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Kernel is loaded at 0x40000000 (QEMU -M virt RAM base).
 */

OUTPUT_FORMAT(elf64-littleaarch64)
OUTPUT_ARCH(aarch64)
ENTRY(_start)

SECTIONS
{
    /* Load address: QEMU virt RAM start */
    . = 0x40000000;

    _kernel_start = .;

    /* ── Boot code (must be first) ──────────────────────────────── */
    .text.boot ALIGN(4096) :
    {
        *(.text.boot)
    }

    /* ── Exception vector table (2048-byte aligned) ─────────────── */
    .vectors ALIGN(2048) :
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

    /* ── Kernel stack (16 KB) ──────────────────────────────────── */
    .stack ALIGN(4096) :
    {
        _stack_bottom = .;
        . += 16384;
        _stack_top = .;
    }

    /* ── Page table storage ────────────────────────────────────── */
    .page_tables ALIGN(4096) :
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
    }
}
