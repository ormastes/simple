/*
 * linker.ld — Linker script for x86_64 SimpleOS kernel
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Kernel is loaded at physical address 1 MB (0x00100000) by the
 * Multiboot-compliant bootloader (e.g. GRUB).
 * Output format: ELF64 for x86-64.
 */

OUTPUT_FORMAT(elf64-x86-64)
ENTRY(_start)

SECTIONS
{
    /* Load address: 1 MB */
    . = 0x00100000;

    _kernel_start = .;

    /* ── Multiboot header (must be in first 8 KB) ─────────────── */
    .multiboot ALIGN(4) :
    {
        *(.multiboot)
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
