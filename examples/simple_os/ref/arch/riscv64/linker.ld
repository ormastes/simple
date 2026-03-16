/*
 * linker.ld — Linker script for RISC-V 64-bit SimpleOS kernel
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Kernel is loaded at 0x80000000 (DRAM base on QEMU virt).
 * Output format: elf64-littleriscv
 */

OUTPUT_FORMAT("elf64-littleriscv")
OUTPUT_ARCH(riscv)
ENTRY(_start)

SECTIONS
{
    /* Load address: DRAM base on QEMU virt */
    . = 0x80000000;

    _kernel_start = .;

    /* ── Code ──────────────────────────────────────────────────── */
    .text ALIGN(4096) :
    {
        *(.text.entry)
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
        *(.sdata)
        *(.sdata.*)
    }

    /* ── Uninitialised data (BSS) ──────────────────────────────── */
    .bss ALIGN(4096) :
    {
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(.sbss)
        *(.sbss.*)
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
