/*
 * linker64.ld — Linker script for x86_64 64-bit kernel payload
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * This is the STAGE 1 linker script used to build kernel64.elf,
 * which contains only the 64-bit kernel code.  The boot_wrapper.S
 * (compiled as 32-bit) embeds the flat-binary form of this ELF
 * and handles the Multiboot header + 32→64 mode transition.
 *
 * Layout: loaded at 0x00101000 (1 MB + 4 KB), leaving room for the
 * 32-bit boot wrapper's multiboot header + trampoline at 0x00100000.
 */

OUTPUT_FORMAT(elf64-x86-64)
ENTRY(_start64)

SECTIONS
{
    /* 64-bit payload starts at 1 MB + 4 KB.
     * The first 4 KB (0x100000..0x100FFF) is reserved for the
     * 32-bit boot wrapper (multiboot header + trampoline). */
    . = 0x00101000;

    _kernel64_start = .;

    /* ── Code ──────────────────────────────────────────────────── */
    /* entry64.o MUST come first so _start64 is at the very start
     * of .text (address 0x101000).  The boot_wrapper.S trampoline
     * jumps to 0x101000 after switching to long mode. */
    .text ALIGN(16) :
    {
        *entry64.o(.text)
        *(.text)
        *(.text.*)
    }

    /* ── Read-only data ────────────────────────────────────────── */
    .rodata ALIGN(16) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    /* ── Initialised data ──────────────────────────────────────── */
    .data ALIGN(16) :
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
    .stack ALIGN(16) :
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

    _kernel64_end = .;

    /* ── Discard unwanted sections ─────────────────────────────── */
    /DISCARD/ :
    {
        *(.comment)
        *(.note)
        *(.note.*)
        *(.eh_frame)
        *(.multiboot)
    }
}
