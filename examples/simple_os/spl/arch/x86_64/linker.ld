/*
 * linker.ld — Linker script for x86_64 SimpleOS kernel
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * Kernel loaded at 1 MB (0x00100000). Output: ELF64 x86-64.
 */

OUTPUT_FORMAT(elf64-x86-64)
ENTRY(_start)

SECTIONS
{
    . = 0x00100000;

    _kernel_start = .;

    .multiboot ALIGN(4) :
    {
        *(.multiboot)
    }

    .text ALIGN(4096) :
    {
        *(.text)
        *(.text.*)
    }

    .rodata ALIGN(4096) :
    {
        *(.rodata)
        *(.rodata.*)
    }

    .data ALIGN(4096) :
    {
        *(.data)
        *(.data.*)
    }

    .bss ALIGN(4096) :
    {
        _bss_start = .;
        *(.bss)
        *(.bss.*)
        *(COMMON)
        _bss_end = .;
    }

    .stack ALIGN(4096) :
    {
        _stack_bottom = .;
        . += 16384;
        _stack_top = .;
    }

    .page_tables ALIGN(4096) :
    {
        _page_tables_start = .;
        *(.page_tables)
        _page_tables_end = .;
    }

    _kernel_end = .;

    /DISCARD/ :
    {
        *(.comment)
        *(.note)
        *(.note.*)
        *(.eh_frame)
    }
}
