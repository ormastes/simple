/*
 * x86 Kernel Linker Script
 *
 * Loads the kernel at physical address 1 MB (0x00100000).
 * All sections are page-aligned (4 KB).
 * Provides symbols for kernel bounds and BSS clearing.
 */

ENTRY(_start)

SECTIONS
{
    /* Kernel loaded at 1 MB */
    . = 0x00100000;

    /* Export kernel start address */
    _kernel_start = .;

    /* ---- Multiboot header (must be in first 8KB) ---- */
    .multiboot ALIGN(4) :
    {
        *(.multiboot)
    }

    /* ---- Executable code ---- */
    .text ALIGN(4096) :
    {
        _text_start = .;
        *(.text)
        *(.text.*)
        _text_end = .;
    }

    /* ---- Read-only data ---- */
    .rodata ALIGN(4096) :
    {
        _rodata_start = .;
        *(.rodata)
        *(.rodata.*)
        _rodata_end = .;
    }

    /* ---- Initialized read-write data ---- */
    .data ALIGN(4096) :
    {
        _data_start = .;
        *(.data)
        *(.data.*)
        _data_end = .;
    }

    /* ---- Uninitialized data (zeroed at boot) ---- */
    .bss ALIGN(4096) :
    {
        _bss_start = .;
        *(COMMON)
        *(.bss)
        *(.bss.*)
        _bss_end = .;
    }

    /* ---- Kernel stack ---- */
    .stack ALIGN(4096) :
    {
        _stack_start = .;
        *(.stack)
        _stack_end = .;
    }

    /* ---- Page tables (statically allocated) ---- */
    .page_tables ALIGN(4096) :
    {
        _page_tables_start = .;
        *(.page_tables)
        _page_tables_end = .;
    }

    /* Export kernel end address (page-aligned) */
    . = ALIGN(4096);
    _kernel_end = .;

    /* ---- Sections to discard ---- */
    /DISCARD/ :
    {
        *(.comment)
        *(.note)
        *(.note.*)
        *(.eh_frame)
        *(.eh_frame_hdr)
    }
}
