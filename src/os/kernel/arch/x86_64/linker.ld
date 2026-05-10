/*
 * x86_64 Kernel Linker Script (Limine Boot Protocol)
 *
 * Target: x86_64 processors (QEMU, physical hardware)
 * Bootloader: Limine (higher-half kernel)
 *
 * Memory Layout:
 *   Virtual base:  0xFFFFFFFF80000000 (high-half, -2GB)
 *   Physical load:  0x100000 (1MB mark)
 *   Limine maps the kernel into the higher half and provides HHDM.
 *
 * Sections:
 *   .limine_reqs - Limine bootloader request structures (must survive strip)
 *   .text        - Executable code
 *   .rodata      - Read-only data
 *   .data        - Initialized mutable data
 *   .bss         - Uninitialized data (zeroed by boot stub)
 */

ENTRY(kernel_main)

PHDRS
{
    text    PT_LOAD FLAGS(5);  /* R-X */
    rodata  PT_LOAD FLAGS(4);  /* R-- */
    data    PT_LOAD FLAGS(6);  /* RW- */
}

SECTIONS
{
    /* Kernel virtual base in higher half */
    . = 0xFFFFFFFF80000000 + 0x100000;

    /*
     * Limine request structures.
     * These MUST be kept (KEEP) so the linker does not garbage-collect them;
     * Limine scans the binary for the magic IDs at boot time.
     */
    .limine_reqs ALIGN(4096) : AT(ADDR(.limine_reqs) - 0xFFFFFFFF80000000)
    {
        KEEP(*(.limine_reqs))
        KEEP(*(.limine_reqs.*))
    } :text

    /* Executable code */
    .text ALIGN(4096) : AT(ADDR(.text) - 0xFFFFFFFF80000000)
    {
        *(.text)
        *(.text.*)
    } :text

    /* Read-only data */
    .rodata ALIGN(4096) : AT(ADDR(.rodata) - 0xFFFFFFFF80000000)
    {
        *(.rodata)
        *(.rodata.*)
    } :rodata

    /* Initialized data */
    .data ALIGN(4096) : AT(ADDR(.data) - 0xFFFFFFFF80000000)
    {
        *(.data)
        *(.data.*)
    } :data

    /* Uninitialized data (BSS) */
    .bss ALIGN(4096) : AT(ADDR(.bss) - 0xFFFFFFFF80000000)
    {
        __bss_start = .;
        *(COMMON)
        *(.bss)
        *(.bss.*)
        __bss_end = .;
    } :data

    /* End of kernel image */
    _kernel_end = .;

    /* Debug sections (not loaded) */
    .debug_info     0 : { *(.debug_info) }
    .debug_abbrev   0 : { *(.debug_abbrev) }
    .debug_line     0 : { *(.debug_line) }
    .debug_str      0 : { *(.debug_str) }
    .debug_frame    0 : { *(.debug_frame) }
    .debug_loc      0 : { *(.debug_loc) }
    .debug_ranges   0 : { *(.debug_ranges) }

    /* Discard unwanted sections */
    /DISCARD/ :
    {
        *(.note*)
        *(.eh_frame*)
        *(.comment)
        *(.gnu.hash)
    }
}
