/* SimpleOS x86_64 userspace linker script
 *
 * Text starts at 0x10000000 — matches kernel bump allocator base.
 * Static linking only (no GOT/PLT).
 */
ENTRY(_start)

SECTIONS {
    . = 0x10000000;

    .text : {
        *(.text.entry)
        *(.text .text.*)
    }

    . = ALIGN(4096);
    .rodata : {
        *(.rodata .rodata.*)
    }

    . = ALIGN(4096);
    .data : {
        *(.data .data.*)
        *(.sdata .sdata.*)
    }

    . = ALIGN(16);
    .init_array : {
        __init_array_start = .;
        KEEP(*(.init_array .init_array.*))
        __init_array_end = .;
    }

    . = ALIGN(16);
    .fini_array : {
        __fini_array_start = .;
        KEEP(*(.fini_array .fini_array.*))
        __fini_array_end = .;
    }

    . = ALIGN(16);
    .tdata : {
        _tls_start = .;
        *(.tdata .tdata.*)
    }

    . = ALIGN(16);
    .tbss : {
        *(.tbss .tbss.*)
        _tls_end = .;
    }

    . = ALIGN(4096);
    .bss : {
        __bss_start = .;
        *(.bss .bss.*)
        *(.sbss .sbss.*)
        *(COMMON)
        __bss_end = .;
    }

    _end = .;

    /DISCARD/ : {
        *(.comment)
        *(.note .note.*)
        *(.eh_frame)
        *(.eh_frame_hdr)
        *(.got)
        *(.got.plt)
        *(.plt)
        *(.rela.plt)
    }
}
