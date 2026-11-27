/* SimpleOS aarch64 userspace linker script
 *
 * Text starts at 0x50000000 — the first byte clear of the arm64 fs-exec
 * kernel band [0x40200000, 0x50000000) (QEMU virt RAM base 0x40000000).
 * Static linking only.
 */
ENTRY(_start)

SECTIONS {
    . = 0x50000000;

    .text : {
        *(.text.entry)
        *(.text .text.*)
    }

    . = ALIGN(4096);
    .rodata : {
        *(.rodata .rodata.*)
    }

    /* C++ exception unwinding tables — kept for baremetal libunwind
     * boundary-symbol lookup (no dynamic loader / dl_iterate_phdr). */
    . = ALIGN(8);
    .eh_frame_hdr : {
        __eh_frame_hdr_start = .;
        KEEP(*(.eh_frame_hdr))
        __eh_frame_hdr_end = .;
    }

    . = ALIGN(8);
    .eh_frame : {
        __eh_frame_start = .;
        KEEP(*(.eh_frame))
        __eh_frame_end = .;
    }

    . = ALIGN(4096);
    .data : {
        *(.data .data.*)
        *(.sdata .sdata.*)
    }

    /* Static-link GOT: keep it placed (NOT discarded) so absolute target
     * VAs get baked into real load addresses (same rationale as x86_64). */
    . = ALIGN(8);
    .got : {
        *(.got) *(.got.*)
    }

    . = ALIGN(8);
    .got.plt : {
        *(.got.plt)
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
        *(.plt)
        *(.rela.plt)
    }
}
