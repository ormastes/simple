/* SimpleOS riscv64 userspace linker script
 *
 * Text starts at 0x100000000 (Sv39 VPN[2] slot 4), separate from the kernel
 * identity mapping at 0x80200000 (slot 2). Physical user pages still come
 * from QEMU virt RAM; this address is their supervisor-managed virtual map.
 * Static linking only.
 */
ENTRY(_start)
INPUT(test/fixtures/linker/simpleos/crt0_rv64.o)

SECTIONS {
    . = 0x100000000;

    .text : {
        *(.text.entry)
        *(.text .text.*)
    }

    . = ALIGN(4096);
    .rodata : {
        *(.rodata .rodata.*)
        *(.srodata .srodata.*)
    }

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
    }

    . = ALIGN(8);
    .sdata : {
        PROVIDE(__global_pointer$ = . + 0x800);
        *(.sdata .sdata.*)
    }

    . = ALIGN(8);
    .got : {
        *(.got) *(.got.*)
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
        *(.sbss .sbss.*)
        *(.bss .bss.*)
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
