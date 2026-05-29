/* x86 Linker Script for Multiboot */
ENTRY(_start)

SECTIONS
{
    /* Load at 1 MB (standard for Multiboot) */
    . = 1M;

    .multiboot ALIGN(4K) : {
        *(.multiboot)
    }

    .text ALIGN(4K) : {
        *(.text)
    }

    .rodata ALIGN(4K) : {
        *(.rodata)
    }

    .data ALIGN(4K) : {
        *(.data)
    }

    .bss ALIGN(4K) : {
        *(.bss)
    }
}
