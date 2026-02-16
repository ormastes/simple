/* x86_64 Linker Script for Multiboot2 */
ENTRY(_start)

SECTIONS
{
    /* Load at 2 MB (higher than x86 to avoid conflicts) */
    . = 2M;

    .multiboot2 ALIGN(8) : {
        *(.multiboot2)
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
