/* Minimal Multiboot1 layout for the UP Squared first-light kernel. */
ENTRY(_entry32)
EXTERN(_entry32)

SECTIONS
{
    /* Leave low memory available to the vendor UEFI GRUB relocator. */
    . = 0x08000000;
    _kernel_start = .;

    .text ALIGN(4K) :
    {
        KEEP(*(.text.entry))
        KEEP(*(.multiboot))
        *(.text)
        *(.text.*)
    }
    .rodata ALIGN(4K) : { *(.rodata) *(.rodata.*) }
    .data ALIGN(4K) : { *(.data) *(.data.*) }

    .bss ALIGN(4K) :
    {
        __bss_start = .;
        *(COMMON)
        *(.bss)
        *(.bss.*)
        __bss_end = .;
    }

    .heap ALIGN(4K) (NOLOAD) :
    {
        __heap_start = .;
        . = . + 16M;
        __heap_end = .;
    }

    .stack ALIGN(4K) (NOLOAD) :
    {
        . = . + 8M;
        _stack_top = .;
    }
    _kernel_end = .;

    .debug_info 0 : { *(.debug_info) }
    .debug_abbrev 0 : { *(.debug_abbrev) }
    .debug_line 0 : { *(.debug_line) }
    .debug_str 0 : { *(.debug_str) }
    .debug_frame 0 : { *(.debug_frame) }
    .debug_loc 0 : { *(.debug_loc) }
    .debug_ranges 0 : { *(.debug_ranges) }

    /DISCARD/ : { *(.note*) *(.eh_frame*) *(.comment) }
}
