/* ARM64/AArch64 Linker Script */
ENTRY(_start)

SECTIONS
{
    /* Load at 0x40000000 (typical for ARM64 virt machine) */
    . = 0x40000000;

    .vectors ALIGN(2K) : {
        KEEP(*(.vectors))
    }

    .text : {
        *(.text)
        *(.text.*)
    }

    .rodata : {
        *(.rodata)
        *(.rodata.*)
    }

    .simple_sandbox ALIGN(4K) : {
        __simple_sandbox_start = .;
        KEEP(*(.simple.sandbox*))
        KEEP(*(.simple.mpu*))
        __simple_sandbox_end = .;
    }

    .data : {
        *(.data)
        *(.data.*)
    }

    .bss : {
        *(.bss)
        *(.bss.*)
    }
}
