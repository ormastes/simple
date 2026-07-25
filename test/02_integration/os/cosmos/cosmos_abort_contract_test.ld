OUTPUT_ARCH(arm)
OUTPUT_FORMAT("elf32-littlearm")
ENTRY(_start)

MEMORY {
    RAM (rwx) : ORIGIN = 0x00100000, LENGTH = 0x00040000
}

SECTIONS {
    . = ORIGIN(RAM);
    .text : ALIGN(4) {
        KEEP(*(.text.start))
        *(.text*)
    } > RAM
    .rodata : ALIGN(4) { *(.rodata*) } > RAM
    .data : ALIGN(4) { *(.data*) } > RAM
    .bss (NOLOAD) : ALIGN(8) {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        _ebss = .;
    } > RAM
    .irq_stacks (NOLOAD) : ALIGN(16) {
        . += 0x400;
        _irq_stack_cpu0_top = .;
        . += 0x400;
        _irq_stack_cpu1_top = .;
    } > RAM
    .stack (NOLOAD) : ALIGN(16) {
        . += 0x1000;
        _stack_top = .;
    } > RAM
}
