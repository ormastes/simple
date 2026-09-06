/* StarFive JH7110 SimpleOS — U-Boot/OpenSBI S-mode RAM image. */
OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(__starfive_image_entry)

MEMORY {
    RAM (rwx) : ORIGIN = 0x40200000, LENGTH = 126M
}

SECTIONS {
    __starfive_image_entry = ORIGIN(RAM);
    .text : ALIGN(4K) {
        KEEP(*(.text.entry))
        *(.text.trap)
        *(.text*)
    } > RAM
    .rodata : ALIGN(4K) { *(.rodata*) *(.srodata*) } > RAM
    .simple_sandbox : ALIGN(4K) {
        __simple_sandbox_start = .;
        KEEP(*(.simple.sandbox*))
        KEEP(*(.simple.mpu*))
        __simple_sandbox_end = .;
    } > RAM
    .data : ALIGN(4K) {
        *(.data*) *(.sdata*)
        PROVIDE(__global_pointer$ = . + 0x800);
    } > RAM
    .bss (NOLOAD) : ALIGN(4K) {
        _sbss = .;
        *(.bss*) *(.sbss*) *(COMMON)
        _ebss = .;
    } > RAM
    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 64K;
        _stack_top = .;
    } > RAM
    _kernel_end = .;
    /DISCARD/ : { *(.note*) *(.eh_frame*) *(.comment) }
}
