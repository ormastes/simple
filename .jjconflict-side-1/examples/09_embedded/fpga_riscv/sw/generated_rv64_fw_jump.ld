OUTPUT_ARCH(riscv)
OUTPUT_FORMAT("elf64-littleriscv")
ENTRY(_start)

SECTIONS {
    . = 0x80000000;
    .text.fw : ALIGN(4) {
        *(.text.fw)
    }

    . = 0x80200000;
    .text.payload : ALIGN(4) {
        *(.text.payload)
    }
}
