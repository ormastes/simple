/* CRZ Cosmos+ OpenSSD (Zynq-7000) bring-up linker script.
 *
 * Loaded into DDR at 0x00100000 (1 MB in — below this is OCM/vectors/reserved on Zynq).
 * For `qemu-system-arm -M xilinx-zynq-a9 -kernel <elf>`. Output: ELF32 ARM little-endian.
 */

OUTPUT_ARCH(arm)
OUTPUT_FORMAT("elf32-littlearm")
ENTRY(_start)

MEMORY {
    DDR (rwx) : ORIGIN = 0x00100000, LENGTH = 64M
}

SECTIONS {
    . = 0x00100000;
    .text : ALIGN(8) {
        KEEP(*(.text.start))
        *(.text*)
    } > DDR
    .rodata : ALIGN(8) { *(.rodata*) } > DDR
    .data   : ALIGN(8) { *(.data*) } > DDR
    .bss (NOLOAD) : ALIGN(8) {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        _ebss = .;
    } > DDR
    . = ALIGN(16);
    . += 0x10000;       /* 64 KB boot stack */
    _stack_top = .;
}
