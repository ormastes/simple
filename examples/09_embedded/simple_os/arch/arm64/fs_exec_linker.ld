/* ARM64 SimpleOS filesystem execution acceptance linker script.
 *
 * QEMU virt places its generated device tree at the start of RAM when using
 * the generic loader device. Keep this acceptance kernel above that reserved
 * area and let the loader set the CPU PC to ENTRY(_start).
 */

OUTPUT_ARCH(aarch64)
OUTPUT_FORMAT("elf64-littleaarch64")
ENTRY(_start)

MEMORY {
    /* 768 MiB: the entry-closure image is ~236 MiB of text/rodata/data plus a
     * 512 MiB C heap (see baremetal_stubs.c _heap) and the 8 MiB stack — the
     * old 254 MiB cap overflowed the moment the heap grew (linker would place
     * sections past the region end and ld.lld rejects the overflow). QEMU
     * gives this guest 2 GiB, so 0x40200000+768 MiB = 0x70200000 stays well
     * inside RAM. */
    RAM (rwx) : ORIGIN = 0x40200000, LENGTH = 768M
}

SECTIONS {
    .text : ALIGN(4K) {
        KEEP(*(.text.entry))
        . = ALIGN(2K);
        *(.text.vectors)
        *(.text*)
    } > RAM

    .rodata : ALIGN(4K) {
        *(.rodata*)
    } > RAM

    .simple_sandbox : ALIGN(4K) {
        __simple_sandbox_start = .;
        KEEP(*(.simple.sandbox*))
        KEEP(*(.simple.mpu*))
        __simple_sandbox_end = .;
    } > RAM

    .data : ALIGN(4K) {
        *(.data*)
    } > RAM

    /* End of the LOADED image: crt0.S's self-relocation stub moves exactly
     * [_start, _kernel_load_end). Everything below is NOLOAD. */
    _kernel_load_end = .;

    .bss (NOLOAD) : ALIGN(4K) {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        _ebss = .;
    } > RAM

    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 8M;
        _stack_top = .;
    } > RAM

    .heap (NOLOAD) : ALIGN(4K) {
        __heap_start = .;
        . += 64M;
        __heap_end = .;
    } > RAM

INCLUDE "examples/09_embedded/simple_os/arch/common/linker_arm_common.ld"

/* Total in-memory footprint (text..heap), declared in the arm64 Linux Image
 * header in crt0.S so a real bootloader reserves the full span. */
_image_size = _kernel_end - _start;
}
