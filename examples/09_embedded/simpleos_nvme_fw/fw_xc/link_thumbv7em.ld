/* fw_xc thumbv7em (Cortex-M4F) memory map: QEMU mps2-an386 / typical MCU.
   Code at 0x00000000 (vector table first), SRAM at 0x20000000. */
ENTRY(_start)
MEMORY {
  FLASH (rx) : ORIGIN = 0x00000000, LENGTH = 0x00080000
  RAM (rwx)  : ORIGIN = 0x20000000, LENGTH = 0x00020000
}
SECTIONS {
  .text : { KEEP(*(.vectors)) KEEP(*(.text.entry)) *(.text .text.*) *(.rodata .rodata.*) } > FLASH
  /* No .data copy loop in crt0: initialised globals are not supported yet. */
  .data : { *(.data .data.*) } > RAM AT > FLASH
  ASSERT(SIZEOF(.data) == 0, "fw_xc thumbv7em: .data needs a FLASH->RAM copy loop in crt0")
  .bss (NOLOAD) : ALIGN(4) { _sbss = .; *(.bss .bss.* COMMON) . = ALIGN(4); _ebss = .; } > RAM
  _stack_top = ORIGIN(RAM) + LENGTH(RAM);
  /DISCARD/ : { *(.comment) *(.note*) *(.ARM.exidx*) *(.eh_frame*) }
}
