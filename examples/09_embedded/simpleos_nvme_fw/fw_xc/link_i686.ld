/* fw_xc i686 memory map: RAM at 0x00100000, 0x00100000 bytes. Board: change ORIGIN/LENGTH. */
ENTRY(_start)
MEMORY { RAM (rwx) : ORIGIN = 0x00100000, LENGTH = 0x00100000 }
SECTIONS {
  .text : { KEEP(*(.text.entry)) *(.text .text.*) } > RAM
  .rodata : { *(.rodata .rodata.*) } > RAM
  .data : { *(.data .data.* .sdata .sdata.*) } > RAM
  .bss (NOLOAD) : ALIGN(8) { _sbss = .; *(.bss .bss.* .sbss .sbss.* COMMON) . = ALIGN(8); _ebss = .; } > RAM
  . = ALIGN(16);
  . = . + 0x4000;
  _stack_top = .;
  /DISCARD/ : { *(.comment) *(.note*) *(.eh_frame*) *(.ARM.exidx*) }
}
