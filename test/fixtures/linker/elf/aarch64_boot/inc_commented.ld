ENTRY(_start)
/* disabled:
INCLUDE "test/fixtures/linker/elf/aarch64_boot/missing.ld"
*/
SECTIONS { . = 0x40200000; .text : { *(.text*) } }
