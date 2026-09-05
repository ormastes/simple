/* Ring-3 hello-world user image.
 *
 * Every section group that differs in permission MUST start on its own page.
 * The kernel's ELF admission (_admit_raw_elf64 in hello_world_ovmf_entry.spl)
 * maps one frame per page and UNIONS the permissions of every segment covering
 * that page, so it rejects an image where an executable and a writable segment
 * share a page -- the resulting PTE would silently become W+X. Without these
 * ALIGN(0x1000) directives .text (RX, ending 0x4004b0) and .bss (RW, starting
 * 0x400500) both landed in page 0x400000 and the image was refused with
 * "[spawn] FAIL raw ELF admission rejected", even though their byte ranges are
 * disjoint.
 */
ENTRY(_start)
SECTIONS {
  . = 0x400000;
  .text : { *(.text._start) *(.text*) }
  . = ALIGN(0x1000);
  .rodata : { *(.rodata*) }
  . = ALIGN(0x1000);
  .data : { *(.data*) }
  .bss : { *(.bss*) *(COMMON) }
}
