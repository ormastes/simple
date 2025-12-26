/* Linker script for RISC-V embedded
 *
 * Configure MEMORY section for your specific chip.
 * Example values are for QEMU virt machine.
 */

ENTRY(_start)

/* Memory layout - CUSTOMIZE FOR YOUR CHIP */
MEMORY
{
  /* For QEMU virt, RAM starts at 0x80000000 */
  /* For ESP32-C3, flash is at 0x42000000, RAM at 0x3FC80000 */
  FLASH (rx)  : ORIGIN = 0x80000000, LENGTH = 16M
  RAM   (rwx) : ORIGIN = 0x81000000, LENGTH = 16M
}

/* Stack and heap sizes - CUSTOMIZE AS NEEDED */
__stack_size = 65536;
__heap_size = 1048576;

SECTIONS
{
  /* Startup code at the entry point */
  .init ORIGIN(FLASH) :
  {
    KEEP(*(.init.boot))
  } > FLASH

  /* Trap handler */
  .trap :
  {
    . = ALIGN(4);
    KEEP(*(.trap.handler))
  } > FLASH

  /* Code */
  .text :
  {
    *(.text .text.*)
  } > FLASH

  /* Read-only data */
  .rodata :
  {
    *(.rodata .rodata.*)
    *(.srodata .srodata.*)
  } > FLASH

  /* Initialized data (copied from flash to RAM at startup) */
  .data : AT(__data_load)
  {
    __data_start = .;
    *(.data .data.*)
    *(.sdata .sdata.*)
    . = ALIGN(8);
    __data_end = .;
  } > RAM
  __data_load = LOADADDR(.data);

  /* Small data section for GP-relative addressing */
  .sdata :
  {
    __global_pointer$ = . + 0x800;
    *(.sdata .sdata.*)
  } > RAM

  /* Uninitialized data (zeroed at startup) */
  .bss (NOLOAD) :
  {
    __bss_start = .;
    *(.bss .bss.*)
    *(.sbss .sbss.*)
    *(COMMON)
    . = ALIGN(8);
    __bss_end = .;
  } > RAM

  /* Heap */
  .heap (NOLOAD) :
  {
    . = ALIGN(16);
    __heap_start = .;
    . = . + __heap_size;
    __heap_end = .;
  } > RAM

  /* Stack (grows downward) */
  .stack (NOLOAD) :
  {
    . = ALIGN(16);
    __stack_bottom = .;
    . = . + __stack_size;
    __stack_top = .;
  } > RAM

  /* Discard debug sections to reduce size */
  /DISCARD/ :
  {
    *(.debug*)
    *(.comment)
    *(.riscv.attributes)
  }
}

/* Provide default values for symbols if not defined */
PROVIDE(__stack_top = ORIGIN(RAM) + LENGTH(RAM));
