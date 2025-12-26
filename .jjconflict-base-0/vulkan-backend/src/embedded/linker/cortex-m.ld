/* Linker script for ARM Cortex-M
 *
 * Configure MEMORY section for your specific chip.
 * Example values are for STM32F103 (Blue Pill).
 */

ENTRY(Reset_Handler)

/* Memory layout - CUSTOMIZE FOR YOUR CHIP */
MEMORY
{
  FLASH (rx)  : ORIGIN = 0x08000000, LENGTH = 64K
  RAM   (rwx) : ORIGIN = 0x20000000, LENGTH = 20K
}

/* Stack and heap sizes - CUSTOMIZE AS NEEDED */
__stack_size = 2048;
__heap_size = 4096;

SECTIONS
{
  /* Vector table must be at the start of flash */
  .vector_table ORIGIN(FLASH) :
  {
    KEEP(*(.vector_table))
  } > FLASH

  /* Code */
  .text :
  {
    *(.reset_handler)
    *(.hard_fault_handler)
    *(.mem_fault_handler)
    *(.bus_fault_handler)
    *(.usage_fault_handler)
    *(.text .text.*)
  } > FLASH

  /* Read-only data */
  .rodata :
  {
    *(.rodata .rodata.*)
  } > FLASH

  /* Initialized data (copied from flash to RAM at startup) */
  .data : AT(__data_load)
  {
    __data_start = .;
    *(.data .data.*)
    . = ALIGN(4);
    __data_end = .;
  } > RAM
  __data_load = LOADADDR(.data);

  /* Uninitialized data (zeroed at startup) */
  .bss (NOLOAD) :
  {
    __bss_start = .;
    *(.bss .bss.*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end = .;
  } > RAM

  /* Heap */
  .heap (NOLOAD) :
  {
    . = ALIGN(8);
    __heap_start = .;
    . = . + __heap_size;
    __heap_end = .;
  } > RAM

  /* Stack (grows downward) */
  .stack (NOLOAD) :
  {
    . = ALIGN(8);
    __stack_bottom = .;
    . = . + __stack_size;
    __stack_top = .;
  } > RAM

  /* ARM exception frame info */
  .ARM.exidx :
  {
    __exidx_start = .;
    *(.ARM.exidx* .gnu.linkonce.armexidx.*)
    __exidx_end = .;
  } > FLASH

  /* Discard debug sections to reduce size */
  /DISCARD/ :
  {
    *(.debug*)
    *(.comment)
  }
}

/* Provide default values for symbols if not defined */
PROVIDE(__stack_top = ORIGIN(RAM) + LENGTH(RAM));
