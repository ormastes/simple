/* Realtime Simple OS — ARM Cortex-M3 (lm3s6965evb) linker script */
/* 256K Flash at 0x00000000, 64K SRAM at 0x20000000 */

MEMORY
{
    FLASH (rx)  : ORIGIN = 0x00000000, LENGTH = 256K
    SRAM  (rwx) : ORIGIN = 0x20000000, LENGTH = 64K
}

SECTIONS
{
    .text : {
        KEEP(*(.vector_table))
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
    } > FLASH

    .data : AT(LOADADDR(.text) + SIZEOF(.text)) {
        __data_start = .;
        *(.data*)
        . = ALIGN(4);
        __data_end = .;
    } > SRAM

    .bss (NOLOAD) : {
        __bss_start = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        __bss_end = .;
    } > SRAM

    .rtos_state (NOLOAD) : {
        __rtos_state_start = .;
        KEEP(*(.rtos_state))
        . = ALIGN(4);
        __rtos_state_end = .;
    } > SRAM

    /* Task stacks: 1K each, 16 tasks max = 16K */
    .task_stacks (NOLOAD) : {
        __task_stacks_start = .;
        . = . + 0x4000;
        __task_stacks_end = .;
    } > SRAM

    /* Kernel stack (MSP) */
    .kernel_stack (NOLOAD) : {
        . = ALIGN(8);
        __kernel_stack_bottom = .;
        . = . + 0x400;
        __kernel_stack_top = .;
    } > SRAM

    _end = .;
    __heap_start = .;
}
