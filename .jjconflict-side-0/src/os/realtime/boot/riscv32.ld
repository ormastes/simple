/* Realtime Simple OS — RISC-V RV32 (QEMU virt) linker script */
/* 128M DRAM at 0x80000000 */

MEMORY
{
    DRAM (rwx) : ORIGIN = 0x80000000, LENGTH = 128M
}

SECTIONS
{
    .text : {
        *(.text.entry)
        *(.text*)
        *(.rodata*)
        . = ALIGN(4);
    } > DRAM

    .data : {
        __data_start = .;
        *(.data*)
        . = ALIGN(4);
        __data_end = .;
    } > DRAM

    .bss (NOLOAD) : {
        __bss_start = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4);
        __bss_end = .;
    } > DRAM

    .rtos_state (NOLOAD) : {
        __rtos_state_start = .;
        KEEP(*(.rtos_state))
        . = ALIGN(4);
        __rtos_state_end = .;
    } > DRAM

    .task_stacks (NOLOAD) : {
        __task_stacks_start = .;
        . = . + 0x4000;
        __task_stacks_end = .;
    } > DRAM

    .kernel_stack (NOLOAD) : {
        . = ALIGN(16);
        __kernel_stack_bottom = .;
        . = . + 0x1000;
        __kernel_stack_top = .;
    } > DRAM

    _end = .;
}
