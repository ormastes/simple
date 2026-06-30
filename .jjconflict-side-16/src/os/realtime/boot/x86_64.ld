/* Realtime Simple OS — x86_64 (QEMU q35) linker script */
/* Kernel loaded at 1M, 2M available */

MEMORY
{
    KERNEL (rwx) : ORIGIN = 0x100000, LENGTH = 2M
}

SECTIONS
{
    .text : {
        *(.text*)
        *(.rodata*)
        . = ALIGN(4096);
    } > KERNEL

    .data : {
        __data_start = .;
        *(.data*)
        . = ALIGN(4096);
        __data_end = .;
    } > KERNEL

    .bss (NOLOAD) : {
        __bss_start = .;
        *(.bss*)
        *(COMMON)
        . = ALIGN(4096);
        __bss_end = .;
    } > KERNEL

    .rtos_state (NOLOAD) : {
        __rtos_state_start = .;
        KEEP(*(.rtos_state))
        . = ALIGN(4096);
        __rtos_state_end = .;
    } > KERNEL

    .task_stacks (NOLOAD) : {
        __task_stacks_start = .;
        . = . + 0x10000;
        __task_stacks_end = .;
    } > KERNEL

    .kernel_stack (NOLOAD) : {
        . = ALIGN(16);
        __kernel_stack_bottom = .;
        . = . + 0x2000;
        __kernel_stack_top = .;
    } > KERNEL

    _end = .;
}
