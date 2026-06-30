/*
 * ARM Cortex-M Startup Code (crt0.s)
 *
 * Minimal bare-metal startup for ARM Cortex-M processors.
 * Tested on: STM32F4xx (Cortex-M4F), LM3S6965 (Cortex-M3 in QEMU)
 *
 * Memory Layout:
 *   0x08000000 - Flash (512KB-2MB)
 *   0x20000000 - SRAM (64KB-256KB)
 *   0xE000E000 - System Control Block + NVIC
 *
 * This file provides:
 *   - Vector table with initial SP and reset handler
 *   - Reset handler (copies .data, zeros .bss, calls main)
 *   - Default exception handlers
 */

    .syntax unified
    .cpu cortex-m4
    .fpu fpv4-sp-d16
    .thumb

    .global vtable
    .global reset_handler
    .global default_handler

/*
 * Stack Configuration
 * Linker script will define _stack_top at the end of RAM
 */
    .equ STACK_SIZE, 0x2000     /* 8KB stack */

/*
 * Vector Table
 *
 * Entry 0: Initial stack pointer (loaded into SP on reset)
 * Entry 1: Reset handler address
 * Entries 2-15: Core exception handlers
 * Entries 16+: External interrupt handlers (device-specific)
 */
    .section .vector_table,"a",%progbits
    .type vtable, %object
    .align 9                     /* 512-byte alignment for VTOR */
vtable:
    .word _stack_top             /* 0x00: Initial stack pointer */
    .word reset_handler + 1      /* 0x04: Reset handler (Thumb bit set) */
    .word nmi_handler + 1        /* 0x08: NMI */
    .word hard_fault_handler + 1 /* 0x0C: Hard fault */
    .word mem_manage_handler + 1 /* 0x10: Memory management fault */
    .word bus_fault_handler + 1  /* 0x14: Bus fault */
    .word usage_fault_handler + 1 /* 0x18: Usage fault */
    .word 0                      /* 0x1C: Reserved */
    .word 0                      /* 0x20: Reserved */
    .word 0                      /* 0x24: Reserved */
    .word 0                      /* 0x28: Reserved */
    .word svcall_handler + 1     /* 0x2C: SVCall */
    .word debug_mon_handler + 1  /* 0x30: Debug monitor */
    .word 0                      /* 0x34: Reserved */
    .word pendsv_handler + 1     /* 0x38: PendSV */
    .word systick_handler + 1    /* 0x3C: SysTick */

    /* External interrupts (240 max for Cortex-M4) */
    .rept 240
    .word default_handler + 1
    .endr

    .size vtable, . - vtable

/*
 * Reset Handler
 *
 * Called on power-on reset or hardware reset.
 * Responsibilities:
 *   1. Copy .data section from flash to RAM
 *   2. Zero .bss section
 *   3. Enable FPU (Cortex-M4F only)
 *   4. Call main()
 *   5. If main returns, loop forever
 */
    .section .text.reset_handler
    .weak reset_handler
    .type reset_handler, %function
reset_handler:
    /* Set stack pointer (redundant, but ensures SP is correct) */
    ldr r0, =_stack_top
    mov sp, r0

    /* Copy .data section from flash to RAM */
    ldr r0, =_sidata        /* Start of data in flash */
    ldr r1, =_sdata         /* Start of data in RAM */
    ldr r2, =_edata         /* End of data in RAM */

    movs r3, #0
    b .Ldata_copy_check

.Ldata_copy_loop:
    ldr r4, [r0, r3]        /* Read from flash */
    str r4, [r1, r3]        /* Write to RAM */
    adds r3, r3, #4

.Ldata_copy_check:
    adds r4, r1, r3
    cmp r4, r2
    bcc .Ldata_copy_loop    /* Continue if r1+r3 < r2 */

    /* Zero .bss section */
    ldr r0, =_sbss          /* Start of BSS */
    ldr r1, =_ebss          /* End of BSS */

    movs r2, #0
    b .Lbss_zero_check

.Lbss_zero_loop:
    str r2, [r0]            /* Write zero */
    adds r0, r0, #4

.Lbss_zero_check:
    cmp r0, r1
    bcc .Lbss_zero_loop     /* Continue if r0 < r1 */

    /* Enable FPU (Cortex-M4F only) */
    /* CPACR at 0xE000ED88 - Coprocessor Access Control Register */
    ldr r0, =0xE000ED88
    ldr r1, [r0]
    orr r1, r1, #(0xF << 20)  /* Enable CP10 and CP11 (FPU) */
    str r1, [r0]
    dsb                       /* Data Synchronization Barrier */
    isb                       /* Instruction Synchronization Barrier */

    /* Call C/Simple runtime initialization */
    bl __spl_start_bare       /* Defined in crt_baremetal.c */

    /* If main returns, loop forever */
.Lreset_loop:
    b .Lreset_loop

    .size reset_handler, . - reset_handler

/*
 * Default Exception Handler
 *
 * Infinite loop for unhandled exceptions.
 * In a real system, would log error information or trigger a reset.
 */
    .section .text.default_handler,"ax",%progbits
default_handler:
.Ldefault_loop:
    b .Ldefault_loop
    .size default_handler, . - default_handler

/*
 * Core Exception Handlers
 *
 * These are weak symbols - can be overridden by application code.
 * Default behavior: infinite loop (call default_handler).
 */
    .macro def_irq_handler handler_name
    .weak \handler_name
    .thumb_set \handler_name, default_handler
    .endm

    def_irq_handler nmi_handler
    def_irq_handler hard_fault_handler
    def_irq_handler mem_manage_handler
    def_irq_handler bus_fault_handler
    def_irq_handler usage_fault_handler
    def_irq_handler svcall_handler
    def_irq_handler debug_mon_handler
    def_irq_handler pendsv_handler
    def_irq_handler systick_handler

/*
 * Hard Fault Handler (Enhanced for Debugging)
 *
 * Reads fault status registers and stores them in a struct
 * for inspection with a debugger.
 */
    .section .text.hard_fault_handler_enhanced
    .weak hard_fault_handler_enhanced
    .type hard_fault_handler_enhanced, %function
hard_fault_handler_enhanced:
    /* Save fault information */
    ldr r0, =0xE000ED28     /* CFSR - Configurable Fault Status Register */
    ldr r1, [r0]
    ldr r2, =fault_info
    str r1, [r2, #0]        /* Store CFSR */

    ldr r0, =0xE000ED2C     /* HFSR - Hard Fault Status Register */
    ldr r1, [r0]
    str r1, [r2, #4]        /* Store HFSR */

    ldr r0, =0xE000ED30     /* DFSR - Debug Fault Status Register */
    ldr r1, [r0]
    str r1, [r2, #8]        /* Store DFSR */

    ldr r0, =0xE000ED34     /* MMFAR - MemManage Fault Address Register */
    ldr r1, [r0]
    str r1, [r2, #12]       /* Store MMFAR */

    ldr r0, =0xE000ED38     /* BFAR - BusFault Address Register */
    ldr r1, [r0]
    str r1, [r2, #16]       /* Store BFAR */

    /* Trigger breakpoint for debugger */
    bkpt #0

    /* Loop forever */
.Lhf_loop:
    b .Lhf_loop
    .size hard_fault_handler_enhanced, . - hard_fault_handler_enhanced

/*
 * Fault Information Structure
 *
 * Stores fault status registers for debugging.
 */
    .section .bss.fault_info
    .align 4
fault_info:
    .space 20               /* 5 registers × 4 bytes */

/*
 * System Control Block Registers (for reference)
 *
 * CPACR:  0xE000ED88 - Coprocessor Access Control Register
 * CFSR:   0xE000ED28 - Configurable Fault Status Register
 * HFSR:   0xE000ED2C - Hard Fault Status Register
 * DFSR:   0xE000ED30 - Debug Fault Status Register
 * MMFAR:  0xE000ED34 - MemManage Fault Address Register
 * BFAR:   0xE000ED38 - BusFault Address Register
 * AFSR:   0xE000ED3C - Auxiliary Fault Status Register
 */
