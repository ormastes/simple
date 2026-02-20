/*
 * RISC-V Bare-Metal Startup Code (crt0.s)
 *
 * Minimal bare-metal startup for RISC-V processors (RV32/RV64).
 * Tested on: QEMU virt machine, SiFive FU540
 *
 * Memory Layout (QEMU virt):
 *   0x80000000 - RAM start (2GB)
 *   0x80100000 - Kernel load address
 *   0x80200000 - Stack (grows down)
 *
 * This file provides:
 *   - Entry point after bootloader/firmware
 *   - Hart (CPU core) initialization
 *   - Stack setup
 *   - BSS zeroing
 *   - Call to main()
 */

#ifdef __riscv_xlen
# if __riscv_xlen == 64
#  define STORE sd
#  define LOAD ld
#  define REGBYTES 8
# else
#  define STORE sw
#  define LOAD lw
#  define REGBYTES 4
# endif
#else
# define STORE sw
# define LOAD lw
# define REGBYTES 4
#endif

    .section .text.start
    .global _start
    .type _start, @function

/*
 * Entry Point
 *
 * Called by bootloader with:
 *   - a0 = hart ID (hardware thread ID)
 *   - a1 = device tree blob address (optional)
 *   - Machine mode enabled
 *   - Interrupts disabled
 */
_start:
    .cfi_startproc
    .cfi_undefined ra

    /* Disable interrupts globally */
    csrw mie, zero               /* Clear MIE register */
    csrw mip, zero               /* Clear MIP register */

    /* Set up trap vector (early, before stack) */
    la t0, trap_vector
    csrw mtvec, t0               /* Set mtvec to trap_vector */

    /* Only hart 0 proceeds, others park */
    bnez a0, .Lsecondary_hart

/*
 * Primary Hart (hart 0) Initialization
 */
.Lprimary_hart:
    /* Save device tree blob address */
    la t0, dtb_addr
    STORE a1, 0(t0)

    /* Set up stack pointer */
    la sp, _stack_top
    li t0, 0
    STORE t0, 0(sp)              /* Zero initial stack frame */

    /* Configure mstatus */
    li t0, 0x1800                /* MPP = Machine mode (bits 12:11 = 11) */
    csrw mstatus, t0

    /* Zero BSS section */
    la t0, __bss_start
    la t1, __bss_end
.Lbss_zero_loop:
    bge t0, t1, .Lbss_zero_done
    STORE zero, 0(t0)
    addi t0, t0, REGBYTES
    j .Lbss_zero_loop
.Lbss_zero_done:

    /* Copy .data section from flash to RAM (if needed) */
    la t0, _sidata               /* Start of data in flash */
    la t1, _sdata                /* Start of data in RAM */
    la t2, _edata                /* End of data in RAM */
.Ldata_copy_loop:
    bge t1, t2, .Ldata_copy_done
    LOAD t3, 0(t0)
    STORE t3, 0(t1)
    addi t0, t0, REGBYTES
    addi t1, t1, REGBYTES
    j .Ldata_copy_loop
.Ldata_copy_done:

    /* Set up arguments for __spl_start_bare */
    li a0, 0                     /* argc = 0 */
    li a1, 0                     /* argv = NULL */

    /* Call C/Simple runtime initialization */
    call __spl_start_bare        /* Defined in crt_baremetal.c */

    /* If main returns, jump to exit */
    j .Lexit

/*
 * Secondary Harts (SMP support)
 *
 * Park secondary harts in WFI loop.
 * Can be woken up later by IPI (inter-processor interrupt).
 */
.Lsecondary_hart:
    /* Set up minimal stack for secondary hart */
    la sp, _stack_top
    li t0, 0x10000               /* 64KB stack per hart */
    mul t0, t0, a0               /* Offset by hart ID */
    sub sp, sp, t0

    /* Wait for interrupt (low power mode) */
.Lsecondary_loop:
    wfi
    j .Lsecondary_loop

/*
 * Exit Handler
 *
 * Disable interrupts and halt all harts.
 */
.Lexit:
    csrw mie, zero               /* Disable interrupts */
.Lhalt:
    wfi
    j .Lhalt

    .cfi_endproc
    .size _start, . - _start

/*
 * Trap Vector
 *
 * Handles exceptions and interrupts in machine mode.
 * Default behavior: save registers, call trap_handler, restore, return.
 */
    .section .text.trap
    .align 4                     /* mtvec requires 4-byte alignment */
    .global trap_vector
trap_vector:
    /* Save caller-saved registers */
    addi sp, sp, -16*REGBYTES
    STORE ra,  0*REGBYTES(sp)
    STORE t0,  1*REGBYTES(sp)
    STORE t1,  2*REGBYTES(sp)
    STORE t2,  3*REGBYTES(sp)
    STORE a0,  4*REGBYTES(sp)
    STORE a1,  5*REGBYTES(sp)
    STORE a2,  6*REGBYTES(sp)
    STORE a3,  7*REGBYTES(sp)
    STORE a4,  8*REGBYTES(sp)
    STORE a5,  9*REGBYTES(sp)
    STORE a6, 10*REGBYTES(sp)
    STORE a7, 11*REGBYTES(sp)
    STORE t3, 12*REGBYTES(sp)
    STORE t4, 13*REGBYTES(sp)
    STORE t5, 14*REGBYTES(sp)
    STORE t6, 15*REGBYTES(sp)

    /* Read trap cause */
    csrr a0, mcause              /* Trap cause */
    csrr a1, mepc                /* Exception PC */
    csrr a2, mtval               /* Trap value (faulting address, etc.) */

    /* Call trap handler */
    call trap_handler

    /* Restore caller-saved registers */
    LOAD ra,  0*REGBYTES(sp)
    LOAD t0,  1*REGBYTES(sp)
    LOAD t1,  2*REGBYTES(sp)
    LOAD t2,  3*REGBYTES(sp)
    LOAD a0,  4*REGBYTES(sp)
    LOAD a1,  5*REGBYTES(sp)
    LOAD a2,  6*REGBYTES(sp)
    LOAD a3,  7*REGBYTES(sp)
    LOAD a4,  8*REGBYTES(sp)
    LOAD a5,  9*REGBYTES(sp)
    LOAD a6, 10*REGBYTES(sp)
    LOAD a7, 11*REGBYTES(sp)
    LOAD t3, 12*REGBYTES(sp)
    LOAD t4, 13*REGBYTES(sp)
    LOAD t5, 14*REGBYTES(sp)
    LOAD t6, 15*REGBYTES(sp)
    addi sp, sp, 16*REGBYTES

    mret                         /* Return from trap */

/*
 * Default Trap Handler
 *
 * Weak symbol - can be overridden by application.
 * Default behavior: loop forever.
 */
    .section .text
    .weak trap_handler
    .type trap_handler, @function
trap_handler:
    /* Save trap info for debugging */
    la t0, trap_info
    STORE a0, 0*REGBYTES(t0)     /* mcause */
    STORE a1, 1*REGBYTES(t0)     /* mepc */
    STORE a2, 2*REGBYTES(t0)     /* mtval */

    /* Loop forever */
.Ltrap_loop:
    wfi
    j .Ltrap_loop
    .size trap_handler, . - trap_handler

/*
 * Timer Interrupt Handler
 *
 * Called for machine timer interrupts (interrupt cause = 7).
 * Weak symbol - can be overridden by application.
 */
    .weak timer_interrupt_handler
    .type timer_interrupt_handler, @function
timer_interrupt_handler:
    /* Acknowledge timer interrupt by setting mtimecmp */
    /* Implementation depends on platform (CLINT, etc.) */
    ret
    .size timer_interrupt_handler, . - timer_interrupt_handler

/*
 * External Interrupt Handler
 *
 * Called for external interrupts (interrupt cause = 11).
 * Weak symbol - can be overridden by application.
 */
    .weak external_interrupt_handler
    .type external_interrupt_handler, @function
external_interrupt_handler:
    /* Query PLIC (Platform-Level Interrupt Controller) */
    /* Implementation depends on platform */
    ret
    .size external_interrupt_handler, . - external_interrupt_handler

/*
 * Data Section
 */
    .section .data
    .align REGBYTES

/* Device tree blob address (saved from bootloader) */
    .global dtb_addr
dtb_addr:
    .space REGBYTES

/* Trap information (for debugging) */
    .align REGBYTES
trap_info:
    .space 3*REGBYTES            /* mcause, mepc, mtval */

/*
 * BSS Section
 */
    .section .bss
    .align 16

/* Boot stack */
boot_stack_bottom:
    .skip 0x4000                 /* 16KB boot stack */
boot_stack_top:

    .global _stack_top
    .weak _stack_top
_stack_top = boot_stack_top

/*
 * Weak Symbols for Linker
 *
 * These can be overridden by linker script.
 */
    .weak __bss_start
    .weak __bss_end
    .weak _sidata
    .weak _sdata
    .weak _edata

__bss_start = .
__bss_end = .
_sidata = .
_sdata = .
_edata = .
