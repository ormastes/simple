/* CRZ Cosmos+ OpenSSD (Xilinx Zynq-7000, dual Cortex-A9 / ARMv7-A) bare-metal entry.
 *
 * Direct M-... (ARM has no M-mode; this is the FSBL-less bring-up entry used under
 * `qemu-system-arm -M xilinx-zynq-a9 -kernel`). On real Cosmos+ hardware the Zynq BootROM
 * + FSBL would run first; this entry is the minimal "kernel loaded into DDR, jump here"
 * bring-up that validates the Cadence UART / memory map binding.
 */
    .section .text.start,"ax",%progbits
    .balign 32
    .global _start
    .arm
    .equ    COSMOS_BSS_READY_MAGIC, 0x42535321
_start:
    b       cosmos_reset_entry
    b       cosmos_exception_park          /* undefined instruction */
    b       cosmos_exception_park          /* supervisor call */
    b       cosmos_prefetch_abort
    b       cosmos_data_abort
    b       cosmos_exception_park          /* reserved */
    b       cosmos_irq_entry
    b       cosmos_exception_park          /* FIQ */
    .global cosmos_vectors_end
cosmos_vectors_end:

cosmos_reset_entry:
    cpsid   if
    mrc     p15, 0, r0, c1, c0, 0
    bic     r0, r0, #0x2000                 /* SCTLR.V: use VBAR */
    dsb     sy
    mcr     p15, 0, r0, c1, c0, 0
    isb     sy
    ldr     r0, =_start
    mcr     p15, 0, r0, c12, c0, 0         /* VBAR */
    dsb     sy
    isb     sy
    /* CPU1 (and any secondary) parks; CPU0 boots. MPIDR low bits = CPU id. */
    mrc     p15, 0, r1, c0, c0, 5      /* read MPIDR */
    and     r1, r1, #3
    cmp     r1, #0
    bne     cosmos_secondary_start
    bl      cosmos_init_irq_stack
    ldr     sp, =_stack_top

    /* The initialized sync word is outside BSS, so CPU1 cannot observe
     * partially-cleared C globals. Only CPU0 executes this clear loop. */
    ldr     r0, =cosmos_bss_ready
    mov     r2, #0
    str     r2, [r0]
    dsb     sy
    ldr     r0, =_sbss
    ldr     r1, =_ebss
.Lbss_clear:
    cmp     r0, r1
    strlo   r2, [r0], #4
    blo     .Lbss_clear
    dsb     sy
    ldr     r0, =cosmos_bss_ready
    ldr     r1, =COSMOS_BSS_READY_MAGIC
    str     r1, [r0]
    dsb     sy
    sev

    bl      cosmos_boot_main
.Lhalt:
    wfi
    b       .Lhalt

    .global cosmos_secondary_start
cosmos_secondary_start:
    cpsid   if
    mrc     p15, 0, r0, c1, c0, 0
    bic     r0, r0, #0x2000                 /* SCTLR.V: use VBAR */
    dsb     sy
    mcr     p15, 0, r0, c1, c0, 0
    isb     sy
    ldr     r0, =_start
    mcr     p15, 0, r0, c12, c0, 0         /* private VBAR */
    dsb     sy
    isb     sy
    bl      cosmos_init_irq_stack

    /* Do not touch BSS-backed release mailboxes until CPU0 publishes ready. */
    ldr     r2, =cosmos_bss_ready
.Lbss_wait:
    ldr     r3, [r2]
    ldr     r4, =COSMOS_BSS_READY_MAGIC
    cmp     r3, r4
    beq     .Lbss_ready
    wfe
    b       .Lbss_wait
.Lbss_ready:
    ldr     sp, =cosmos_secondary_boot_stack_top
.Lsecondary_wait:
    ldr     r2, =cosmos_secondary_release_state
    ldr     r3, [r2]
    cmp     r3, #2                  /* COSMOS_SMP_RELEASED */
    beq     .Lsecondary_release
    cmp     r3, #4                  /* COSMOS_SMP_CANCELLED */
    beq     .Lpark
    mov     r3, #1                  /* COSMOS_SMP_READY */
    str     r3, [r2]
    dsb     sy
    wfe
    b       .Lsecondary_wait
.Lsecondary_release:
    ldr     r2, =cosmos_secondary_release_entry
    ldr     r4, [r2]
    ldr     r2, =cosmos_secondary_release_stack
    ldr     r5, [r2]
    cmp     r4, #0
    beq     .Lpark
    cmp     r5, #0
    beq     .Lpark
    dsb     sy
    mov     sp, r5
    bl      cosmos_smp_secondary_prepare
    cmp     r0, #0                  /* COSMOS_OK */
    bne     .Lpark
    ldr     r2, =cosmos_secondary_release_entry
    ldr     r4, [r2]
    blx     r4
.Lpark:
    wfi
    b       .Lpark

/* Install an aligned banked IRQ stack without consuming C state. */
cosmos_init_irq_stack:
    mrs     r2, cpsr
    bic     r3, r2, #0x1f
    orr     r3, r3, #0x12                  /* IRQ mode */
    orr     r3, r3, #0xc0                  /* keep IRQ/FIQ masked */
    msr     cpsr_c, r3
    mrc     p15, 0, r0, c0, c0, 5
    and     r0, r0, #3
    cmp     r0, #0
    ldreq   sp, =_irq_stack_cpu0_top
    ldrne   sp, =_irq_stack_cpu1_top
    msr     cpsr_c, r2
    isb     sy
    bx      lr

    .global cosmos_irq_entry
    .type   cosmos_irq_entry, %function
    .extern cosmos_gic_irq_dispatch
cosmos_irq_entry:
    /* Six saved registers plus the SPSR/pad pair preserve 8-byte alignment. */
    stmdb   sp!, {r0-r3, r12, lr}
    mrs     r0, spsr
    sub     sp, sp, #8
    str     r0, [sp]
    bl      cosmos_gic_irq_dispatch
    ldr     r0, [sp]
    msr     spsr_cxsf, r0
    add     sp, sp, #8
    ldmia   sp!, {r0-r3, r12, lr}
    subs    pc, lr, #4
    .size   cosmos_irq_entry, . - cosmos_irq_entry

cosmos_prefetch_abort:
    mrc     p15, 0, r1, c5, c0, 1          /* IFSR */
    mrc     p15, 0, r2, c6, c0, 2          /* IFAR */
    sub     r3, lr, #4
    mov     r0, #1
    b       cosmos_abort_enter

cosmos_data_abort:
    mrc     p15, 0, r1, c5, c0, 0          /* DFSR */
    mrc     p15, 0, r2, c6, c0, 0          /* DFAR */
    sub     r3, lr, #8
    mov     r0, #2

cosmos_abort_enter:
    cpsid   if
    ldr     sp, =cosmos_abort_stack_top
    b       cosmos_exception_halt

cosmos_exception_park:
    cpsid   if
    wfi
    b       cosmos_exception_park

    .section .data.boot_sync,"aw",%progbits
    .balign 4
    .global cosmos_bss_ready
    .type   cosmos_bss_ready, %object
cosmos_bss_ready:
    .word   0
    .size   cosmos_bss_ready, . - cosmos_bss_ready

    .section .bss,"aw",%nobits
    .balign 8
cosmos_abort_stack:
    .space  1024
cosmos_abort_stack_top:
    .balign 16
cosmos_secondary_boot_stack:
    .space  1024
cosmos_secondary_boot_stack_top:
    .align  2
    .global cosmos_secondary_release_entry
cosmos_secondary_release_entry:
    .space  4
    .global cosmos_secondary_release_stack
cosmos_secondary_release_stack:
    .space  4
    .global cosmos_secondary_release_generation
cosmos_secondary_release_generation:
    .space  4
    .global cosmos_secondary_release_ack
cosmos_secondary_release_ack:
    .space  4
    .global cosmos_secondary_release_state
cosmos_secondary_release_state:
    .space  4
