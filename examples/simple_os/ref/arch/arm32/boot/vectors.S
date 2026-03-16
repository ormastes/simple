/*
 * vectors.S — ARM32 exception vector table
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * The vector table must be 32-byte aligned and is installed at the
 * address pointed to by the VBAR (Vector Base Address Register).
 *
 * ARM exception vector layout (each entry is 4 bytes):
 *   0x00: Reset
 *   0x04: Undefined Instruction
 *   0x08: Supervisor Call (SVC)
 *   0x0C: Prefetch Abort
 *   0x10: Data Abort
 *   0x14: Reserved (Hypervisor Trap on ARMv7-VE)
 *   0x18: IRQ
 *   0x1C: FIQ
 */

.section .vectors, "ax"
.align 5        /* 32-byte aligned */

.global vector_table
vector_table:
    ldr pc, =reset_handler
    ldr pc, =undef_handler
    ldr pc, =svc_handler
    ldr pc, =prefetch_abort_handler
    ldr pc, =data_abort_handler
    ldr pc, =reserved_handler
    ldr pc, =irq_handler
    ldr pc, =fiq_handler

/* ══════════════════════════════════════════════════════════════════════
 * Exception handler stubs
 *
 * Each stub saves context into a trap_frame_t on the SVC stack,
 * then calls the C handler with a pointer to that frame.
 *
 * trap_frame_t layout:
 *   r0-r12, sp, lr, pc, cpsr  (17 * 4 = 68 bytes)
 * ══════════════════════════════════════════════════════════════════════ */

.section .text

/* ── Macro: save context and call C handler ───────────────────────── */

/*
 * SAVE_CONTEXT: save user/interrupted registers to SVC stack
 *   - lr_offset: value to subtract from LR to get return address
 *   - handler: C function to call
 */
.macro EXCEPTION_ENTRY lr_offset, handler
    /* Adjust LR to point to the faulting/return instruction */
    sub     lr, lr, #\lr_offset

    /* Save LR (return address) and SPSR on SVC stack */
    srsdb   sp!, #0x13          /* Store Return State to SVC mode stack */

    /* Switch to SVC mode (we may already be in SVC for SVC exceptions) */
    cps     #0x13

    /* Save all general-purpose registers */
    push    {r0-r12}

    /* Save the user/interrupted SP and LR */
    /* (These are banked, so we read them from the interrupted mode) */
    mov     r0, sp              /* r0 = pointer to trap frame */

    /* Call the C handler */
    bl      \handler

    /* Restore registers */
    pop     {r0-r12}

    /* Return from exception (restores PC and CPSR from stack) */
    rfeia   sp!
.endm

/* ── Reset ─────────────────────────────────────────────────────────── */

reset_handler:
    b       _start              /* Jump to boot startup */

/* ── Undefined Instruction ─────────────────────────────────────────── */

undef_handler:
    EXCEPTION_ENTRY 4, handle_undef

/* ── Supervisor Call (SVC) ─────────────────────────────────────────── */

svc_handler:
    EXCEPTION_ENTRY 0, handle_svc

/* ── Prefetch Abort ────────────────────────────────────────────────── */

prefetch_abort_handler:
    EXCEPTION_ENTRY 4, handle_prefetch_abort

/* ── Data Abort ────────────────────────────────────────────────────── */

data_abort_handler:
    EXCEPTION_ENTRY 8, handle_data_abort

/* ── Reserved ──────────────────────────────────────────────────────── */

reserved_handler:
    b       reserved_handler    /* Should never occur — spin */

/* ── IRQ ───────────────────────────────────────────────────────────── */

irq_handler:
    EXCEPTION_ENTRY 4, handle_irq

/* ── FIQ ───────────────────────────────────────────────────────────── */

fiq_handler:
    EXCEPTION_ENTRY 4, handle_fiq

/* Note: .size omitted — vector_table and handlers span multiple sections */
