/*
 * trap_vector.S -- RV64 S-mode trap entry/exit and user-mode entry
 *
 * Implements:
 *   _rv64_trap_vector  — single supervisor trap entrypoint (stvec target)
 *   _rv64_enter_user   — first entry into U-mode from scheduler
 *
 * Trap-frame layout matches Riscv64Context (34 slots x 8 bytes = 272 bytes)
 * defined in os.kernel.arch.riscv64.trap_frame. The dispatcher function
 * rv64_dispatch_trap_frame_ptr(ctx_addr: u64) -> i64 is called with the
 * frame pointer in a0.
 *
 * sscratch protocol:
 *   - From U-mode: sscratch holds the kernel stack pointer
 *   - From S-mode: sscratch is 0 (detect reentrant traps)
 */

/* Trap-frame field offsets (slot_index * 8) */
.equ TF_RA,       0    /* x1  */
.equ TF_SP,       8    /* x2  */
.equ TF_GP,      16    /* x3  */
.equ TF_TP,      24    /* x4  */
.equ TF_T0,      32    /* x5  */
.equ TF_T1,      40    /* x6  */
.equ TF_T2,      48    /* x7  */
.equ TF_S0,      56    /* x8  */
.equ TF_S1,      64    /* x9  */
.equ TF_A0,      72    /* x10 */
.equ TF_A1,      80    /* x11 */
.equ TF_A2,      88    /* x12 */
.equ TF_A3,      96    /* x13 */
.equ TF_A4,     104    /* x14 */
.equ TF_A5,     112    /* x15 */
.equ TF_A6,     120    /* x16 */
.equ TF_A7,     128    /* x17 */
.equ TF_S2,     136    /* x18 */
.equ TF_S3,     144    /* x19 */
.equ TF_S4,     152    /* x20 */
.equ TF_S5,     160    /* x21 */
.equ TF_S6,     168    /* x22 */
.equ TF_S7,     176    /* x23 */
.equ TF_S8,     184    /* x24 */
.equ TF_S9,     192    /* x25 */
.equ TF_S10,    200    /* x26 */
.equ TF_S11,    208    /* x27 */
.equ TF_T3,     216    /* x28 */
.equ TF_T4,     224    /* x29 */
.equ TF_T5,     232    /* x30 */
.equ TF_T6,     240    /* x31 */
.equ TF_SEPC,   248    /* sepc */
.equ TF_SSTATUS,256    /* sstatus */
.equ TF_SCAUSE, 264    /* scause */
.equ TF_SIZE,   272    /* 34 * 8 */

    .section .text.trap, "ax", @progbits
    .balign 4

/* =========================================================================
 * _rv64_trap_vector — S-mode trap entry (direct mode stvec target)
 *
 * On entry:
 *   - If from U-mode: sscratch = kernel sp, sp = user sp
 *   - If from S-mode: sscratch = 0,         sp = kernel sp
 * ========================================================================= */
    .globl _rv64_trap_vector
    .type _rv64_trap_vector, @function
_rv64_trap_vector:
    /* Swap sp <-> sscratch. After this:
     *   sp = kernel sp (or user sp if from S-mode)
     *   sscratch = user sp (or 0 if from S-mode)
     */
    csrrw   sp, sscratch, sp

    /* Check if we came from S-mode (sscratch was 0 before swap).
     * If sscratch is now 0, we're reentrant from S-mode — use sp as-is
     * but we need to recover the original sp from sscratch (which is now
     * what we just wrote, i.e., the S-mode sp).
     * Actually: if from S-mode, sscratch was 0, so after csrrw:
     *   sp = 0 (wrong!), sscratch = old S-mode sp
     * We need to detect this and fix up.
     */
    bnez    sp, .Lfrom_user

    /* From S-mode: sp is 0 after swap. Recover from sscratch. */
    csrr    sp, sscratch

.Lfrom_user:
    /* Allocate trap frame on kernel stack */
    addi    sp, sp, -TF_SIZE

    /* Save GPRs — t0 first (we need a temp for user sp) */
    sd      t0, TF_T0(sp)

    /* Save user sp: it's in sscratch (if from U-mode) or we need
     * to compute it (if from S-mode, original sp = sp + TF_SIZE) */
    csrr    t0, sscratch
    beqz    t0, .Lsave_smode_sp
    /* From U-mode: user sp is in t0 (from sscratch) */
    sd      t0, TF_SP(sp)
    /* Set sscratch = 0 to mark "now in S-mode" for reentrant traps */
    csrw    sscratch, zero
    j       .Lsp_saved
.Lsave_smode_sp:
    /* From S-mode: original sp was sp + TF_SIZE */
    addi    t0, sp, TF_SIZE
    sd      t0, TF_SP(sp)
.Lsp_saved:

    /* Save remaining GPRs */
    sd      ra, TF_RA(sp)
    sd      gp, TF_GP(sp)
    sd      tp, TF_TP(sp)
    /* t0 already saved above */
    sd      t1, TF_T1(sp)
    sd      t2, TF_T2(sp)
    sd      s0, TF_S0(sp)
    sd      s1, TF_S1(sp)
    sd      a0, TF_A0(sp)
    sd      a1, TF_A1(sp)
    sd      a2, TF_A2(sp)
    sd      a3, TF_A3(sp)
    sd      a4, TF_A4(sp)
    sd      a5, TF_A5(sp)
    sd      a6, TF_A6(sp)
    sd      a7, TF_A7(sp)
    sd      s2, TF_S2(sp)
    sd      s3, TF_S3(sp)
    sd      s4, TF_S4(sp)
    sd      s5, TF_S5(sp)
    sd      s6, TF_S6(sp)
    sd      s7, TF_S7(sp)
    sd      s8, TF_S8(sp)
    sd      s9, TF_S9(sp)
    sd      s10, TF_S10(sp)
    sd      s11, TF_S11(sp)
    sd      t3, TF_T3(sp)
    sd      t4, TF_T4(sp)
    sd      t5, TF_T5(sp)
    sd      t6, TF_T6(sp)

    /* Save supervisor CSRs */
    csrr    t0, sepc
    sd      t0, TF_SEPC(sp)
    csrr    t0, sstatus
    sd      t0, TF_SSTATUS(sp)
    csrr    t0, scause
    sd      t0, TF_SCAUSE(sp)

    /* Call rv64_dispatch_trap_frame_ptr(ctx_addr=sp) -> i64
     * The dispatcher reads/updates the frame in place and returns 0 on success.
     */
    mv      a0, sp
    call    rv64_dispatch_trap_frame_ptr

    /* Check return: a0 != 0 means fatal trap */
    bnez    a0, .Ltrap_fatal

    /* === Restore path (shared with _rv64_enter_user) === */
.Ltrap_restore:
    /* Restore supervisor CSRs from (possibly updated) frame */
    ld      t0, TF_SEPC(sp)
    csrw    sepc, t0
    ld      t0, TF_SSTATUS(sp)
    csrw    sstatus, t0
    /* scause is read-only to software — skip restore */

    /* Restore all GPRs except sp and t0 (restored last) */
    ld      ra, TF_RA(sp)
    ld      gp, TF_GP(sp)
    ld      tp, TF_TP(sp)
    /* t0 restored after sp swap */
    ld      t1, TF_T1(sp)
    ld      t2, TF_T2(sp)
    ld      s0, TF_S0(sp)
    ld      s1, TF_S1(sp)
    ld      a0, TF_A0(sp)
    ld      a1, TF_A1(sp)
    ld      a2, TF_A2(sp)
    ld      a3, TF_A3(sp)
    ld      a4, TF_A4(sp)
    ld      a5, TF_A5(sp)
    ld      a6, TF_A6(sp)
    ld      a7, TF_A7(sp)
    ld      s2, TF_S2(sp)
    ld      s3, TF_S3(sp)
    ld      s4, TF_S4(sp)
    ld      s5, TF_S5(sp)
    ld      s6, TF_S6(sp)
    ld      s7, TF_S7(sp)
    ld      s8, TF_S8(sp)
    ld      s9, TF_S9(sp)
    ld      s10, TF_S10(sp)
    ld      s11, TF_S11(sp)
    ld      t3, TF_T3(sp)
    ld      t4, TF_T4(sp)
    ld      t5, TF_T5(sp)
    ld      t6, TF_T6(sp)

    /* Check sstatus.SPP to decide sscratch handling:
     *   SPP=0 (U-mode return): set sscratch = kernel sp, restore user sp
     *   SPP=1 (S-mode return): set sscratch = 0, restore S-mode sp
     */
    csrr    t0, sstatus
    andi    t0, t0, 0x100       /* SPP bit (bit 8) */
    bnez    t0, .Lreturn_smode

    /* Returning to U-mode: sscratch = kernel sp for next trap */
    addi    t0, sp, TF_SIZE     /* kernel sp = frame base + frame size */
    csrw    sscratch, t0
    ld      t0, TF_T0(sp)      /* restore t0 */
    ld      sp, TF_SP(sp)      /* restore user sp */
    sret

.Lreturn_smode:
    /* Returning to S-mode: sscratch = 0 (signals "in S-mode") */
    csrw    sscratch, zero
    ld      t0, TF_T0(sp)      /* restore t0 */
    ld      sp, TF_SP(sp)      /* restore original S-mode sp */
    sret

.Ltrap_fatal:
    /* Fatal trap: spin forever (debugger can inspect frame at sp) */
    wfi
    j       .Ltrap_fatal

    .size _rv64_trap_vector, . - _rv64_trap_vector


/* =========================================================================
 * _rv64_enter_user — First entry into U-mode from scheduler
 *
 * Called as: _rv64_enter_user(ctx_addr: u64)
 *   a0 = pointer to Riscv64Context struct (same layout as trap frame)
 *
 * Loads all registers from the context, sets sscratch to kernel sp,
 * and executes sret to enter U-mode at sepc with SPP=0.
 * ========================================================================= */
    .globl _rv64_enter_user
    .type _rv64_enter_user, @function
_rv64_enter_user:
    /* a0 points to the Riscv64Context. Use it as our frame base.
     * First, set up CSRs from the context. */
    ld      t0, TF_SEPC(a0)
    csrw    sepc, t0
    ld      t0, TF_SSTATUS(a0)
    csrw    sstatus, t0

    /* Set sscratch = current kernel sp (so trap vector can find it) */
    csrw    sscratch, sp

    /* Load all GPRs from context. Use a0 as base, restore a0 last. */
    ld      ra, TF_RA(a0)
    ld      gp, TF_GP(a0)
    ld      tp, TF_TP(a0)
    ld      t0, TF_T0(a0)
    ld      t1, TF_T1(a0)
    ld      t2, TF_T2(a0)
    ld      s0, TF_S0(a0)
    ld      s1, TF_S1(a0)
    ld      a1, TF_A1(a0)
    ld      a2, TF_A2(a0)
    ld      a3, TF_A3(a0)
    ld      a4, TF_A4(a0)
    ld      a5, TF_A5(a0)
    ld      a6, TF_A6(a0)
    ld      a7, TF_A7(a0)
    ld      s2, TF_S2(a0)
    ld      s3, TF_S3(a0)
    ld      s4, TF_S4(a0)
    ld      s5, TF_S5(a0)
    ld      s6, TF_S6(a0)
    ld      s7, TF_S7(a0)
    ld      s8, TF_S8(a0)
    ld      s9, TF_S9(a0)
    ld      s10, TF_S10(a0)
    ld      s11, TF_S11(a0)
    ld      t3, TF_T3(a0)
    ld      t4, TF_T4(a0)
    ld      t5, TF_T5(a0)
    ld      t6, TF_T6(a0)

    /* Load user sp, then restore a0 last */
    ld      sp, TF_SP(a0)
    ld      a0, TF_A0(a0)

    /* Enter U-mode: sstatus.SPP=0 means sret goes to U-mode */
    sret

    .size _rv64_enter_user, . - _rv64_enter_user
