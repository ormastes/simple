/* M-mode setup; S-mode load through Sv32 must trap before physical 0x8000. */
    .option norvc
    .section .text
    .globl _start

_start:
    la      t0, trap
    csrw    mtvec, t0

    li      t0, 0x800             /* PMP0: [0x0000, 0x2000), RX */
    csrw    pmpaddr0, t0
    li      t0, 0x2000            /* PMP1: [0x2000, 0x8000), R (page tables) */
    csrw    pmpaddr1, t0
    li      t0, 0x2400            /* PMP2: [0x8000, 0x9000), deny */
    csrw    pmpaddr2, t0
    li      t0, 0x2800            /* PMP3: [0x9000, 0xa000), RWX (completion) */
    csrw    pmpaddr3, t0
    li      t0, 0x8f88898d
    csrw    pmpcfg0, t0           /* lock all ranges: M-mode must obey too */

    li      t0, 0x80000004        /* Sv32 root page table at physical 0x4000 */
    csrw    satp, t0
    csrr    t0, mstatus
    li      t1, -6145             /* clear MPP */
    and     t0, t0, t1
    li      t1, 0x800
    or      t0, t0, t1            /* MPP = S */
    csrw    mstatus, t0
    la      t0, s_entry
    li      t1, 0x80000000
    or      t0, t0, t1            /* S-mode virtual code aliases physical 0 */
    csrw    mepc, t0
    mret

s_entry:
    lui     t0, 0x40000           /* virtual 0x40000000 -> physical 0x8000 */
    lw      t1, 0(t0)             /* PMP must suppress this final WB request */
    ebreak                         /* reaching here is a failure */

trap:
    csrr    t1, mcause
    lui     t0, 0x9
    sw      t1, 0(t0)             /* testbench observes load-access-fault cause 5 */
1:  j       1b
