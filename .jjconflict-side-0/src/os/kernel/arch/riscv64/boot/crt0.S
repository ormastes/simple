/* RISC-V 64 S-mode startup — minimal hardware ABI trampoline.
 *
 * OpenSBI jumps here at 0x80200000 in S-mode with:
 *   a0 = hart ID
 *   a1 = DTB physical address
 *   sp = undefined
 *
 * This stub preserves the boot args, sets up the stack, zeros BSS,
 * then passes hart_id/dtb_addr to boot_main(a0, a1) in Simple.
 */

.section .text.entry
.globl _start
_start:
    /* Save OpenSBI boot arguments before anything clobbers them.
     * s0/s1 are callee-saved, so they survive the BSS-zero loop.
     */
    mv      s0, a0              /* s0 = hart_id  */
    mv      s1, a1              /* s1 = dtb_addr */

    /* Set up stack pointer from linker symbol */
    la      sp, _stack_top

    /* Zero BSS (g_hart_id, g_dtb_addr live here — zeroed intentionally) */
    la      t0, _sbss
    la      t1, _ebss
1:  bgeu    t0, t1, 2f
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       1b
2:

    /* Restore boot args into argument registers for boot_main(hart_id, dtb_addr).
     * The Simple compiler mangles the name with module path prefix.
     */
    mv      a0, s0
    mv      a1, s1
    call    os__kernel__arch__riscv64__boot__boot_main

    /* If boot_main returns, halt */
.Lhalt:
    wfi
    j       .Lhalt
