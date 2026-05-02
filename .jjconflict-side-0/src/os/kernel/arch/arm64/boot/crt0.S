/* ARM64 (AArch64) startup for QEMU virt — src/os kernel boot.
 *
 * QEMU -kernel drops us at EL1 (or EL2) with:
 *   x0 = DTB physical address
 *   x1-x3 = 0 (reserved)
 *   SP = undefined, MMU off, caches off, DAIF masked
 *
 * This stub:
 *   1. Masks all exceptions (DAIF)
 *   2. Sets up the stack from linker symbol _stack_top
 *   3. Zeroes BSS
 *   4. Saves DTB address in x0, calls boot_main(dtb_addr)
 *
 * The Simple compiler mangles the function name with the module path,
 * so we call os__kernel__arch__arm64__boot__boot_main.
 */

    .section .text.entry, "ax", %progbits
    .globl _start
    .type _start, @function

_start:
    /* Mask all exceptions (IRQ, FIQ, SError, Debug) */
    msr     daifset, #0xF

    /* Save DTB address (x0) into a callee-saved register */
    mov     x19, x0

    /* Set up stack pointer from linker symbol */
    adrp    x0, _stack_top
    add     sp, x0, :lo12:_stack_top

    /* Zero BSS section */
    adrp    x0, _sbss
    add     x0, x0, :lo12:_sbss
    adrp    x1, _ebss
    add     x1, x1, :lo12:_ebss
.Lbss_loop:
    cmp     x0, x1
    b.ge    .Lbss_done
    str     xzr, [x0], #8
    b       .Lbss_loop
.Lbss_done:

    /* Call boot_main(dtb_addr) in Simple.
     * The compiler mangles the name with the module path prefix.
     */
    mov     x0, x19
    bl      os__kernel__arch__arm64__boot__boot_main

    /* If boot_main returns, halt forever */
.Lhalt:
    wfe
    b       .Lhalt

    .size _start, . - _start
