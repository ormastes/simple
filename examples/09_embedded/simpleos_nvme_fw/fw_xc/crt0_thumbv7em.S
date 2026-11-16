/* fw_xc Cortex-M4F crt0: vector table (initial SP + reset) at 0x0, enables
   the FPU (CPACR CP10/CP11) for the eabihf ABI. UART = CMSDK UART0 @0x40004000
   (QEMU mps2-an386); board: change FW_UART. */
#define FW_UART 0x40004000
    .syntax unified
    .thumb
    .section .vectors, "a"
    .word   _stack_top
    .word   _start
    .section .text.entry, "ax"
    .globl _start
    .thumb_func
_start:
    ldr     r0, =0xE000ED88
    ldr     r1, [r0]
    orr     r1, r1, #(0xF << 20)
    str     r1, [r0]
    dsb
    isb
    ldr     r0, =_sbss
    ldr     r1, =_ebss
    movs    r2, #0
1:  cmp     r0, r1
    bhs     2f
    str     r2, [r0], #4
    b       1b
2:  ldr     r0, =FW_UART
    movs    r1, #1
    str     r1, [r0, #8]
    bl      __simple_main
.Lhalt:
    wfi
    b       .Lhalt

    .text
    .globl rt_mmio_write8
    .thumb_func
rt_mmio_write8:
    /* i64 args on AAPCS: addr in r0:r1, value in r2:r3 */
    ldr     r0, =FW_UART
1:  ldr     r1, [r0, #4]
    tst     r1, #1
    bne     1b
    str     r2, [r0]
    bx      lr
