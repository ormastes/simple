/* fw_xc AArch64 crt0. Standalone image entry (EL1/EL2, MMU off); the
   real-firmware boot uses check-baremetal-efi-boot.shs's EFI shim instead.
   UART = PL011 @0x09000000 (QEMU virt); board: change FW_UART. */
#define FW_UART 0x09000000
    .section .text.entry, "ax"
    .globl _start
_start:
    mrs     x0, mpidr_el1
    and     x0, x0, #0xff
    cbnz    x0, .Lhalt
    mov     x0, #(3 << 20)          /* CPACR_EL1.FPEN: no trap on FP/SIMD */
    msr     cpacr_el1, x0
    isb
    ldr     x0, =_stack_top
    mov     sp, x0
    ldr     x0, =_sbss
    ldr     x1, =_ebss
1:  cmp     x0, x1
    b.hs    2f
    str     xzr, [x0], #8
    b       1b
2:  bl      __simple_main
.Lhalt:
    wfe
    b       .Lhalt

    .text
    .globl rt_mmio_write8
rt_mmio_write8:
    ldr     x2, =FW_UART
    strb    w1, [x2]
    ret
