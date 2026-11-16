/* fw_xc RISC-V crt0 (rv32 + rv64). M-mode reset entry at RAM base, as the
   image is the firmware itself (QEMU virt: -bios <elf>). UART = ns16550 @0x10000000. */
#if __riscv_xlen == 64
#define STORE sd
#define WORD 8
#else
#define STORE sw
#define WORD 4
#endif
    .section .text.entry, "ax"
    .globl _start
_start:
    csrr    t0, mhartid
    bnez    t0, .Lhalt
    la      sp, _stack_top
    la      t0, _sbss
    la      t1, _ebss
1:  bgeu    t0, t1, 2f
    STORE   zero, 0(t0)
    addi    t0, t0, WORD
    j       1b
2:  call    __simple_main
.Lhalt:
    wfi
    j       .Lhalt

    .text
    .globl rt_mmio_write8
rt_mmio_write8:
    li      t0, 0x10000000
1:  lbu     t1, 5(t0)
    andi    t1, t1, 0x20
    beqz    t1, 1b
#if __riscv_xlen == 64
    sb      a1, 0(t0)
#else
    sb      a2, 0(t0)        /* ilp32: i64 addr in a0:a1, value lo in a2 */
#endif
    ret
