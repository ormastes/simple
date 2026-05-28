    .section .text
    .align 2

    .macro SIMPLEOS_RISCV_SEMIHOST_TRAP call_symbol, write0_symbol, exit_symbol
    .global \call_symbol
\call_symbol:
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop
    ret

    .global \write0_symbol
\write0_symbol:
    mv a1, a0
    li a0, 0x04
    tail \call_symbol

    .global \exit_symbol
\exit_symbol:
    mv a1, a0
    li a0, 0x18
    tail \call_symbol
    .endm
