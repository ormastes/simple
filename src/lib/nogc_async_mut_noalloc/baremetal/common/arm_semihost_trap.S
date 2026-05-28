    .section .text
    .align 2

    .macro SIMPLEOS_ARM_SEMIHOST_TRAP call_symbol, write0_symbol, exit_symbol
    .global \call_symbol
\call_symbol:
    SIMPLEOS_ARM_SEMIHOST_CALL
    SIMPLEOS_ARM_SEMIHOST_RETURN

    .global \write0_symbol
\write0_symbol:
    SIMPLEOS_ARM_SEMIHOST_ARG_WRITE0
    b \call_symbol

    .global \exit_symbol
\exit_symbol:
    SIMPLEOS_ARM_SEMIHOST_ARG_EXIT
    b \call_symbol
    .endm
