    .section .text
    .align 2

    .macro SIMPLEOS_ARM_INTERRUPT_CONTROL disable_symbol, enable_symbol, wait_symbol
    .global \disable_symbol
\disable_symbol:
    SIMPLEOS_ARM_DISABLE_INTERRUPTS
    SIMPLEOS_ARM_RETURN

    .global \enable_symbol
\enable_symbol:
    SIMPLEOS_ARM_ENABLE_INTERRUPTS
    SIMPLEOS_ARM_RETURN

    .global \wait_symbol
\wait_symbol:
    SIMPLEOS_ARM_WAIT_FOR_INTERRUPT
    SIMPLEOS_ARM_RETURN
    .endm
