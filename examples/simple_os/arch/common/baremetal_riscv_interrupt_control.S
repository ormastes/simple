    .section .text
    .align 2
    .global RV_INT_DISABLE
    .type RV_INT_DISABLE, @function
RV_INT_DISABLE:
    csrci mstatus, 0x8
    ret
    .size RV_INT_DISABLE, . - RV_INT_DISABLE
    .global RV_INT_ENABLE
    .type RV_INT_ENABLE, @function
RV_INT_ENABLE:
    csrsi mstatus, 0x8
    ret
    .size RV_INT_ENABLE, . - RV_INT_ENABLE
    .global RV_WAIT
    .type RV_WAIT, @function
RV_WAIT:
    wfi
    ret
    .size RV_WAIT, . - RV_WAIT
