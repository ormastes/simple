# Simple test - just write 'P' to UART and halt
.section .text
.global _start
_start:
    # Write 'P' to UART MMIO 0x10000000
    li x5, 0x10000000
    li x6, 0x50  # 'P'
    sb x6, 0(x5)
1:  j 1b        # infinite loop
