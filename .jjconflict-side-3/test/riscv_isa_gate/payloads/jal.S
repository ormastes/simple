# Test JAL instruction - simple pattern matching simple.S
.section .text
.global _start
_start:
    # Test instruction: jal x1, target (result discarded, just execution)
    jal x1, target
target:
    # (execution continues here)

    # Write 'P' to UART MMIO 0x10000000 (matches simple.S exactly)
    li x5, 0x10000000
    li x6, 0x50  # 'P'
    sb x6, 0(x5)
1:  j 1b        # infinite loop (matches simple.S exactly)
