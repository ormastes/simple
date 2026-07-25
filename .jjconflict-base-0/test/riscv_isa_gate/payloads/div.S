# Test DIV instruction - simple pattern matching simple.S
.section .text
.global _start
_start:
    # Test instruction: div x7, x5, x6 (result discarded, just execution)
    li x5, 100
    li x6, 10
    div x7, x5, x6

    # Write 'P' to UART MMIO 0x10000000 (matches simple.S exactly)
    li x5, 0x10000000
    li x6, 0x50  # 'P'
    sb x6, 0(x5)
1:  j 1b        # infinite loop (matches simple.S exactly)
