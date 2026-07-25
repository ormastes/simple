# Test SW instruction - simple pattern matching simple.S
.section .text
.global _start
_start:
    # Test instruction: sw x6, 0(x5) (result discarded, just execution)
    li x5, 0x10000000  # Use UART address as safe store location
    li x6, 0x12345678
    sw x6, 0(x5)

    # Write 'P' to UART MMIO 0x10000000 (matches simple.S exactly)
    li x5, 0x10000000
    li x6, 0x50  # 'P'
    sb x6, 0(x5)
1:  j 1b        # infinite loop (matches simple.S exactly)
