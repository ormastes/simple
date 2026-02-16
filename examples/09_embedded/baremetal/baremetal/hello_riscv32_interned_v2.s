# RISC-V 32-bit Semihosting with Binary Protocol (QEMU Compatible)
#
# Uses standard SYS_WRITE0 to output binary protocol frames.
# Parser reconstructs text from frames + .smt file.
#
# Protocol: [MAGIC VERSION OP LEN PAYLOAD]
# - MAGIC: 0xAB
# - VERSION: 0x01
# - OP: 0x0100 (SYS_WRITE_HANDLE, 2 bytes little-endian)
# - LEN: 0x00000004 (4 bytes, little-endian)
# - PAYLOAD: String ID (4 bytes, little-endian)

.section .text
.global _start

_start:
    # Frame 1: Print string ID 1 ("Hello, RISC-V 32!")
    # Output: AB 01 00 01 04 00 00 00 01 00 00 00
    li a0, 0x04           # SYS_WRITE0
    la a1, frame1         # Point to binary frame

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Frame 2: Print string ID 2 ("[SEMIHOST TEST] Success")
    li a0, 0x04
    la a1, frame2

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Frame 3: Exit
    # Output: AB 01 18 00 04 00 00 00 00 00 00 00
    li a0, 0x04
    la a1, frame_exit

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Infinite loop
1:  j 1b

.section .data
.align 4

# Frame 1: SYS_WRITE_HANDLE with ID=1
frame1:
    .byte 0xAB           # MAGIC
    .byte 0x01           # VERSION
    .byte 0x00, 0x01     # OP = 0x0100 (SYS_WRITE_HANDLE, little-endian)
    .byte 0x04, 0x00, 0x00, 0x00  # LEN = 4
    .byte 0x01, 0x00, 0x00, 0x00  # PAYLOAD = String ID 1
    .byte 0x00           # Null terminator (for SYS_WRITE0)

# Frame 2: SYS_WRITE_HANDLE with ID=2
frame2:
    .byte 0xAB
    .byte 0x01
    .byte 0x00, 0x01
    .byte 0x04, 0x00, 0x00, 0x00
    .byte 0x02, 0x00, 0x00, 0x00
    .byte 0x00

# Frame 3: SYS_EXIT with code=0
frame_exit:
    .byte 0xAB
    .byte 0x01
    .byte 0x18, 0x00     # OP = 0x0018 (SYS_EXIT)
    .byte 0x04, 0x00, 0x00, 0x00
    .byte 0x00, 0x00, 0x00, 0x00  # Exit code 0
    .byte 0x00

# Size comparison:
# - Text mode: ~43 bytes of strings + code = ~100 bytes total
# - This version: ~39 bytes of frames + code = ~80 bytes total
# - Real interned (with proper QEMU): ~12 bytes code only = 88% reduction
