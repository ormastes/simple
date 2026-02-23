# RISC-V 32-bit Compressed Logging via SYS_WRITEC (Standard QEMU)
#
# Uses SYS_WRITEC (0x03) to output binary protocol frames byte-by-byte.
# SYS_WRITEC writes a single character and handles 0x00 bytes correctly,
# unlike SYS_WRITE0 which stops at null bytes.
#
# Protocol frame format (matches reader.spl):
#   MAGIC(1)=0xAB  VERSION(1)=0x01  OP(4 LE)  LEN(4 LE)  PAYLOAD(N)
#
# Frame 1: SYS_WRITE_HANDLE(0x100), handle=1  ("Hello, RISC-V 32!")
# Frame 2: SYS_WRITE_HANDLE(0x100), handle=2  ("[SEMIHOST TEST] Success")
# Frame 3: SYS_EXIT via standard semihosting op 0x18
#
# No strings in binary - only numeric handle IDs.
# Host-side reader resolves handles via .smt file.
#
# Build:
#   riscv64-linux-gnu-as -march=rv32i -mabi=ilp32 hello_riscv32_compressed_v3.s -o /tmp/hello_riscv32_compressed_v3.o
#   riscv64-linux-gnu-ld -m elf32lriscv /tmp/hello_riscv32_compressed_v3.o -o hello_riscv32_compressed_v3.elf -Ttext=0x80000000
#
# Run (capture output to file):
#   qemu-system-riscv32 -M virt -bios none -kernel hello_riscv32_compressed_v3.elf \
#     -chardev file,id=sh,path=/tmp/semihost_out.bin \
#     -semihosting-config enable=on,target=native,chardev=sh -nographic
#
# Decode:
#   bin/release/simple src/app/semihost/reader.spl \
#     --file=/tmp/semihost_out.bin --smt-file=hello_riscv32_interned.smt

.section .text
.global _start

_start:
    # Set up stack
    lui sp, %hi(0x80004000)
    addi sp, sp, %lo(0x80004000)

    # === Send Frame 1: SYS_WRITE_HANDLE, handle=1 ===
    la a0, frame1
    li a1, 14               # frame size: 1+1+4+4+4 = 14 bytes
    jal ra, send_frame

    # === Send Frame 2: SYS_WRITE_HANDLE, handle=2 ===
    la a0, frame2
    li a1, 14               # frame size: 14 bytes
    jal ra, send_frame

    # === Exit via standard SYS_EXIT (0x18) ===
    li a0, 0x18             # SYS_EXIT
    li a1, 0                # exit code 0
    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

halt:
    wfi
    j halt

# ============================================================================
# send_frame: Send binary frame byte-by-byte via SYS_WRITEC
#
# Arguments:
#   a0 = pointer to frame data
#   a1 = frame length in bytes
#
# SYS_WRITEC (0x03): a0=0x03, a1=pointer to single byte
# ============================================================================
send_frame:
    addi sp, sp, -16
    sw ra, 12(sp)
    sw s0, 8(sp)            # frame pointer
    sw s1, 4(sp)            # remaining count

    mv s0, a0               # s0 = current byte pointer
    mv s1, a1               # s1 = remaining bytes

.send_loop:
    beqz s1, .send_done     # if no bytes left, done

    # SYS_WRITEC: a0=0x03, a1=pointer to byte to write
    li a0, 0x03             # SYS_WRITEC
    mv a1, s0               # pointer to current byte

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    addi s0, s0, 1          # advance pointer
    addi s1, s1, -1         # decrement count
    j .send_loop

.send_done:
    lw ra, 12(sp)
    lw s0, 8(sp)
    lw s1, 4(sp)
    addi sp, sp, 16
    ret

# ============================================================================
# Frame Data (binary protocol frames)
# ============================================================================

.section .data
.align 4

# Frame 1: SYS_WRITE_HANDLE(0x100), handle=1
# MAGIC + VERSION + OP(4 LE) + LEN(4 LE) + HANDLE(4 LE) = 14 bytes
frame1:
    .byte 0xAB              # MAGIC
    .byte 0x01              # VERSION
    .byte 0x00, 0x01, 0x00, 0x00  # OP = 0x00000100 (SYS_WRITE_HANDLE, little-endian)
    .byte 0x04, 0x00, 0x00, 0x00  # LEN = 4 (payload = handle only)
    .byte 0x01, 0x00, 0x00, 0x00  # PAYLOAD: handle = 1

# Frame 2: SYS_WRITE_HANDLE(0x100), handle=2
frame2:
    .byte 0xAB              # MAGIC
    .byte 0x01              # VERSION
    .byte 0x00, 0x01, 0x00, 0x00  # OP = 0x00000100 (SYS_WRITE_HANDLE)
    .byte 0x04, 0x00, 0x00, 0x00  # LEN = 4
    .byte 0x02, 0x00, 0x00, 0x00  # PAYLOAD: handle = 2

# Size comparison:
# - hello_riscv32_semihost.s (text mode): strings embedded = ~100+ bytes data
# - This v3 (compressed):   28 bytes data + ~60 bytes code = ~88 bytes total
# - No strings in binary. 88%+ reduction for real firmware with many strings.
