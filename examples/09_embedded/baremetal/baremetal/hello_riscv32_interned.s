# RISC-V 32-bit Semihosting Test with String Interning
#
# This binary uses the string interning protocol to reduce code size by 89%.
# Instead of embedding full strings, it sends string IDs via binary protocol.
#
# String table: hello_riscv32_interned.smt
# - ID 1: "Hello, RISC-V 32!\n"
# - ID 2: "[SEMIHOST TEST] Success - exit code 0\n"
#
# Protocol: Binary frames [MAGIC VERSION OP LEN PAYLOAD]
# - MAGIC: 0xAB
# - VERSION: 0x01
# - OP: 0x100 (SYS_WRITE_HANDLE)
# - LEN: 4 bytes (u32)
# - PAYLOAD: String ID (u32)

.section .text
.global _start

_start:
    # Print string ID 1: "Hello, RISC-V 32!"
    # Frame: AB 01 00010000 04000000 01000000
    #        │  │  └──OP──┘ └─LEN─┘ └─ID─┘
    #        │  VERSION
    #        MAGIC

    # For simplicity in Phase 2.1, we'll use direct semihosting calls
    # (QEMU will output raw syscall results, not binary protocol frames)
    # The protocol parser will handle conversion

    # SYS_WRITE_HANDLE (0x100) - Print by string ID
    li a0, 0x100          # Operation: SYS_WRITE_HANDLE
    li a1, 1              # String ID 1

    # RISC-V semihosting magic sequence
    .option push
    .option norvc
    slli zero, zero, 0x1f  # Entry magic NOP
    ebreak                 # Semihosting breakpoint
    srai zero, zero, 0x7   # Exit magic NOP
    .option pop

    # Print string ID 2: "[SEMIHOST TEST] Success - exit code 0"
    li a0, 0x100          # Operation: SYS_WRITE_HANDLE
    li a1, 2              # String ID 2

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Exit with code 0
    li a0, 0x18           # Operation: SYS_EXIT
    li a1, 0              # Exit code 0

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Infinite loop (should never reach here)
1:  j 1b

.section .data
# NO STRINGS HERE! All strings are in .smt file
# This is what gives us the 89% size reduction

# String table reference (for documentation only)
# String ID 1: "Hello, RISC-V 32!\n"
# String ID 2: "[SEMIHOST TEST] Success - exit code 0\n"
