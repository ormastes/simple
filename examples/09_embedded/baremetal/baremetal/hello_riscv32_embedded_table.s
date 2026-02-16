# RISC-V 32-bit Semihosting with Embedded String Table
#
# String table is embedded in the binary's .smt section.
# QEMU reads table from target memory (no external files needed).
#
# Binary format:
#   .text    - Program code
#   .smt     - String metadata table
#   .data    - Data section
#
# String table format (.smt section):
#   [count: u32]
#   [entries...]
#
# Entry format:
#   [id: u32, length: u32, param_count: u32, text: char[]]
#

.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    # Table header
    .word 2                        # Entry count

    # Entry 1: ID=1, "Hello, RISC-V 32!\n"
    .word 1                        # ID
    .word 19                       # Length (including null terminator)
    .word 0                        # Parameter count
    .ascii "Hello, RISC-V 32!\n"
    .byte 0
    .align 4                       # Align to 4-byte boundary

    # Entry 2: ID=2, "[SEMIHOST TEST] Success - exit code 0\n"
    .word 2                        # ID
    .word 40                       # Length
    .word 0                        # Parameter count
    .ascii "[SEMIHOST TEST] Success - exit code 0\n"
    .byte 0
    .align 4

.section .text
.global _start

_start:
    # Print string ID 1: "Hello, RISC-V 32!"
    li a0, 0x100              # SYS_WRITE_HANDLE (custom operation)
    li a1, 1                  # String ID 1

    .option push
    .option norvc
    slli zero, zero, 0x1f    # Entry magic NOP
    ebreak                    # Semihosting breakpoint
    srai zero, zero, 0x7     # Exit magic NOP
    .option pop

    # Print string ID 2: "[SEMIHOST TEST] Success"
    li a0, 0x100
    li a1, 2                  # String ID 2

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Exit with code 0
    li a0, 0x18               # SYS_EXIT (standard operation)
    li a1, 0                  # Exit code 0

    .option push
    .option norvc
    slli zero, zero, 0x1f
    ebreak
    srai zero, zero, 0x7
    .option pop

    # Infinite loop (should never reach here)
1:  j 1b

# Symbol for table location (for debugging)
.section .rodata
.global __simple_string_table_addr
__simple_string_table_addr:
    .word __simple_string_table

# Size information
# Text section:  ~52 bytes (code only, no embedded strings!)
# .smt section:  ~80 bytes (string table)
# Total:         ~132 bytes
#
# Compare to text mode: ~66KB with embedded strings
# Reduction: 99.8% for code, table overhead is fixed cost
