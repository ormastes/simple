.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    .word 2                          # Entry count

    # Entry 1: "Hello, RISC-V!\n" (16 bytes, 0 params)
    .word 1                          # ID
    .word 16                         # Length
    .word 0                          # Params
    .ascii "Hello, RISC-V!\n\0"
    .align 4

    # Entry 2: "[TEST] String interning works!\n" (34 bytes, 0 params)
    .word 2                          # ID
    .word 34                         # Length
    .word 0                          # Params
    .ascii "[TEST] String interning works!\n\0"
    .align 4

__simple_string_table_end:
