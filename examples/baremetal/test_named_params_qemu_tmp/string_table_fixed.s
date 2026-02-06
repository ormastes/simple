.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    .word 3                          # Entry count

    # Entry 1: "Hello, {}!\n" (11 chars + null = 12 bytes)
    .word 1                          # ID
    .word 12                         # Length
    .word 1                          # Params
    .ascii "Hello, {}!\n\0"
    .byte 0, 0                       # Padding to 4-byte boundary (12+2=16 aligned to next 4)
    .align 4

    # Entry 2: "User: {}, Age: {}\n" (18 chars + null = 19 bytes, pad to 20)
    .word 2                          # ID
    .word 19                         # Length (actual string length)
    .word 2                          # Params
    .ascii "User: {}, Age: {}\n\0"
    .byte 0                          # Padding to 4-byte boundary
    .align 4

    # Entry 3: "RGB({}, {}, {})\n" (16 chars + null = 17 bytes, pad to 20)
    .word 3                          # ID
    .word 17                         # Length
    .word 3                          # Params
    .ascii "RGB({}, {}, {})\n\0"
    .byte 0, 0, 0                    # Padding to 4-byte boundary
    .align 4

__simple_string_table_end:
