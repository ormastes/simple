.section .smt, "a"
.align 4
.global __simple_string_table
__simple_string_table:
    .word 3                          # Entry count

    # Entry 1: "Hello, {}!" - param_names: ["name"]
    .word 1                          # ID
    .word 12                         # Length
    .word 1                          # Params
    .ascii "Hello, {}!\n\0"
    .align 4

    # Entry 2: "User: {}, Age: {}" - param_names: ["username", "age"]
    .word 2                          # ID
    .word 20                         # Length
    .word 2                          # Params
    .ascii "User: {}, Age: {}\n\0"
    .align 4

    # Entry 3: "RGB({}, {}, {})" - param_names: ["r", "g", "b"]
    .word 3                          # ID
    .word 18                         # Length
    .word 3                          # Params
    .ascii "RGB({}, {}, {})\n\0"
    .align 4

__simple_string_table_end:
