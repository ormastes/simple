.data
.p2align 3
.globl encoded_sizes
.type encoded_sizes,@object
encoded_sizes:
    .long 0
    .reloc encoded_sizes, R_X86_64_SIZE32, sized_object
    .long 0
    .quad 0
    .reloc encoded_sizes + 8, R_X86_64_SIZE64, sized_object
.size encoded_sizes, 16

.text
.globl _start
.type _start,@function
_start:
    ret
.size _start, .-_start
