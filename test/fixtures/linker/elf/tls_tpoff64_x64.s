.section .tdata,"awT",@progbits
.p2align 3
.globl tls_tpoff64_value
.type tls_tpoff64_value,@object
tls_tpoff64_value:
    .quad 1
.size tls_tpoff64_value, 8

.data
.p2align 3
.globl tls_tpoff64_offset
.type tls_tpoff64_offset,@object
tls_tpoff64_offset:
    .quad tls_tpoff64_value@tpoff
.size tls_tpoff64_offset, 8

.text
.globl _start
.type _start,@function
_start:
    ret
.size _start, .-_start
