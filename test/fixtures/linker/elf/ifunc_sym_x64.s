# Static IFUNC symtab fixture: add_val is STT_GNU_IFUNC (resolver = resolve).
    .text
    .globl _start
    .type _start, @function
_start:
    mov fp(%rip), %rax
    call add_val
    ret
    .type resolve, @function
resolve:
    lea impl(%rip), %rax
    ret
impl:
    ret
    .globl add_val
    .type add_val, @gnu_indirect_function
    .set add_val, resolve
    .data
    .globl fp
fp:
    .quad add_val
