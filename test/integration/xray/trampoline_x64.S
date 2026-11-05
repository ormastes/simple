// Windows x64 ABI-preserving trampoline for the 13-byte no-clobber sled.
// Read the function ID at [sled CALL return address + 2]; all registers/flags
// survive dispatch. Ordinary CALL/RET balance is CET shadow-stack compatible.
.text
.p2align 4
.globl simple_trace_entry
simple_trace_entry:
    endbr64
    pushq $0
    jmp simple_trace_common

.p2align 4
.globl simple_trace_exit
simple_trace_exit:
    endbr64
    pushq $1
    jmp simple_trace_common

simple_trace_common:
    pushfq
    push %rax
    push %rcx
    push %rdx
    push %r8
    push %r9
    push %r10
    push %r11
    // RSP is 16-byte aligned here. 32-byte shadow + 6 XMM registers.
    sub $0x80, %rsp
    movdqu %xmm0, 0x20(%rsp)
    movdqu %xmm1, 0x30(%rsp)
    movdqu %xmm2, 0x40(%rsp)
    movdqu %xmm3, 0x50(%rsp)
    movdqu %xmm4, 0x60(%rsp)
    movdqu %xmm5, 0x70(%rsp)
    // Stack: [RSP+0xc0] trace kind, [RSP+0xc8] CALL return address.
    mov 0xc0(%rsp), %edx
    mov 0xc8(%rsp), %r11
    mov 2(%r11), %ecx
    call simple_trace_dispatch
    movdqu 0x20(%rsp), %xmm0
    movdqu 0x30(%rsp), %xmm1
    movdqu 0x40(%rsp), %xmm2
    movdqu 0x50(%rsp), %xmm3
    movdqu 0x60(%rsp), %xmm4
    movdqu 0x70(%rsp), %xmm5
    add $0x80, %rsp
    pop %r11
    pop %r10
    pop %r9
    pop %r8
    pop %rdx
    pop %rcx
    pop %rax
    popfq
    // Skip our own kind word without modifying restored flags.
    lea 8(%rsp), %rsp
    ret
