// BOUNDED REMEDY PROTOTYPE, not a generic extended-ISA guarantee.
// Requires OS-enabled AVX state. Saves YMM0-15, MXCSR, ordinary Windows x64
// volatile GPRs, and RFLAGS before any user callback. No AVX-512/AMX/APX/x87
// guarantee. Production must reject those live-state profiles or provide a
// separately verified extended-state-preserving implementation.
.text
.p2align 4
.globl xray_bounded_entry
xray_bounded_entry:
    endbr64
    pushq $0
    jmp xray_bounded_common
.p2align 4
.globl xray_bounded_exit
xray_bounded_exit:
    endbr64
    pushq $1
    jmp xray_bounded_common
xray_bounded_common:
    pushfq
    push %rax
    push %rcx
    push %rdx
    push %r8
    push %r9
    push %r10
    push %r11
    // Aligned stack; 32-byte shadow, 512-byte YMM save, 16 bytes MXCSR/padding.
    sub $0x230, %rsp
    vmovdqu %ymm0, 0x020(%rsp)
    vmovdqu %ymm1, 0x040(%rsp)
    vmovdqu %ymm2, 0x060(%rsp)
    vmovdqu %ymm3, 0x080(%rsp)
    vmovdqu %ymm4, 0x0a0(%rsp)
    vmovdqu %ymm5, 0x0c0(%rsp)
    vmovdqu %ymm6, 0x0e0(%rsp)
    vmovdqu %ymm7, 0x100(%rsp)
    vmovdqu %ymm8, 0x120(%rsp)
    vmovdqu %ymm9, 0x140(%rsp)
    vmovdqu %ymm10, 0x160(%rsp)
    vmovdqu %ymm11, 0x180(%rsp)
    vmovdqu %ymm12, 0x1a0(%rsp)
    vmovdqu %ymm13, 0x1c0(%rsp)
    vmovdqu %ymm14, 0x1e0(%rsp)
    vmovdqu %ymm15, 0x200(%rsp)
    stmxcsr 0x220(%rsp)
    mov 0x270(%rsp), %edx
    mov 0x278(%rsp), %r11
    mov 2(%r11), %ecx
    call simple_trace_dispatch
    ldmxcsr 0x220(%rsp)
    vmovdqu 0x020(%rsp), %ymm0
    vmovdqu 0x040(%rsp), %ymm1
    vmovdqu 0x060(%rsp), %ymm2
    vmovdqu 0x080(%rsp), %ymm3
    vmovdqu 0x0a0(%rsp), %ymm4
    vmovdqu 0x0c0(%rsp), %ymm5
    vmovdqu 0x0e0(%rsp), %ymm6
    vmovdqu 0x100(%rsp), %ymm7
    vmovdqu 0x120(%rsp), %ymm8
    vmovdqu 0x140(%rsp), %ymm9
    vmovdqu 0x160(%rsp), %ymm10
    vmovdqu 0x180(%rsp), %ymm11
    vmovdqu 0x1a0(%rsp), %ymm12
    vmovdqu 0x1c0(%rsp), %ymm13
    vmovdqu 0x1e0(%rsp), %ymm14
    vmovdqu 0x200(%rsp), %ymm15
    add $0x230, %rsp
    pop %r11
    pop %r10
    pop %r9
    pop %r8
    pop %rdx
    pop %rcx
    pop %rax
    popfq
    lea 8(%rsp), %rsp
    ret
#if !defined(_WIN32)
.section .note.GNU-stack,"",@progbits
#endif
