// Windows x64 calling convention on both native Windows and an ELF test host.
// The deterministic dispatcher is a valid ordinary Windows x64 ABI callee:
// upper vector lanes and MXCSR status bits are caller-saved. It preserves
// XMM6-15 low lanes, GPR nonvolatiles, and MXCSR control bits.
.text
.p2align 4
.globl simple_trace_dispatch
simple_trace_dispatch:
    endbr64
    cmp $0x1234, %ecx
    jne 3f
    test %edx, %edx
    jne 1f
    incl xray_seen_entries(%rip)
    jmp 4f
1:
    cmp $1, %edx
    jne 3f
    incl xray_seen_exits(%rip)
    jmp 4f
3:
    incl xray_dispatch_errors(%rip)
4:
    vzeroupper
    vpxor %xmm0, %xmm0, %xmm0
    vpxor %xmm1, %xmm1, %xmm1
    vpxor %xmm2, %xmm2, %xmm2
    vpxor %xmm3, %xmm3, %xmm3
    vpxor %xmm4, %xmm4, %xmm4
    vpxor %xmm5, %xmm5, %xmm5
    sub $8, %rsp
    stmxcsr (%rsp)
    orl $0x20, (%rsp)
    ldmxcsr (%rsp)
    add $8, %rsp
    // Deliberately change arithmetic flags as well.
    xorl %eax, %eax
    ret

.p2align 4
.globl xray_read_xcr0
xray_read_xcr0:
    endbr64
    xor %ecx, %ecx
    xgetbv
    shl $32, %rdx
    or %rdx, %rax
    ret

.macro PROBE name, target
.p2align 4
.globl \name
\name:
    endbr64
    push %rbx
    sub $0xd0, %rsp
    mov %rcx, %rbx
    movdqu %xmm6, 0x20(%rsp)
    movdqu %xmm7, 0x30(%rsp)
    movdqu %xmm8, 0x40(%rsp)
    movdqu %xmm9, 0x50(%rsp)
    movdqu %xmm10, 0x60(%rsp)
    movdqu %xmm11, 0x70(%rsp)
    movdqu %xmm12, 0x80(%rsp)
    movdqu %xmm13, 0x90(%rsp)
    movdqu %xmm14, 0xa0(%rsp)
    movdqu %xmm15, 0xb0(%rsp)
    stmxcsr 0xc0(%rsp)
    movl $0x1f80, 0xc4(%rsp)
    ldmxcsr 0xc4(%rsp)
    vmovdqu xray_pattern(%rip), %ymm0
    vmovdqu xray_pattern(%rip), %ymm1
    vmovdqu xray_pattern(%rip), %ymm2
    vmovdqu xray_pattern(%rip), %ymm3
    vmovdqu xray_pattern(%rip), %ymm4
    vmovdqu xray_pattern(%rip), %ymm5
    vmovdqu xray_pattern(%rip), %ymm6
    vmovdqu xray_pattern(%rip), %ymm7
    vmovdqu xray_pattern(%rip), %ymm8
    vmovdqu xray_pattern(%rip), %ymm9
    vmovdqu xray_pattern(%rip), %ymm10
    vmovdqu xray_pattern(%rip), %ymm11
    vmovdqu xray_pattern(%rip), %ymm12
    vmovdqu xray_pattern(%rip), %ymm13
    vmovdqu xray_pattern(%rip), %ymm14
    vmovdqu xray_pattern(%rip), %ymm15
    mov $0x123, %eax
    cmp $0x456, %eax
    pushfq
    pop %rax
    mov %rax, 0x208(%rbx)
    // Exact enabled 13-byte sled layout used by the current fixture.
    .p2align 1
    .byte 0x66, 0x90
    call \target
    .byte 0xeb, 0x04
    .long 0x1234
    pushfq
    pop %rax
    mov %rax, 0x210(%rbx)
    stmxcsr 0x200(%rbx)
    vmovdqu %ymm0, 0x000(%rbx)
    vmovdqu %ymm1, 0x020(%rbx)
    vmovdqu %ymm2, 0x040(%rbx)
    vmovdqu %ymm3, 0x060(%rbx)
    vmovdqu %ymm4, 0x080(%rbx)
    vmovdqu %ymm5, 0x0a0(%rbx)
    vmovdqu %ymm6, 0x0c0(%rbx)
    vmovdqu %ymm7, 0x0e0(%rbx)
    vmovdqu %ymm8, 0x100(%rbx)
    vmovdqu %ymm9, 0x120(%rbx)
    vmovdqu %ymm10, 0x140(%rbx)
    vmovdqu %ymm11, 0x160(%rbx)
    vmovdqu %ymm12, 0x180(%rbx)
    vmovdqu %ymm13, 0x1a0(%rbx)
    vmovdqu %ymm14, 0x1c0(%rbx)
    vmovdqu %ymm15, 0x1e0(%rbx)
    vzeroupper
    movdqu 0x20(%rsp), %xmm6
    movdqu 0x30(%rsp), %xmm7
    movdqu 0x40(%rsp), %xmm8
    movdqu 0x50(%rsp), %xmm9
    movdqu 0x60(%rsp), %xmm10
    movdqu 0x70(%rsp), %xmm11
    movdqu 0x80(%rsp), %xmm12
    movdqu 0x90(%rsp), %xmm13
    movdqu 0xa0(%rsp), %xmm14
    movdqu 0xb0(%rsp), %xmm15
    ldmxcsr 0xc0(%rsp)
    add $0xd0, %rsp
    pop %rbx
    ret
.endm

PROBE xray_probe_baseline_entry, simple_trace_entry
PROBE xray_probe_bounded_entry, xray_bounded_entry
PROBE xray_probe_baseline_exit, simple_trace_exit
PROBE xray_probe_bounded_exit, xray_bounded_exit

.p2align 5
xray_pattern:
    .byte 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16
    .byte 17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32

.data
.p2align 2
.globl xray_dispatch_errors
xray_dispatch_errors:
    .long 0
.globl xray_seen_entries
xray_seen_entries:
    .long 0
.globl xray_seen_exits
xray_seen_exits:
    .long 0

#if !defined(_WIN32)
.section .note.GNU-stack,"",@progbits
#endif
