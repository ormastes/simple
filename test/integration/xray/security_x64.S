.text
.p2align 4
.globl security_return_control
.def security_return_control; .scl 2; .type 32; .endef
security_return_control:
    endbr64
    movl $0x5678, %eax
    retq

.p2align 4
.globl security_cet_bad_return
.def security_cet_bad_return; .scl 2; .type 32; .endef
security_cet_bad_return:
    endbr64
    // Change ONLY the normal-stack return address to a real executable label.
    // A successful RET reaches a sentinel ExitProcess instead of random memory.
    leaq .Lunchecked(%rip), %rax
    movq %rax, (%rsp)
    retq
.Lunchecked:
    endbr64
    // RET popped the old slot, so RSP is 16-byte aligned here. Reserve shadow
    // space then CALL the no-return C helper using the normal Windows x64 ABI.
    subq $32, %rsp
    callq security_unchecked_landing
    int3
