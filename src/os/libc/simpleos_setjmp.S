/*
 * SimpleOS setjmp/longjmp — x86_64 implementation
 *
 * jmp_buf layout (8 x uint64_t):
 *   [0] rbx  [1] rsp  [2] rbp  [3] r12
 *   [4] r13  [5] r14  [6] r15  [7] rip
 *
 * setjmp saves callee-saved registers and return address.
 * longjmp restores them and returns the specified value.
 */

.section .text

/* int setjmp(jmp_buf env) */
/* env pointer is in rdi (System V AMD64 ABI) */
.global setjmp
.type setjmp, @function
setjmp:
    /* Save callee-saved registers */
    movq %rbx, 0(%rdi)
    /* Save rsp AFTER the call instruction pushed the return address */
    leaq 8(%rsp), %rax     /* rsp value the caller will see on return */
    movq %rax, 8(%rdi)
    movq %rbp, 16(%rdi)
    movq %r12, 24(%rdi)
    movq %r13, 32(%rdi)
    movq %r14, 40(%rdi)
    movq %r15, 48(%rdi)
    /* Save return address (top of stack = caller's rip) */
    movq (%rsp), %rax
    movq %rax, 56(%rdi)
    /* Return 0 on initial call */
    xorl %eax, %eax
    ret
.size setjmp, . - setjmp

/* Alias: _setjmp = setjmp (POSIX) */
.global _setjmp
.type _setjmp, @function
_setjmp:
    jmp setjmp
.size _setjmp, . - _setjmp

/* void longjmp(jmp_buf env, int val) */
/* env in rdi, val in esi */
.global longjmp
.type longjmp, @function
longjmp:
    /* Ensure val is non-zero (longjmp(buf, 0) must return 1) */
    movl %esi, %eax
    testl %eax, %eax
    jnz .Lval_ok
    movl $1, %eax
.Lval_ok:
    /* Restore callee-saved registers */
    movq 0(%rdi), %rbx
    movq 8(%rdi), %rsp
    movq 16(%rdi), %rbp
    movq 24(%rdi), %r12
    movq 32(%rdi), %r13
    movq 40(%rdi), %r14
    movq 48(%rdi), %r15
    /* Jump to saved return address */
    jmpq *56(%rdi)
.size longjmp, . - longjmp

/* Alias: _longjmp = longjmp (POSIX) */
.global _longjmp
.type _longjmp, @function
_longjmp:
    jmp longjmp
.size _longjmp, . - _longjmp
