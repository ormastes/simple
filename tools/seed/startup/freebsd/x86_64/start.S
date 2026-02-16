/*
 * Simple Seed — FreeBSD x86_64 _start
 *
 * Entry point for ELF executables on FreeBSD x86_64.
 * Same stack layout as Linux: kernel places argc, argv, envp on stack.
 * Syscall numbers differ (handled in crt_freebsd.c).
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    xor     %rbp, %rbp

    mov     (%rsp), %rdi            /* argc */
    lea     8(%rsp), %rsi           /* argv */
    lea     8(%rsi,%rdi,8), %rdx    /* envp */

    and     $~0xF, %rsp

    call    __spl_start

    ud2

    .size _start, . - _start
