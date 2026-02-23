/*
 * Simple Seed — Linux x86_64 _start
 *
 * Entry point for ELF executables on Linux x86_64.
 * Kernel places argc, argv, envp on the stack:
 *   (%rsp)        = argc
 *   8(%rsp)       = argv[0]
 *   ...
 *   8+8*argc(%rsp)= NULL (argv terminator)
 *   next          = envp[0], ..., NULL
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    xor     %rbp, %rbp              /* ABI: clear frame pointer */

    mov     (%rsp), %rdi            /* argc */
    lea     8(%rsp), %rsi           /* argv */
    lea     8(%rsi,%rdi,8), %rdx    /* envp = &argv[argc + 1] */

    and     $~0xF, %rsp             /* Align stack to 16 bytes */

    call    __spl_start             /* __spl_start(argc, argv, envp) */

    /* Should never return — __spl_start calls __spl_exit */
    ud2

    .size _start, . - _start
