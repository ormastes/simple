/*
 * Simple Seed — macOS x86_64 _start
 *
 * Entry point for Mach-O executables on macOS x86_64.
 * Kernel places argc, argv, envp on the stack (same layout as Linux):
 *   (%rsp)        = argc
 *   8(%rsp)       = argv[0]
 *   ...
 *   8+8*argc(%rsp)= NULL (argv terminator)
 *   next          = envp[0], ..., NULL
 *
 * Mach-O conventions: symbols get _ prefix, no .type/.size directives.
 */

    .section __TEXT,__text
    .global _main
    .global __start

__start:
_main:
    xor     %rbp, %rbp              /* ABI: clear frame pointer */

    mov     (%rsp), %rdi            /* argc */
    lea     8(%rsp), %rsi           /* argv */
    lea     8(%rsi,%rdi,8), %rdx    /* envp = &argv[argc + 1] */

    and     $~0xF, %rsp             /* Align stack to 16 bytes */

    call    ___spl_start            /* __spl_start(argc, argv, envp) */

    /* Should never return */
    ud2
