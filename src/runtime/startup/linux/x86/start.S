/*
 * Simple Seed — Linux x86 (i386) _start
 *
 * Entry point for ELF executables on Linux i386.
 * Kernel places argc, argv, envp on the stack:
 *   (%esp)        = argc
 *   4(%esp)       = argv[0]
 *   ...
 *   4+4*argc(%esp)= NULL
 *   next          = envp[0], ..., NULL
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    xor     %ebp, %ebp              /* ABI: clear frame pointer */

    mov     (%esp), %eax            /* argc */
    lea     4(%esp), %ecx           /* argv */
    /* envp = argv + (argc + 1) * 4 */
    lea     4(%ecx,%eax,4), %edx    /* envp */

    and     $~0xF, %esp             /* Align stack to 16 bytes */

    push    %edx                    /* envp (arg 3) */
    push    %ecx                    /* argv (arg 2) */
    push    %eax                    /* argc (arg 1) */

    call    __spl_start             /* __spl_start(argc, argv, envp) */

    ud2

    .size _start, . - _start
