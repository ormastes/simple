/*
 * Simple Seed — Linux RISC-V 64 (RV64) _start
 *
 * Entry point for ELF executables on Linux RISC-V 64.
 * Kernel places argc, argv, envp on the stack:
 *   (sp)          = argc
 *   8(sp)         = argv[0]
 *   ...
 *   8+8*argc(sp)  = NULL (argv terminator)
 *   next          = envp[0], ..., NULL
 *
 * RISC-V calling convention: a0-a7 for args, 16-byte stack alignment.
 */

    .section .text
    .global _start
    .type _start, @function

    .align 2

_start:
    /* Clear frame pointer and return address */
    li      s0, 0
    li      ra, 0

    /* Extract argc from stack */
    ld      a0, 0(sp)              /* argc */
    addi    a1, sp, 8              /* argv = sp + 8 */

    /* envp = argv + (argc + 1) * 8 */
    addi    a2, a0, 1
    slli    a2, a2, 3
    add     a2, a1, a2             /* envp */

    /* Align stack to 16 bytes */
    andi    sp, sp, ~0xF

    call    __spl_start            /* __spl_start(argc, argv, envp) */

    /* Should never return — __spl_start calls __spl_exit */
    ebreak

    .size _start, . - _start
