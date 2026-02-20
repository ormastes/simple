/*
 * Simple Seed — macOS arm64 (AArch64) _start
 *
 * Entry point for Mach-O executables on Apple Silicon.
 * Kernel places argc, argv, envp on the stack:
 *   (sp)          = argc
 *   8(sp)         = argv[0]
 *   ...
 *   8+8*argc(sp)  = NULL (argv terminator)
 *   next          = envp[0], ..., NULL
 *
 * Mach-O conventions: symbols get _ prefix, no .type/.size directives.
 * ARM64 calling convention: x0-x7 for args, 16-byte stack alignment.
 */

    .section __TEXT,__text
    .global _main
    .global __start

    .p2align 2

__start:
_main:
    /* Extract argc, argv, envp from stack */
    ldr     x0, [sp]               /* argc */
    add     x1, sp, #8             /* argv = sp + 8 */
    add     x2, x0, #1             /* argc + 1 */
    add     x2, x1, x2, lsl #3    /* envp = argv + (argc+1)*8 */

    /* Align stack to 16 bytes */
    mov     x3, sp
    and     x3, x3, #~0xF
    mov     sp, x3

    bl      ___spl_start           /* __spl_start(argc, argv, envp) */

    /* Should never return */
    brk     #0x1
