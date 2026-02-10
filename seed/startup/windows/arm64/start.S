/*
 * Simple Seed — Windows arm64 (AArch64) entry
 *
 * PE entry point for console applications on Windows ARM64.
 * Windows does not pass argc/argv — the CRT must parse them
 * from GetCommandLineA.
 *
 * ARM64 Windows calling convention: x0-x7 for args,
 * 16-byte stack alignment required at call site.
 */

    .section .text
    .global mainCRTStartup

    .p2align 2

mainCRTStartup:
    /* Reserve stack space (16-byte aligned) */
    sub     sp, sp, #32

    bl      __spl_start_win

    /* Should never return */
    brk     #0xF000

/*
 * Also provide _start as alias for linkers that expect it.
 */
    .global _start
_start:
    b       mainCRTStartup
