/*
 * Simple Seed — Windows x86_64 entry
 *
 * PE entry point for console applications.
 * Windows does not pass argc/argv on the stack — the CRT must
 * parse them from GetCommandLineA.
 *
 * For MinGW: entry is mainCRTStartup (console subsystem).
 * For MSVC/clang-cl: entry is mainCRTStartup.
 */

    .section .text
    .global mainCRTStartup

mainCRTStartup:
    sub     $0x28, %rsp             /* 32-byte shadow space + 8 alignment */

    call    __spl_start_win

    /* Should never return */
    ud2

/*
 * Also provide _start as alias for linkers that expect it.
 */
    .global _start
_start:
    jmp     mainCRTStartup
