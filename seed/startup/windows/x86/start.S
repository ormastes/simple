/*
 * Simple Seed — Windows x86 (i386) entry
 *
 * PE entry point for 32-bit console applications.
 * Uses cdecl calling convention.
 */

    .section .text
    .global _mainCRTStartup

_mainCRTStartup:
    and     $~0xF, %esp             /* Align stack to 16 bytes */
    sub     $0x10, %esp             /* Reserve space */

    call    ___spl_start_win

    ud2

/*
 * Also provide __start as alias (MinGW i386 convention).
 */
    .global __start
__start:
    jmp     _mainCRTStartup
