/*
 * Simple Seed — FreeBSD x86 (i386) _start
 *
 * Entry point for ELF executables on FreeBSD i386.
 * Same stack layout as Linux i386.
 * Syscall convention differs (handled in crt_freebsd.c).
 */

    .section .text
    .global _start
    .type _start, @function

_start:
    xor     %ebp, %ebp

    mov     (%esp), %eax            /* argc */
    lea     4(%esp), %ecx           /* argv */
    lea     4(%ecx,%eax,4), %edx    /* envp */

    and     $~0xF, %esp

    push    %edx
    push    %ecx
    push    %eax

    call    __spl_start

    ud2

    .size _start, . - _start
