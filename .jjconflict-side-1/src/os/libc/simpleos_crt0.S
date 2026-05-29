/*
 * SimpleOS CRT0 — minimal C runtime entry point (x86_64)
 *
 * Called by the kernel's process loader after mapping the ELF.
 * Stack is already set up by the kernel. BSS must be zeroed.
 *
 * Calls main(argc=0, argv=NULL) then exit(retval).
 */

.intel_syntax noprefix
.section .text
.global _start
.type _start, @function

_start:
    /* Clear direction flag (ABI requirement) */
    cld

    /* Zero BSS segment */
    lea     rdi, [rip + __bss_start]
    lea     rcx, [rip + __bss_end]
    sub     rcx, rdi
    jz      .Lbss_done          /* skip if BSS is empty */
    xor     eax, eax
    rep     stosb
.Lbss_done:

    /* Align stack to 16 bytes (ABI requirement) */
    and     rsp, -16

    /* Initialize C++ constructors and libc (.init_array) */
    call    __libc_init_array

    /* Set environ to NULL (no initial environment from kernel yet) */
    lea     rdi, [rip + environ]
    mov     qword ptr [rdi], 0

    /* Call main(argc=0, argv=NULL, envp=NULL) */
    xor     edi, edi            /* argc = 0 */
    xor     esi, esi            /* argv = NULL */
    xor     edx, edx            /* envp = NULL */
    call    main

    /* Exit with main's return value */
    mov     edi, eax
    call    exit

    /* Should never reach here */
    hlt
    jmp     _start

.size _start, . - _start

/*
 * Provide weak symbols for __bss_start / __bss_end
 * so this file assembles standalone. The linker script
 * overrides these with the actual BSS boundaries.
 */
.weak __bss_start
.weak __bss_end
.weak environ
