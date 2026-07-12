/*
 * SimpleOS CRT0 — minimal C runtime entry point (x86_64)
 *
 * Called by the kernel's process loader after mapping the ELF.
 * Stack is already set up by the kernel. BSS must be zeroed.
 *
 * Calls main(argc, argv) then exit(retval). SimpleOS kernels that do not
 * provide an argc/argv stack still fall back to argc=0, argv=NULL.
 */

.intel_syntax noprefix
.section .text
.global _start
.type _start, @function

_start:
    /* Clear direction flag (ABI requirement) */
    cld

    /*
     * Preserve a conventional process entry stack when present:
     *   rsp[0] = argc, rsp[1...] = argv, then envp.
     * This lets the Linux-host smoke artifact run LLVM's InitLLVM path while
     * retaining the SimpleOS no-arguments fallback for early kernels.
     */
    mov     r12, qword ptr [rsp]        /* argc */
    lea     r13, [rsp + 8]              /* argv */
    xor     r14d, r14d                  /* envp */
    test    r12, r12
    jz      .Lno_initial_args
    cmp     r12, 4096
    ja      .Lno_initial_args
    cmp     qword ptr [r13], 0
    je      .Lno_initial_args
    lea     r14, [r13 + r12*8 + 8]
    jmp     .Largs_done
.Lno_initial_args:
    xor     r12d, r12d
    xor     r13d, r13d
.Largs_done:

    /* Zero BSS segment */
    lea     rdi, [rip + __bss_start]
    lea     rcx, [rip + __bss_end]
    test    rcx, rcx
    jz      .Lbss_done          /* generic links may leave weak end undefined */
    cmp     rdi, rcx
    jae     .Lbss_done          /* reject missing/reversed linker boundaries */
    sub     rcx, rdi
    jz      .Lbss_done          /* skip if BSS is empty */
    xor     eax, eax
    rep     stosb
.Lbss_done:

    /* Align stack to 16 bytes (ABI requirement) */
    and     rsp, -16

    /* Publish environ before constructors; host smoke has envp, SimpleOS may not. */
    lea     rdi, [rip + environ]
    mov     qword ptr [rdi], r14

    /* Publish argc/argv for SimpleCore's rt_cli_get_args when linked. */
    lea     rax, [rip + rt_set_args]
    test    rax, rax
    jz      .Largs_published
    mov     rdi, r12
    mov     rsi, r13
    call    rax
.Largs_published:

    /* Initialize C++ constructors and libc (.init_array) */
    call    __libc_init_array

    /* Call main(argc, argv, envp) */
    mov     edi, r12d
    mov     rsi, r13
    mov     rdx, r14
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
.weak rt_set_args

/*
 * environ: real .bss storage for the POSIX environment pointer that crt0
 * publishes (envp in r14) before running constructors. This was `.weak
 * environ`; with no libc definition it resolved to address 0, so the publish
 * store `mov [environ], r14` faulted writing to NULL (ring-3 #PF at _start,
 * errcode P|W|U, cr2=0). Give it 8 bytes of .bss — zeroed by the BSS clear
 * above, then overwritten with envp.
 */
    .bss
    .balign 8
    .globl environ
environ:
    .quad 0
