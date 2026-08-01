/*
 * SimpleOS CRT0 — minimal C runtime entry point (aarch64)
 *
 * Mirror of simpleos_crt0.S (x86_64) for aarch64-unknown-simpleos.
 * Called by the kernel's process loader after mapping the ELF.
 * Stack is already set up by the kernel. BSS must be zeroed.
 *
 * Calls main(argc, argv, envp) then exit(retval). SimpleOS kernels that do
 * not provide an argc/argv stack still fall back to argc=0, argv=NULL.
 */

.section .text
.global _start
.type _start, @function

_start:
    /*
     * Preserve a conventional process entry stack when present:
     *   sp[0] = argc, sp[1...] = argv, then envp.
     * Falls back to argc=0/argv=NULL/envp=NULL for early kernels that eret
     * with an empty stack.
     */
    ldr     x19, [sp]                   /* argc */
    add     x20, sp, #8                 /* argv */
    mov     x21, xzr                    /* envp */
    cbz     x19, .Lno_initial_args
    mov     x9, #4096
    cmp     x19, x9
    b.hi    .Lno_initial_args
    ldr     x9, [x20]
    cbz     x9, .Lno_initial_args
    add     x21, x20, x19, lsl #3
    add     x21, x21, #8
    b       .Largs_done
.Lno_initial_args:
    mov     x19, xzr
    mov     x20, xzr
.Largs_done:

    /* Zero BSS segment (weak boundaries: literal-pool loads tolerate 0) */
    ldr     x0, =__bss_start
    ldr     x1, =__bss_end
    cbz     x1, .Lbss_done              /* generic links may leave weak end undefined */
    cmp     x0, x1
    b.hs    .Lbss_done                  /* reject missing/reversed linker boundaries */
.Lbss_loop:
    strb    wzr, [x0], #1
    cmp     x0, x1
    b.lo    .Lbss_loop
.Lbss_done:

    /* Align stack to 16 bytes (AAPCS64 requirement) */
    mov     x9, sp
    and     x9, x9, #-16
    mov     sp, x9

    /* Publish environ before constructors; host smoke has envp, SimpleOS may not. */
    ldr     x0, =environ
    str     x21, [x0]

    /* Publish argc/argv for SimpleCore's rt_cli_get_args when linked (weak). */
    ldr     x9, =rt_set_args
    cbz     x9, .Largs_published
    mov     x0, x19
    mov     x1, x20
    blr     x9
.Largs_published:

    /* Initialize C++ constructors and libc (.init_array) */
    bl      __libc_init_array

    /* Call main(argc, argv, envp) */
    mov     x0, x19
    mov     x1, x20
    mov     x2, x21
    bl      main

    /* Exit with main's return value */
    bl      exit

    /* Should never reach here */
.Lhang:
    wfe
    b       .Lhang

.size _start, . - _start

.weak __bss_start
.weak __bss_end
.weak rt_set_args

/*
 * environ: real .bss storage for the POSIX environment pointer (see the
 * x86_64 crt0 comment — a weak-undefined environ resolves to address 0 and
 * the publish store faults at NULL in ring-3/EL0).
 */
    .bss
    .balign 8
    .globl environ
environ:
    .quad 0
