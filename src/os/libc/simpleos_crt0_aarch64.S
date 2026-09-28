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
     * Preserve and validate the conventional process entry stack:
     *   sp[0] = argc, sp[1...] = argv, then envp.
     * argv is capped at 64 entries and envp at 128, matching the admitted
     * executable-launch contract.  Rejecting a
     * malformed image here is deliberate: constructors and user code must
     * never observe attacker-controlled unterminated vectors.
     */
    mov     x22, sp                     /* immutable entry SP */
    tst     x22, #15
    b.ne    .Lmalformed_initial_stack
    ldr     x19, [x22]                  /* argc */
    mov     x9, #64
    cmp     x19, x9
    b.hi    .Lmalformed_initial_stack
    add     x20, x22, #8                /* argv */
    mov     x10, x19                    /* validate every declared argv slot */
    mov     x11, x20
    cbz     x10, .Largv_terminated
.Lscan_argv:
    ldr     x9, [x11], #8
    cbz     x9, .Lmalformed_initial_stack
    subs    x10, x10, #1
    b.ne    .Lscan_argv
.Largv_terminated:
    ldr     x9, [x20, x19, lsl #3]
    cbnz    x9, .Lmalformed_initial_stack
    add     x21, x20, x19, lsl #3
    add     x21, x21, #8                /* envp = &argv[argc + 1] */
    mov     x11, x21                    /* bounded validation cursor */
    mov     x10, #128
.Lscan_envp:
    ldr     x9, [x11], #8
    cbz     x9, .Lenvp_terminated
    subs    x10, x10, #1
    b.ne    .Lscan_envp
    /* Exactly 128 entries are valid only when the next slot terminates. */
    ldr     x9, [x11]
    cbnz    x9, .Lmalformed_initial_stack
.Lenvp_terminated:

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

    /*
     * Generated native artifacts may provide this hook to run the manifest
     * startup admission before constructors and user code.  It is weak so
     * existing C-only and legacy SimpleOS executables keep their exact entry
     * behavior until they carry a manifest-aware generated entry.
     */
    ldr     x9, =__simple_startup_before_main
    cbz     x9, .Lstartup_before_main_done
    mov     x0, x19
    mov     x1, x20
    blr     x9
    cbnz    x0, .Lstartup_admission_failed
.Lstartup_before_main_done:

    /* Initialize C++ constructors and libc (.init_array) */
    bl      __libc_init_array

    /*
     * Run Simple module-global initializers (native_project/linker.rs
     * generate_init_caller). __libc_init_array above only walks
     * .init_array, which cranelift/native-project codegen never populates
     * for this freestanding aarch64-unknown-simpleos userspace target (see
     * doc/08_tracking/bug/simpleos_userspace_crt0_missing_module_init_call_empty_init_array_2026-08-06.md,
     * which fixed the identical gap on x86_64 in simpleos_crt0.S).
     * Weak-guarded exactly like the x86_64 userspace crt0 fix and the
     * SimpleOS kernel's own boot crt0
     * (examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s), using the
     * same weak-symbol-branch idiom already used above for rt_set_args, so a
     * link with no module-init functions to aggregate still resolves
     * cleanly.
     */
    ldr     x9, =__simple_call_module_inits
    cbz     x9, .Lmodule_inits_done
    blr     x9
.Lmodule_inits_done:

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

    /* Manifest/startup admission failure has its reserved raw exit status. */
.Lstartup_admission_failed:
    mov     x0, #125
    b       .Lraw_exit

    /*
     * No libc call is safe before the initial stack has been admitted.
     * Syscall 0 is the always-authorized SimpleOS process exit operation;
     * issue it directly so malformed input cannot reach constructors.
     */
.Lmalformed_initial_stack:
    mov     x0, #127
.Lraw_exit:
    mov     x8, #0
    svc     #0
    wfe
    b       .Lmalformed_initial_stack

.size _start, . - _start

.weak __bss_start
.weak __bss_end
.weak rt_set_args
.weak __simple_call_module_inits
.weak __simple_startup_before_main

/*
 * environ: real .bss storage for the POSIX environment pointer (see the
 * x86_64 crt0 comment — a weak-undefined environ resolves to address 0 and
 * the publish store faults at NULL in ring-3/EL0).
 */
    .bss
    .balign 8
    .weak environ
environ:
    .quad 0
