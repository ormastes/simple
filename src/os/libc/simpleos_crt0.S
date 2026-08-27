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

    /* Publish argc/argv for SimpleCore's rt_cli_get_args when linked. */
    lea     rax, [rip + rt_set_args]
    test    rax, rax
    jz      .Largs_published
    mov     rdi, r12
    mov     rsi, r13
    call    rax
.Largs_published:

    /*
     * Generated native artifacts may provide this hook to run the manifest
     * startup admission before constructors and user code.  It is weak so
     * existing C-only and legacy SimpleOS executables keep their exact entry
     * behavior until they carry a manifest-aware generated entry.
     */
    lea     rax, [rip + __simple_startup_before_main]
    test    rax, rax
    jz      .Lstartup_before_main_done
    mov     rdi, r12
    mov     rsi, r13
    call    rax
.Lstartup_before_main_done:

    /* Initialize C++ constructors and libc (.init_array) */
    call    __libc_init_array

    /*
     * Run Simple module-global initializers (native_project/linker.rs
     * generate_init_caller). __libc_init_array above only walks
     * .init_array, which cranelift/native-project codegen never populates
     * for this freestanding x86_64-unknown-simpleos userspace target (see
     * doc/08_tracking/bug/simpleos_userspace_crt0_missing_module_init_call_empty_init_array_2026-08-06.md).
     * Weak-guarded exactly like the SimpleOS kernel's own crt0
     * (examples/09_embedded/simple_os/arch/x86_64/boot/crt0.s) and the
     * hosted-platform main() stub (native_project/linker.rs
     * compile_main_stub) both already do, so a link with no module-init
     * functions to aggregate still resolves cleanly.
     */
    lea     rax, [rip + __simple_call_module_inits]
    test    rax, rax
    jz      .Lmodule_inits_done
    call    rax
.Lmodule_inits_done:

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

    /*
     * No libc call is safe before the initial stack has been admitted.
     * Syscall 0 is the always-authorized SimpleOS process exit operation;
     * issue it directly so malformed input cannot reach constructors.
     */
.Lmalformed_initial_stack:
    mov     edi, 127
.Lraw_exit:
    xor     eax, eax
    syscall
.Lmalformed_hang:
    hlt
    jmp     .Lmalformed_hang

    /* Manifest startup admission rejected the otherwise valid image. */
.Lstartup_rejected:
    mov     edi, 125
    jmp     .Lraw_exit

.size _start, . - _start

/*
 * Provide weak symbols for __bss_start / __bss_end
 * so this file assembles standalone. The linker script
 * overrides these with the actual BSS boundaries.
 */
.weak __bss_start
.weak __bss_end
.weak __simple_call_module_inits
.weak rt_set_args
.weak __simple_startup_before_main

/*
 * environ: fallback .bss storage for the POSIX environment pointer that crt0
 * publishes (envp in r14) before running constructors.
 *
 * History, both directions of this trap:
 *   1. Originally `.weak environ` with NO libc definition anywhere: it resolved
 *      to address 0, so the publish store `mov [environ], r14` faulted writing
 *      to NULL (ring-3 #PF at _start, errcode P|W|U, cr2=0). Fixed by giving it
 *      real storage here.
 *   2. That fix used `.globl`, which then collided once libc gained its own
 *      definition (`char **environ = _env_storage;` in simpleos_process.c):
 *      `ld.lld: error: duplicate symbol: environ`, crt0.o(.bss) vs
 *      simpleos_process.o(.data). crt0.o is always linked explicitly, so the
 *      clash was unconditional and broke the lld link of the cross toolchain.
 *
 * WEAK is the definition that satisfies both: when libc's process object is
 * linked its strong definition wins and crt0 publishes envp into the real libc
 * pointer; when it is not, this storage keeps the publish store off NULL.
 * Do not promote this back to .globl.
 */
    .bss
    .balign 8
    .weak environ
environ:
    .quad 0
