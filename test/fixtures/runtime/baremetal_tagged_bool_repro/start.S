/* Linux user-mode entry only; no device boot or production startup claim. */
.text
.global repro_start
#if defined(__x86_64__)
repro_start:
    xor %rbp, %rbp
    and $-16, %rsp
    call repro_main
    mov %eax, %edi
    mov $60, %eax
    syscall
#elif defined(__aarch64__)
repro_start:
    bl repro_main
    mov x8, #93
    svc #0
#else
#error unsupported architecture
#endif
.section .note.GNU-stack,"",%progbits
