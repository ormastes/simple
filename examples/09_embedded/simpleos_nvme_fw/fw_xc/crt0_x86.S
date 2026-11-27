/* fw_xc x86 crt0 (i686 + x86_64). Standalone entry expects flat protected
   (i686) or long mode (x86_64) from a loader; the real-firmware x86_64 boot
   uses check-baremetal-efi-boot.shs's EFI shim instead. UART = COM1 port 0x3f8. */
    .section .text.entry, "ax"
    .globl _start
_start:
#ifdef __x86_64__
    lea     _stack_top(%rip), %rsp
    lea     _sbss(%rip), %rdi
    lea     _ebss(%rip), %rcx
    sub     %rdi, %rcx
    xor     %eax, %eax
    cld
    rep stosb
    call    __simple_main
#else
    mov     $_stack_top, %esp
    mov     $_sbss, %edi
    mov     $_ebss, %ecx
    sub     %edi, %ecx
    xor     %eax, %eax
    cld
    rep stosb
    call    __simple_main
#endif
1:  hlt
    jmp     1b

    .text
    .globl rt_mmio_write8
rt_mmio_write8:
#ifdef __x86_64__
    mov     %esi, %eax
#else
    mov     12(%esp), %eax   /* i64 addr at 4(%esp), i64 value lo at 12(%esp) */
#endif
    mov     $0x3f8, %dx
    outb    %al, %dx
    ret
