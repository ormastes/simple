// x86_64 UEFI entry stub for the bare-metal hello image.
//
// Linked FIRST in .text.boot by the Simple linker, so it sits at offset 0 of
// the flat blob that baremetal-efi-wrap.spl wraps in a PE32+ EFI app
// (machine 0x8664, entry RVA = section start). Blob contract shared with
// pe_efi_blob.spl: offset 0 = short jmp, offset 8 = u64 blob length patched
// by the wrapper.
//
// The PE section is read+execute only, so the stub copies the whole blob into
// BootServices->AllocatePages(AnyPages, EfiLoaderCode) pages and jumps to
// _start there. MS x64 ABI: rcx = ImageHandle, rdx = SystemTable.
// Offsets: SystemTable->BootServices at 96, BootServices->AllocatePages at 40.
// Everything is RIP-relative, so the blob runs wherever it is copied.

    .section .text.boot,"ax"
    .globl efi_entry
    .balign 8
efi_entry:
    jmp     1f
    .balign 8, 0x90
efi_blob_len:
    .quad   0
1:
    push    %rbx
    push    %rsi
    push    %rdi
    sub     $48, %rsp               // 32 shadow + out slot at 32; keeps rsp 16-aligned
    movq    $0, 32(%rsp)
    mov     96(%rdx), %rax          // SystemTable->BootServices
    mov     40(%rax), %rax          // BootServices->AllocatePages
    mov     efi_blob_len(%rip), %r8
    add     $4095, %r8
    shr     $12, %r8                // pages
    xor     %ecx, %ecx              // AllocateAnyPages
    mov     $1, %edx                // EfiLoaderCode
    lea     32(%rsp), %r9           // &addr
    call    *%rax
    test    %rax, %rax
    jnz     9f
    mov     32(%rsp), %rdi
    mov     %rdi, %rbx
    lea     efi_entry(%rip), %rsi
    mov     efi_blob_len(%rip), %rcx
    cld
    rep movsb
    lea     _start(%rip), %rax
    lea     efi_entry(%rip), %rcx
    sub     %rcx, %rax
    add     %rbx, %rax
    jmp     *%rax
9:
    hlt
    jmp     9b
