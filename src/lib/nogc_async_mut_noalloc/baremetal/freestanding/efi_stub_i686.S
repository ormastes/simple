/* IA32 UEFI entry stub for the bare-metal hello image.
 *
 * Linked FIRST (.text.boot) by the Simple linker (elf_i686 raw image at a
 * fixed base), so it sits at offset 0 of the flat blob that
 * scripts/check/baremetal-efi-wrap.spl wraps in a PE32 EFI app (machine
 * 0x14c). Blob contract: offset 0 = short jump, offset 8 = u64 blob length
 * patched by the wrapper.
 *
 * The blob is linked at its own first byte (efi_entry) and carries absolute
 * 32-bit relocations, so the stub asks BootServices->AllocatePages for exactly
 * that address (AllocateAddress = 2, EfiLoaderCode = 1), copies the whole blob
 * there and jumps to _start. Until the copy the stub runs wherever the
 * firmware loaded the PE, so it finds itself with call/pop.
 * UEFI IA32: cdecl, SystemTable->BootServices at 60, AllocatePages at 32.
 */
    .section .text.boot,"ax"
    .globl efi_entry
efi_entry:
    jmp     1f
    .balign 8
efi_blob_len:
    .quad   0
1:
    push    %ebp
    mov     %esp, %ebp
    push    %ebx
    push    %esi
    push    %edi
    sub     $16, %esp
    call    2f
2:  pop     %ebx
    sub     $(2b - efi_entry), %ebx        /* ebx = blob's current address */
    movl    $efi_entry, -24(%ebp)          /* u64 addr = link base */
    movl    $0, -20(%ebp)
    mov     12(%ebp), %eax                 /* SystemTable */
    mov     60(%eax), %eax                 /* BootServices */
    mov     32(%eax), %eax                 /* AllocatePages */
    mov     8(%ebx), %ecx
    add     $4095, %ecx
    shr     $12, %ecx
    lea     -24(%ebp), %edx
    push    %edx
    push    %ecx
    push    $1
    push    $2
    call    *%eax
    add     $16, %esp
    test    %eax, %eax
    jnz     9f
    mov     %ebx, %esi
    mov     $efi_entry, %edi
    mov     8(%ebx), %ecx
    cld
    rep movsb
    mov     $_start, %eax
    jmp     *%eax
9:  jmp     9b
