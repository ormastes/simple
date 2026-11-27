/* IA32 UEFI entry stub for the bare-metal hello image.
 *
 * Linked FIRST (.text.boot) by the Simple linker (elf_i386 raw image), so it
 * sits at offset 0 of the flat blob that scripts/check/baremetal-efi-wrap.spl
 * wraps in a PE32 EFI app (machine 0x14c). Blob contract: offset 0 = short
 * jump, offset 8 = u64 blob length patched by the wrapper.
 *
 * The blob is position independent (crt0_i686 and compiled code address data
 * via GOTPC/GOTOFF), so the stub asks BootServices->AllocatePages for
 * AnyPages (0) of EfiLoaderCode (1) -- OVMF IA32 has no free memory at a fixed
 * 16 MiB address (AllocateAddress returned EFI_NOT_FOUND) -- copies the whole
 * blob there and jumps to _start at the same offset. The stub finds itself
 * with call/pop. UEFI IA32: cdecl, SystemTable->BootServices at 60,
 * AllocatePages at 32, EFI_STATUS is 32-bit.
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
    movl    $0, -24(%ebp)                  /* u64 addr out-param */
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
    push    $0
    call    *%eax
    add     $16, %esp
    test    %eax, %eax
    jnz     9f
    mov     %ebx, %esi
    mov     -24(%ebp), %edi
    mov     8(%ebx), %ecx
    cld
    rep movsb
    mov     $_start, %eax                  /* link-time offset of _start ... */
    sub     $efi_entry, %eax               /* ... from the blob start */
    add     -24(%ebp), %eax
    jmp     *%eax
9:  jmp     9b
