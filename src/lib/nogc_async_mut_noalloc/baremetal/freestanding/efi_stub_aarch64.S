// AArch64 UEFI entry stub for the bare-metal hello image.
//
// Linked FIRST in .text.boot by the Simple linker, so it sits at offset 0 of
// the flat blob that baremetal-efi-wrap.spl wraps in a PE32+ EFI app
// (machine 0xAA64, entry RVA = section start). Blob contract shared with
// baremetal-efi-wrap.spl: offset 0 = 4-byte branch, offset 8 = u64 blob
// length patched by the wrapper.
//
// AAVMF maps PE sections W^X, so the stub copies the whole blob into
// BootServices->AllocatePages(AnyPages, EfiLoaderCode) pages (left RWX),
// cleans D-cache / invalidates I-cache, and branches to _start there.
// Offsets: SystemTable->BootServices at 96, BootServices->AllocatePages at 40.
// Everything is PC-relative, so the blob runs wherever it is copied.

    .section .text.boot,"ax"
    .globl efi_entry
    .balign 8
efi_entry:
    b       1f
    .word   0
efi_blob_len:
    .quad   0
1:
    stp     x29, x30, [sp, #-32]!
    mov     x29, sp
    str     xzr, [sp, #16]
    ldr     x9, [x1, #96]
    ldr     x9, [x9, #40]
    ldr     x2, efi_blob_len
    add     x2, x2, #4095
    lsr     x2, x2, #12
    mov     x0, #0
    mov     x1, #1
    add     x3, sp, #16
    blr     x9
    cbnz    x0, 9f
    ldr     x10, [sp, #16]
    adr     x11, efi_entry
    ldr     x12, efi_blob_len
    mov     x13, #0
2:
    cmp     x13, x12
    b.hs    3f
    ldrb    w14, [x11, x13]
    strb    w14, [x10, x13]
    add     x13, x13, #1
    b       2b
3:
    mov     x13, #0
4:
    cmp     x13, x12
    b.hs    5f
    add     x14, x10, x13
    dc      cvau, x14
    add     x13, x13, #64
    b       4b
5:
    dsb     ish
    mov     x13, #0
6:
    cmp     x13, x12
    b.hs    7f
    add     x14, x10, x13
    ic      ivau, x14
    add     x13, x13, #64
    b       6b
7:
    dsb     ish
    isb
    adr     x15, _start
    sub     x15, x15, x11
    add     x15, x10, x15
    br      x15
9:
    b       9b
