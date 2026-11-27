/* ARMv7 (Thumb-2) UEFI entry stub for the bare-metal hello image.
 *
 * Linked FIRST (.text.boot) by the Simple linker (elf_arm32_link_raw), so it
 * sits at offset 0 of the flat blob that scripts/check/baremetal-efi-wrap.spl
 * wraps in a PE32 EFI app (machine 0x01c2 ARMTHUMB_MIXED; entry = section
 * start + 1, Thumb). Blob contract shared with the wrapper: offset 0 = short
 * branch, offset 8 = u64 blob length patched by the wrapper.
 *
 * AAVMF32 maps PE sections W^X, so the stub copies the whole blob into
 * BootServices->AllocatePages(AnyPages, EfiLoaderCode) pages, does ARMv7 cache
 * maintenance by MVA, and branches (ARM state, even address) to _start at the
 * same offset in the copy. Everything is PC-relative.
 * UEFI ARM: AAPCS, SystemTable->BootServices at 60, AllocatePages at 32,
 * EFI_PHYSICAL_ADDRESS stays 64 bit (out-param is 8 bytes).
 */
    .syntax unified
    .thumb
    .section .text.boot,"ax"
    .globl efi_entry
    .thumb_func
    .balign 8
efi_entry:
0:  b.n     1f
    .short  0
    .word   0
efi_blob_len:
    .quad   0
1:
    push    {r4-r8, lr}
    sub     sp, sp, #16                 @ sp+0: u64 addr out-param (keeps 8-byte alignment)
    movs    r4, #0
    str     r4, [sp]
    str     r4, [sp, #4]
    ldr     r6, [r1, #60]               @ BootServices
    ldr     r6, [r6, #32]               @ AllocatePages
    adr.w   r5, 0b                      @ blob's current address
    bic     r5, r5, #1
    ldr     r7, [r5, #8]                @ blob length (low word)
    addw    r2, r7, #4095
    lsrs    r2, r2, #12                 @ pages
    movs    r0, #0                      @ AllocateAnyPages
    movs    r1, #1                      @ EfiLoaderCode
    mov     r3, sp
    blx     r6
    cmp     r0, #0
    bne     9f
    ldr     r4, [sp]                    @ r4 = destination
    mov     r0, r4
    mov     r1, r5
    mov     r2, r7
2:  ldrb    r3, [r1], #1
    strb    r3, [r0], #1
    subs    r2, r2, #1
    bne     2b
    mov     r0, r4                      @ clean D by MVA to PoU
    add     r1, r4, r7
3:  mcr     p15, 0, r0, c7, c11, 1
    adds    r0, r0, #32
    cmp     r0, r1
    blo     3b
    dsb
    mov     r0, r4                      @ invalidate I by MVA
4:  mcr     p15, 0, r0, c7, c5, 1
    adds    r0, r0, #32
    cmp     r0, r1
    blo     4b
    movs    r0, #0
    mcr     p15, 0, r0, c7, c5, 6       @ flush branch predictor
    dsb
    isb
    adr.w   r1, 5f
    ldr     r2, [r1]                    @ _start - 5f (link-time, R_ARM_REL32)
    add     r2, r2, r1                  @ _start in the source blob
    subs    r2, r2, r5                  @ offset of _start in the blob
    add     r2, r2, r4                  @ _start in the copy
    bx      r2                          @ even address: ARM state (crt0_arm32)
9:  b       9b
    .balign 4
5:  .word   _start - 5b
