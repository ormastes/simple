/*
 * boot_wrapper.S — 32-bit Multiboot1 boot stub for x86_64 kernel
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * This file is compiled as a PURE 32-BIT object and linked into an
 * ELF32 binary.  It provides:
 *   1. The Multiboot1 header (so QEMU -kernel can load us)
 *   2. A 32-bit _start that sets up identity paging, enables long mode
 *   3. Embeds the 64-bit kernel payload via .incbin
 *   4. Jumps to _start64 inside the embedded payload
 *
 * Memory layout after loading at 0x00100000:
 *   0x100000 .. 0x100FFF  — This boot wrapper (multiboot hdr + trampoline)
 *   0x101000 .. end       — Embedded 64-bit kernel payload (kernel64.bin)
 *
 * The 64-bit payload is linked at 0x101000, so addresses match after loading.
 */

/* ── Multiboot constants ───────────────────────────────────────────── */

.set MULTIBOOT_MAGIC,    0x1BADB002
.set MULTIBOOT_FLAGS,    0x00000003       /* Align modules + memory map */
.set MULTIBOOT_CHECKSUM, -(MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)

/* ── EFER MSR ──────────────────────────────────────────────────────── */

.set MSR_EFER,           0xC0000080
.set EFER_LME,           (1 << 8)        /* Long Mode Enable */

/* ── CR4 / CR0 bits ────────────────────────────────────────────────── */

.set CR4_PAE,            (1 << 5)
.set CR0_PG,             (1 << 31)
.set CR0_WP,             (1 << 16)

/* ══════════════════════════════════════════════════════════════════════
 * Multiboot header — must appear in the first 8 KB of the ELF
 * ══════════════════════════════════════════════════════════════════════ */

.section .multiboot, "a"
.align 4
    .long MULTIBOOT_MAGIC
    .long MULTIBOOT_FLAGS
    .long MULTIBOOT_CHECKSUM

/* ══════════════════════════════════════════════════════════════════════
 * 32-bit entry point — Multiboot bootloader jumps here
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.code32
.global _start
.type _start, @function

_start:
    cli

    /* Use a temporary stack in low memory (below kernel) */
    movl    $0x7C00, %esp

    /* ── Load the boot GDT ────────────────────────────────────── */
    lgdt    boot_gdt_ptr

    /* ── Zero the boot page tables ────────────────────────────── */
    movl    $boot_pml4, %edi
    movl    $(4096 * 3 / 4), %ecx   /* 3 page tables, 4 bytes each */
    xorl    %eax, %eax
    rep stosl

    /* ── Set up page tables for long mode ─────────────────────── */

    /* PML4[0] -> PDPT */
    movl    $boot_pdpt, %eax
    orl     $0x03, %eax             /* Present + Writable */
    movl    %eax, boot_pml4

    /* PDPT[0] -> PD */
    movl    $boot_pd, %eax
    orl     $0x03, %eax
    movl    %eax, boot_pdpt

    /* PD[0] -> 2 MB huge page at physical 0x000000 */
    movl    $0x00000083, boot_pd        /* Present + Writable + PS */

    /* PD[1] -> 2 MB huge page at physical 0x200000 */
    movl    $0x00200083, boot_pd + 8

    /* ── Enable PAE in CR4 ───────────────────────────────────── */
    movl    %cr4, %eax
    orl     $CR4_PAE, %eax
    movl    %eax, %cr4

    /* ── Load PML4 into CR3 ──────────────────────────────────── */
    movl    $boot_pml4, %eax
    movl    %eax, %cr3

    /* ── Set EFER.LME (Long Mode Enable) ─────────────────────── */
    movl    $MSR_EFER, %ecx
    rdmsr
    orl     $EFER_LME, %eax
    wrmsr

    /* ── Enable paging + write protect in CR0 ────────────────── */
    movl    %cr0, %eax
    orl     $(CR0_PG | CR0_WP), %eax
    movl    %eax, %cr0

    /* ── Far jump to 64-bit code ─────────────────────────────── */
    ljmp    $0x08, $trampoline64

/* ── Brief 64-bit trampoline (still in wrapper) ──────────────────── */

.code64
trampoline64:
    /* Jump to _start64 in the embedded 64-bit kernel payload.
     * _start64 is at virtual address 0x101000 (the start of .text
     * in kernel64.elf, which is the first byte of kernel64.bin). */
    movabs  $0x00101000, %rax
    jmp     *%rax

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * Boot GDT — minimal GDT for the 32→64 transition
 * ══════════════════════════════════════════════════════════════════════ */

.section .rodata, "a"
.align 16

boot_gdt:
    .quad   0x0000000000000000          /* 0x00: Null */
    .quad   0x00AF9A000000FFFF          /* 0x08: 64-bit Code (L=1,D=0) */
    .quad   0x00CF92000000FFFF          /* 0x10: 64-bit Data */
boot_gdt_end:

boot_gdt_ptr:
    .word   boot_gdt_end - boot_gdt - 1
    .long   boot_gdt

/* ══════════════════════════════════════════════════════════════════════
 * Embedded 64-bit kernel payload
 *
 * This must be placed at virtual address 0x101000 (1 MB + 4 KB)
 * because kernel64.elf is linked at that address.
 * ══════════════════════════════════════════════════════════════════════ */

.section .payload, "ax"
.global _kernel64_payload
_kernel64_payload:
    .incbin "build/x86_64/kernel64.bin"

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Boot page tables (used only during 32→64 transition)
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", @nobits
.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 4096
