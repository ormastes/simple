/*
 * multiboot.S — Multiboot1 entry + long mode trampoline for x86_64
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * Boot flow:
 *   1. Multiboot bootloader loads us in 32-bit protected mode
 *   2. We set up identity-mapped PML4 for the first 2 MB (using 2 MB pages)
 *   3. Enable PAE (CR4), load PML4 (CR3), set EFER.LME, enable paging (CR0)
 *   4. Far jump to 64-bit code segment
 *   5. Set up 64-bit stack and call kernel_main
 */

/* ── Multiboot constants ───────────────────────────────────────────── */

.set MULTIBOOT_MAGIC,   0x1BADB002
.set MULTIBOOT_FLAGS,   0x00000003      /* Align modules + memory map */
.set MULTIBOOT_CHECKSUM, -(MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)

/* ── Stack size ────────────────────────────────────────────────────── */

.set STACK_SIZE,        16384           /* 16 KB */

/* ── EFER MSR ──────────────────────────────────────────────────────── */

.set MSR_EFER,          0xC0000080
.set EFER_LME,          (1 << 8)       /* Long Mode Enable */
.set EFER_SCE,          (1 << 0)       /* SYSCALL Enable   */

/* ── CR4 bits ──────────────────────────────────────────────────────── */

.set CR4_PAE,           (1 << 5)       /* Physical Address Extension */

/* ── CR0 bits ──────────────────────────────────────────────────────── */

.set CR0_PG,            (1 << 31)      /* Paging Enable */
.set CR0_WP,            (1 << 16)      /* Write Protect */

/* ══════════════════════════════════════════════════════════════════════
 * Multiboot header — must be in first 8 KB of the binary
 * ══════════════════════════════════════════════════════════════════════ */

.section .multiboot, "a"
.align 4
    .long MULTIBOOT_MAGIC
    .long MULTIBOOT_FLAGS
    .long MULTIBOOT_CHECKSUM

/* ══════════════════════════════════════════════════════════════════════
 * 32-bit entry point (from bootloader)
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.code32
.global _start
.type _start, @function

_start:
    /* Disable interrupts */
    cli

    /* Save Multiboot info pointer (EBX) before anything clobbers it */
    movl    %ebx, %esi

    /* Set up a temporary 32-bit stack */
    movl    $stack_top, %esp

    /* ── Zero the BSS section ─────────────────────────────────── */
    movl    $_bss_start, %edi
    movl    $_bss_end, %ecx
    subl    %edi, %ecx
    shrl    $2, %ecx                /* count in 32-bit words */
    xorl    %eax, %eax
    rep stosl

    /* ── Load the boot GDT ────────────────────────────────────── */
    lgdt    boot_gdt_ptr

    /* ── Set up page tables for long mode ─────────────────────── */

    /* PML4[0] -> PDPT */
    movl    $boot_pdpt, %eax
    orl     $0x03, %eax             /* Present + Writable */
    movl    %eax, boot_pml4

    /* PDPT[0] -> PD */
    movl    $boot_pd, %eax
    orl     $0x03, %eax             /* Present + Writable */
    movl    %eax, boot_pdpt

    /* PD[0] -> 2MB huge page at physical 0x000000 */
    movl    $0x00000083, boot_pd    /* Present + Writable + PS (2MB page) */

    /* PD[1] -> 2MB huge page at physical 0x200000 (for kernel at 1MB) */
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
    /* We are now in 32-bit compatibility mode within long mode.
     * A far jump with the 64-bit code selector activates 64-bit mode. */
    ljmp    $0x08, $long_mode_entry

/* ══════════════════════════════════════════════════════════════════════
 * 64-bit entry point
 * ══════════════════════════════════════════════════════════════════════ */

.code64

long_mode_entry:
    /* Reload data segments with 64-bit data selector */
    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs
    movw    %ax, %ss

    /* Set up the 64-bit kernel stack */
    movabs  $stack_top, %rsp

    /* Zero upper 32 bits of multiboot info pointer */
    movl    %esi, %edi              /* RDI = first argument (System V AMD64 ABI) */

    /* Call the 64-bit kernel entry point */
    call    kernel_main

    /* If kernel_main returns, halt the CPU */
.halt_loop:
    cli
    hlt
    jmp     .halt_loop

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * Boot GDT — minimal 64-bit GDT used during the 32→64 transition.
 * The real GDT is loaded later by gdt_init() in C code.
 *
 * Layout:
 *   0x00 — Null descriptor
 *   0x08 — 64-bit Code (L=1, D=0, P=1, S=1, Type=Execute/Read)
 *   0x10 — 64-bit Data (P=1, S=1, Type=Read/Write)
 * ══════════════════════════════════════════════════════════════════════ */

.section .rodata, "a"
.align 16

boot_gdt:
    /* 0x00: Null descriptor */
    .quad   0x0000000000000000

    /* 0x08: 64-bit Kernel Code — base=0 limit=0 (ignored in long mode)
     *   Access: P(1) DPL(00) S(1) Type(1010) = 0x9A
     *   Flags:  G(1) D(0) L(1) AVL(0) Limit[19:16]=0 → 0xA0
     *   Encoded: 0x00AF9A000000FFFF */
    .quad   0x00AF9A000000FFFF

    /* 0x10: 64-bit Kernel Data — base=0 limit=0 (ignored in long mode)
     *   Access: P(1) DPL(00) S(1) Type(0010) = 0x92
     *   Flags:  G(1) D(0) L(0) AVL(0) Limit[19:16]=0 → 0xC0
     *   Encoded: 0x00CF92000000FFFF */
    .quad   0x00CF92000000FFFF
boot_gdt_end:

boot_gdt_ptr:
    .word   boot_gdt_end - boot_gdt - 1     /* limit */
    .long   boot_gdt                         /* base (32-bit address) */

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Boot page tables and stack
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", @nobits

/* Page-aligned boot page tables (4 KB each) */
.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 4096

/* Kernel stack */
.align 16
stack_bottom:
    .space STACK_SIZE
stack_top:
