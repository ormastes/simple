/*
 * multiboot.S — Multiboot1 entry + long mode trampoline for x86_64
 *
 * Part of the SimpleOS L4 microkernel (Simple language build).
 *
 * Boot flow:
 *   1. Multiboot bootloader loads us in 32-bit protected mode
 *   2. Set up identity-mapped PML4 for the first 4 MB (using 2 MB pages)
 *   3. Enable PAE (CR4), load PML4 (CR3), set EFER.LME, enable paging (CR0)
 *   4. Far jump to 64-bit code segment
 *   5. Set up 64-bit stack and call kernel_main
 */

/* ── Multiboot constants ───────────────────────────────────────────── */

.set MULTIBOOT_MAGIC,   0x1BADB002
.set MULTIBOOT_FLAGS,   0x00000003
.set MULTIBOOT_CHECKSUM, -(MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)

.set STACK_SIZE,        16384

/* ── MSR / CR constants ────────────────────────────────────────────── */

.set MSR_EFER,          0xC0000080
.set EFER_LME,          (1 << 8)
.set CR4_PAE,           (1 << 5)
.set CR0_PG,            (1 << 31)
.set CR0_WP,            (1 << 16)

/* ══════════════════════════════════════════════════════════════════════
 * Multiboot header
 * ══════════════════════════════════════════════════════════════════════ */

.section .multiboot, "a"
.align 4
    .long MULTIBOOT_MAGIC
    .long MULTIBOOT_FLAGS
    .long MULTIBOOT_CHECKSUM

/* ══════════════════════════════════════════════════════════════════════
 * 32-bit entry point
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.code32
.global _start
.type _start, @function

_start:
    cli
    movl    %ebx, %esi              /* Save multiboot info pointer */
    movl    $stack_top, %esp

    /* Zero BSS */
    movl    $_bss_start, %edi
    movl    $_bss_end, %ecx
    subl    %edi, %ecx
    shrl    $2, %ecx
    xorl    %eax, %eax
    rep stosl

    /* Set up page tables: PML4 -> PDPT -> PD with 2MB pages */
    movl    $boot_pdpt, %eax
    orl     $0x03, %eax
    movl    %eax, boot_pml4

    movl    $boot_pd, %eax
    orl     $0x03, %eax
    movl    %eax, boot_pdpt

    movl    $0x00000083, boot_pd        /* 0-2MB: Present+Writable+PS */
    movl    $0x00200083, boot_pd + 8    /* 2-4MB: Present+Writable+PS */

    /* Enable PAE */
    movl    %cr4, %eax
    orl     $CR4_PAE, %eax
    movl    %eax, %cr4

    /* Load PML4 */
    movl    $boot_pml4, %eax
    movl    %eax, %cr3

    /* Enable Long Mode (EFER.LME) */
    movl    $MSR_EFER, %ecx
    rdmsr
    orl     $EFER_LME, %eax
    wrmsr

    /* Enable paging + write protect */
    movl    %cr0, %eax
    orl     $(CR0_PG | CR0_WP), %eax
    movl    %eax, %cr0

    /* Far jump to 64-bit code */
    ljmp    $0x08, $long_mode_entry

/* ══════════════════════════════════════════════════════════════════════
 * 64-bit entry
 * ══════════════════════════════════════════════════════════════════════ */

.code64

long_mode_entry:
    movw    $0x10, %ax
    movw    %ax, %ds
    movw    %ax, %es
    movw    %ax, %fs
    movw    %ax, %gs
    movw    %ax, %ss

    movabs  $stack_top, %rsp

    /* RDI = multiboot info (first arg, System V ABI) */
    movl    %esi, %edi

    call    kernel_main

.halt_loop:
    cli
    hlt
    jmp     .halt_loop

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * BSS: page tables and stack
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", @nobits

.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 4096

.align 16
stack_bottom:
    .space STACK_SIZE
stack_top:
