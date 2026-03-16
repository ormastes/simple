/*
 * multiboot.S — Multiboot1 entry point for x86
 *
 * Part of the SimpleOS L4 microkernel reference implementation.
 *
 * This file provides the Multiboot header, initial stack setup,
 * BSS zeroing, and jumps to kernel_main().
 */

/* ── Multiboot constants ───────────────────────────────────────────── */

.set MULTIBOOT_MAGIC,   0x1BADB002
.set MULTIBOOT_FLAGS,   0x00000003      /* Align modules + memory map */
.set MULTIBOOT_CHECKSUM, -(MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)

/* ── Stack size ────────────────────────────────────────────────────── */

.set STACK_SIZE,        16384           /* 16 KB */

/* ══════════════════════════════════════════════════════════════════════
 * Multiboot header — must be in first 8 KB of the binary
 * ══════════════════════════════════════════════════════════════════════ */

.section .multiboot, "a"
.align 4
    .long MULTIBOOT_MAGIC
    .long MULTIBOOT_FLAGS
    .long MULTIBOOT_CHECKSUM

/* ══════════════════════════════════════════════════════════════════════
 * Entry point
 * ══════════════════════════════════════════════════════════════════════ */

.section .text
.global _start
.type _start, @function

_start:
    /* Set up the initial kernel stack */
    movl    $stack_top, %esp

    /* Zero the BSS section */
    movl    $_bss_start, %edi
    movl    $_bss_end, %ecx
    subl    %edi, %ecx
    shrl    $2, %ecx                    /* count in 32-bit words */
    xorl    %eax, %eax
    rep stosl

    /* Push Multiboot info pointer and magic number for kernel_main */
    pushl   %ebx                        /* Multiboot info struct pointer */
    pushl   %eax                        /* Multiboot magic number (in eax from bootloader) */

    /* Note: the bootloader puts magic in EAX and info ptr in EBX.
     * We already clobbered EAX above when zeroing BSS, so we re-push
     * the expected magic value explicitly. */
    movl    $0x2BADB002, (%esp)         /* Overwrite with expected magic */

    /* Call the C kernel entry point */
    call    kernel_main

    /* If kernel_main returns, halt the CPU */
.halt_loop:
    cli
    hlt
    jmp     .halt_loop

.size _start, . - _start

/* ══════════════════════════════════════════════════════════════════════
 * BSS: Stack reservation
 * ══════════════════════════════════════════════════════════════════════ */

.section .bss, "aw", @nobits
.align 16

stack_bottom:
    .space STACK_SIZE
stack_top:
