/*
 * crt0.s -- x86_64 Multiboot1 header + 32→64 bit mode switch
 *
 * Provides:
 *   1. Multiboot1 header (with framebuffer request) in .text.entry
 *   2. _start entry: sets up identity-mapped page tables, enables
 *      long mode (64-bit), loads a 64-bit GDT, jumps to spl_start
 *
 * Multiboot1 drops us in 32-bit protected mode with:
 *   EAX = 0x2BADB002 (magic)   EBX = multiboot info pointer
 *   Paging disabled, A20 enabled, GDT loaded (flat 32-bit)
 *
 * We identity-map the first 2 GiB with 2 MiB pages so the kernel
 * (loaded at 1 MiB) and all MMIO regions are accessible.
 */

/* ==================================================================
 * Multiboot1 header -- must be in first 8 KiB, 4-byte aligned
 * ================================================================== */
.section .text.entry, "ax"
.code32
.align 4

.set MB_MAGIC, 0x1BADB002
.set MB_FLAGS, 0x00000003

.global _multiboot_header
_multiboot_header:
    .long MB_MAGIC
    .long MB_FLAGS
    .long 0xE4524FFB          /* checksum: -(magic + flags) & 0xFFFFFFFF */

/* ==================================================================
 * 32-bit entry point
 * ================================================================== */
.global _entry32
_entry32:
    /* Disable interrupts */
    cli

    /* Save multiboot info (EBX) on the stack later -- preserve in ESI */
    movl %ebx, %esi

    /* Set up a temporary 32-bit stack */
    movl $_stack_top, %esp

    /* Clear BSS */
    movl $__bss_start, %edi
    movl $__bss_end, %ecx
    subl %edi, %ecx
    shrl $2, %ecx
    xorl %eax, %eax
    rep stosl

    /* ------------------------------------------------------------------
     * Build identity-mapped page tables (2 MiB pages, first 2 GiB)
     *
     * PML4[0] -> PDPT
     * PDPT[0..3] -> PD[0..3]  (4 GiB identity map)
     * PD[0..2047] -> 2 MiB identity pages
     * Maps full 4 GiB to cover VGA framebuffer at 0xFD000000.
     * ------------------------------------------------------------------ */

    /* Zero the page-table area (PML4 4K + PDPT 4K + PD 16K = 24 KiB) */
    movl $boot_pml4, %edi
    movl $6144, %ecx          /* 24576 / 4 = 6144 dwords */
    xorl %eax, %eax
    rep stosl

    /* PML4[0] -> PDPT | present | writable */
    movl $boot_pml4, %edi
    movl $boot_pdpt, %eax
    orl  $0x03, %eax           /* P | RW */
    movl %eax, (%edi)

    /* PDPT[0] -> PD+0x0000 (0-1 GiB) */
    movl $boot_pdpt, %edi
    movl $boot_pd, %eax
    orl  $0x03, %eax
    movl %eax, (%edi)

    /* PDPT[1] -> PD+0x1000 (1-2 GiB) */
    movl $boot_pd, %eax
    addl $0x1000, %eax
    orl  $0x03, %eax
    movl %eax, 8(%edi)

    /* PDPT[2] -> PD+0x2000 (2-3 GiB) */
    movl $boot_pd, %eax
    addl $0x2000, %eax
    orl  $0x03, %eax
    movl %eax, 16(%edi)

    /* PDPT[3] -> PD+0x3000 (3-4 GiB) */
    movl $boot_pd, %eax
    addl $0x3000, %eax
    orl  $0x03, %eax
    movl %eax, 24(%edi)

    /* Fill PD[0..2047] with 2 MiB identity pages (4 GiB total)
     * Each entry: addr | PS (bit 7) | RW | P = addr | 0x83 */
    movl $boot_pd, %edi
    movl $0x00000083, %eax     /* 0 MiB | PS | RW | P */
    movl $2048, %ecx
.fill_pd:
    movl %eax, (%edi)
    movl $0, 4(%edi)           /* high 32 bits = 0 */
    addl $0x200000, %eax       /* next 2 MiB */
    addl $8, %edi
    decl %ecx
    jnz .fill_pd

    /* ------------------------------------------------------------------
     * Enable long mode
     * ------------------------------------------------------------------ */

    /* Load PML4 into CR3 */
    movl $boot_pml4, %eax
    movl %eax, %cr3

    /* Enable PAE (CR4.PAE = bit 5) */
    movl %cr4, %eax
    orl  $0x20, %eax
    movl %eax, %cr4

    /* Set LME (Long Mode Enable) in IA32_EFER MSR (0xC0000080) bit 8 */
    movl $0xC0000080, %ecx
    rdmsr
    orl  $0x100, %eax
    wrmsr

    /* Enable paging (CR0.PG = bit 31) + write protect (CR0.WP = bit 16) */
    movl %cr0, %eax
    orl  $0x80010000, %eax
    movl %eax, %cr0

    /* Now in 32-bit compatibility mode (long mode but CS is still 32-bit).
     * Load 64-bit GDT and far-jump to 64-bit code segment. */
    lgdt (gdt64_ptr)
    ljmp $0x08, $long_mode_entry

/* ==================================================================
 * 64-bit code
 * ================================================================== */
.code64
long_mode_entry:
    /* Reload data segments with 64-bit data selector */
    movw $0x10, %ax
    movw %ax, %ds
    movw %ax, %es
    movw %ax, %fs
    movw %ax, %gs
    movw %ax, %ss

    /* Set up 64-bit stack */
    movq $_stack_top, %rsp

    /* Install minimal IDT — catches faults from stubbed function calls.
     * All 256 vectors point to _fault_handler which returns 0 in RAX.
     */
    leaq _idt(%rip), %rdi
    leaq _fault_handler(%rip), %rsi
    movl $256, %ecx
.fill_idt:
    movq %rsi, %rax
    movw %ax, (%rdi)              /* offset 15:0  */
    movw $0x08, 2(%rdi)           /* selector: code64 */
    movb $0, 4(%rdi)              /* IST = 0 */
    movb $0x8E, 5(%rdi)           /* type: interrupt gate, DPL=0, present */
    shrq $16, %rax
    movw %ax, 6(%rdi)             /* offset 31:16 */
    shrq $16, %rax
    movl %eax, 8(%rdi)            /* offset 63:32 */
    movl $0, 12(%rdi)             /* reserved */
    addq $16, %rdi
    decl %ecx
    jnz .fill_idt

    leaq _idt(%rip), %rax
    movw $4095, _idt_ptr(%rip)    /* limit: 256*16-1 */
    movq %rax, _idt_ptr+2(%rip)   /* base */
    lidt _idt_ptr(%rip)

    /* Pass multiboot info pointer as first arg (rdi) -- zero-extend ESI */
    movl %esi, %edi

    /* Call Simple compiler entry point */
    call _start

    /* Halt if it returns */
.halt64:
    cli
    hlt
    jmp .halt64

/* Minimal fault handler: returns 0 (NIL_VALUE) in RAX and resumes.
 * For error-code exceptions (#GP, #PF, etc.) we must pop the error code.
 * Strategy: pop error code if present (detected via vector number),
 * set RAX=0, increment RIP past the faulting CALL (assume 2-byte callq *reg),
 * then iretq.
 *
 * NOTE: This is a demo-quality handler. Production code needs per-vector
 * entry points that know whether an error code is pushed.
 */
.align 16
_fault_handler:
    /* Save scratch registers */
    pushq %rcx
    pushq %rdx

    /* Check if this is a fault with error code by looking at the stack.
     * For interrupts without error code, stack is: [RIP, CS, RFLAGS, RSP, SS]
     * For interrupts with error code: [errcode, RIP, CS, RFLAGS, RSP, SS]
     * We detect by checking if the value at +24(%rsp) looks like a valid CS (0x08).
     * +0: saved rdx, +8: saved rcx, +16: return-RIP-or-errcode
     * If +24(%rsp) == 0x08, then +16 is RIP (no error code).
     * If +32(%rsp) == 0x08, then +16 is error code, +24 is RIP.
     */
    cmpq $0x08, 24(%rsp)
    je .no_error_code
    /* Has error code: remove it by shifting RIP down */
    movq 24(%rsp), %rcx           /* RIP */
    addq $2, %rcx                 /* skip past callq *reg (2 bytes: FF Dx) */
    movq %rcx, 24(%rsp)           /* write adjusted RIP back */
    /* Remove error code: shift the saved regs + RIP */
    movq 8(%rsp), %rcx            /* saved rcx */
    movq 0(%rsp), %rdx            /* saved rdx */
    addq $8, %rsp                 /* pop error code slot */
    movq %rdx, 0(%rsp)
    movq %rcx, 8(%rsp)
    jmp .fault_return
.no_error_code:
    /* RIP is at +16(%rsp), advance past faulting instruction */
    addq $2, 16(%rsp)
.fault_return:
    xorq %rax, %rax               /* return 0 (NIL_VALUE) */
    popq %rdx
    popq %rcx
    iretq

/* ==================================================================
 * 64-bit GDT (minimal: null, code64, data64)
 * ================================================================== */
.section .rodata
.align 16
gdt64:
    .quad 0                    /* 0x00: null descriptor */

    /* 0x08: 64-bit code segment */
    .word 0xFFFF               /* limit low */
    .word 0x0000               /* base low */
    .byte 0x00                 /* base mid */
    .byte 0x9A                 /* access: present, ring 0, code, exec/read */
    .byte 0xAF                 /* flags: 4K granularity, long mode; limit hi */
    .byte 0x00                 /* base high */

    /* 0x10: 64-bit data segment */
    .word 0xFFFF
    .word 0x0000
    .byte 0x00
    .byte 0x92                 /* access: present, ring 0, data, read/write */
    .byte 0xCF                 /* flags: 4K granularity, 32-bit (ignored in long mode) */
    .byte 0x00

gdt64_end:

gdt64_ptr:
    .word gdt64_end - gdt64 - 1  /* limit */
    .long gdt64                   /* base (32-bit address, fine for < 4 GiB) */

/* ==================================================================
 * IDT — 256 entries * 16 bytes = 4 KiB, in BSS
 * ================================================================== */
.section .bss
.align 4096
_idt:
    .space 4096

.section .data
.align 16
_idt_ptr:
    .word 0        /* limit (filled at runtime) */
    .quad 0        /* base  (filled at runtime) */

/* ==================================================================
 * Page tables -- 4K-aligned, in BSS
 * ================================================================== */
.section .bss
.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 16384   /* 2048 entries * 8 bytes = 16 KiB for 4 GiB identity map */
