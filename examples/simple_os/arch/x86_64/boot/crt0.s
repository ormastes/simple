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
     * PML4[0] -> PDPT     (at pml4 + 0x1000)
     * PDPT[0] -> PD       (at pml4 + 0x2000)
     * PD[0..1023] -> 2 MiB identity pages
     * ------------------------------------------------------------------ */

    /* Zero the page-table area (3 pages = 12 KiB) */
    movl $boot_pml4, %edi
    movl $3072, %ecx          /* 12288 / 4 = 3072 dwords */
    xorl %eax, %eax
    rep stosl

    /* PML4[0] -> PDPT | present | writable */
    movl $boot_pml4, %edi
    movl $boot_pdpt, %eax
    orl  $0x03, %eax           /* P | RW */
    movl %eax, (%edi)

    /* PDPT[0] -> PD | present | writable */
    movl $boot_pdpt, %edi
    movl $boot_pd, %eax
    orl  $0x03, %eax
    movl %eax, (%edi)

    /* Fill PD[0..1023] with 2 MiB identity pages
     * Each entry: addr | PS (bit 7) | RW | P = addr | 0x83 */
    movl $boot_pd, %edi
    movl $0x00000083, %eax     /* 0 MiB | PS | RW | P */
    movl $1024, %ecx
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

    /* Pass multiboot info pointer as first arg (rdi) -- zero-extend ESI */
    movl %esi, %edi

    /* Call Simple compiler entry point */
    call _start

    /* Halt if it returns */
.halt64:
    cli
    hlt
    jmp .halt64

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
 * Page tables -- 4K-aligned, in BSS
 * ================================================================== */
.section .bss
.align 4096
boot_pml4:
    .space 4096
boot_pdpt:
    .space 4096
boot_pd:
    .space 4096
