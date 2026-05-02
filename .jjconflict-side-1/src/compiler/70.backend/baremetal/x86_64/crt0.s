/*
 * x86_64 Bare-Metal Startup Code (crt0.s)
 *
 * Minimal bare-metal startup for x86_64 processors.
 * Tested on: QEMU x86_64, SeaBIOS, multiboot2
 *
 * Memory Layout:
 *   0x00100000 - Kernel load address (1MB mark)
 *   0x00200000 - Stack (grows down)
 *   0xB8000    - VGA text mode buffer (80x25)
 *
 * This file provides:
 *   - Multiboot2 header
 *   - 64-bit mode entry point
 *   - Stack setup
 *   - BSS zeroing
 *   - Call to main()
 */

    .code32                      /* Start in 32-bit mode (bootloader requirement) */
    .section .multiboot
    .align 8

/*
 * Multiboot2 Header
 *
 * Required for GRUB2 and other multiboot2-compliant bootloaders.
 * Requests framebuffer and provides load address.
 */
multiboot_header_start:
    .long 0xE85250D6             /* Multiboot2 magic */
    .long 0                      /* Architecture: x86 protected mode */
    .long multiboot_header_end - multiboot_header_start
    .long -(0xE85250D6 + 0 + (multiboot_header_end - multiboot_header_start))

    /* Framebuffer tag (optional) */
    .short 5                     /* Type: framebuffer */
    .short 0                     /* Flags */
    .long 20                     /* Size */
    .long 1024                   /* Width */
    .long 768                    /* Height */
    .long 32                     /* Depth (bits per pixel) */

    /* End tag */
    .short 0                     /* Type */
    .short 0                     /* Flags */
    .long 8                      /* Size */
multiboot_header_end:

/*
 * BSS Section for Boot Stack
 */
    .section .bss
    .align 16
boot_stack_bottom:
    .skip 0x4000                 /* 16KB boot stack */
boot_stack_top:

/*
 * GDT (Global Descriptor Table) for 64-bit Long Mode
 */
    .section .rodata
    .align 16
gdt64:
    .quad 0                      /* Null descriptor */

gdt64_code:
    .word 0                      /* Limit (ignored in 64-bit) */
    .word 0                      /* Base (low) */
    .byte 0                      /* Base (mid) */
    .byte 0b10011010             /* Access: present, ring 0, code, executable */
    .byte 0b10100000             /* Flags: long mode, 4KB granularity */
    .byte 0                      /* Base (high) */

gdt64_data:
    .word 0                      /* Limit (ignored in 64-bit) */
    .word 0                      /* Base (low) */
    .byte 0                      /* Base (mid) */
    .byte 0b10010010             /* Access: present, ring 0, data, writable */
    .byte 0                      /* Flags */
    .byte 0                      /* Base (high) */

gdt64_pointer:
    .word gdt64_pointer - gdt64 - 1   /* Limit */
    .quad gdt64                  /* Base */

/*
 * Entry Point (32-bit Protected Mode)
 *
 * Called by bootloader with:
 *   - Interrupts disabled
 *   - A20 gate enabled
 *   - EBX = multiboot2 info structure address
 *   - EAX = multiboot2 magic value (0x36D76289)
 */
    .section .text
    .global _start
    .type _start, @function
_start:
    /* Set up stack */
    mov $boot_stack_top, %esp
    mov %esp, %ebp

    /* Save multiboot info */
    push %ebx                    /* Multiboot info address */
    push %eax                    /* Multiboot magic */

    /* Check for long mode support */
    call check_long_mode
    test %eax, %eax
    jz .Lno_long_mode

    /* Set up paging for 64-bit mode */
    call setup_page_tables
    call enable_paging

    /* Load GDT */
    lgdt gdt64_pointer

    /* Jump to 64-bit code */
    ljmp $0x08, $start64

.Lno_long_mode:
    /* Print error message to VGA buffer */
    mov $0xB8000, %edi
    mov $0x4F524F45, (%edi)      /* 'E', 'R' with white on red */
    mov $0x4F524F52, 4(%edi)     /* 'R', 'O' with white on red */
    jmp .Lhalt

.Lhalt:
    cli
    hlt
    jmp .Lhalt

/*
 * Check for Long Mode Support
 *
 * Returns 1 in EAX if long mode is supported, 0 otherwise.
 */
check_long_mode:
    /* Check for CPUID support */
    pushfl
    pop %eax
    mov %eax, %ecx
    xor $(1 << 21), %eax
    push %eax
    popfl
    pushfl
    pop %eax
    push %ecx
    popfl
    cmp %eax, %ecx
    je .Lno_cpuid

    /* Check for extended CPUID (0x80000001) */
    mov $0x80000000, %eax
    cpuid
    cmp $0x80000001, %eax
    jb .Lno_long_mode_support

    /* Check for long mode bit (bit 29 of EDX) */
    mov $0x80000001, %eax
    cpuid
    test $(1 << 29), %edx
    jz .Lno_long_mode_support

    mov $1, %eax
    ret

.Lno_cpuid:
.Lno_long_mode_support:
    xor %eax, %eax
    ret

/*
 * Setup Page Tables
 *
 * Identity-maps first 2MB of physical memory.
 * Page table structure:
 *   - PML4: 512GB per entry
 *   - PDPT: 1GB per entry
 *   - PD:   2MB per entry (using huge pages)
 */
    .section .bss
    .align 4096
page_table_l4:
    .skip 4096
page_table_l3:
    .skip 4096
page_table_l2:
    .skip 4096

    .section .text
setup_page_tables:
    /* Clear page tables */
    mov $page_table_l4, %edi
    mov $3, %ecx                 /* 3 pages × 4096 bytes */
    shl $12, %ecx
    xor %eax, %eax
    rep stosb

    /* Set up PML4 (level 4) */
    mov $page_table_l4, %edi
    mov $page_table_l3, %eax
    or $0b11, %eax               /* Present + Writable */
    mov %eax, (%edi)

    /* Set up PDPT (level 3) */
    mov $page_table_l3, %edi
    mov $page_table_l2, %eax
    or $0b11, %eax               /* Present + Writable */
    mov %eax, (%edi)

    /* Set up PD (level 2) with huge pages */
    mov $page_table_l2, %edi
    mov $0, %ecx
.Lpage_loop:
    mov %ecx, %eax
    shl $21, %eax                /* 2MB per entry */
    or $0b10000011, %eax         /* Present + Writable + Huge page */
    mov %eax, (%edi)
    add $8, %edi
    inc %ecx
    cmp $512, %ecx               /* Map 512 × 2MB = 1GB */
    jne .Lpage_loop

    ret

/*
 * Enable Paging
 *
 * Enables PAE (Physical Address Extension) and long mode.
 */
enable_paging:
    /* Load PML4 into CR3 */
    mov $page_table_l4, %eax
    mov %eax, %cr3

    /* Enable PAE (bit 5 of CR4) */
    mov %cr4, %eax
    or $(1 << 5), %eax
    mov %eax, %cr4

    /* Enable long mode (bit 8 of EFER MSR) */
    mov $0xC0000080, %ecx        /* EFER MSR */
    rdmsr
    or $(1 << 8), %eax           /* LME bit */
    wrmsr

    /* Enable paging (bit 31 of CR0) */
    mov %cr0, %eax
    or $(1 << 31), %eax          /* PG bit */
    mov %eax, %cr0

    ret

/*
 * 64-bit Entry Point
 */
    .code64
    .section .text
start64:
    /* Load data segment */
    mov $0x10, %ax               /* GDT data segment */
    mov %ax, %ds
    mov %ax, %es
    mov %ax, %fs
    mov %ax, %gs
    mov %ax, %ss

    /* Set up 64-bit stack */
    mov $boot_stack_top, %rsp

    /* Zero BSS section */
    mov $__bss_start, %rdi
    mov $__bss_end, %rcx
    sub %rdi, %rcx
    xor %rax, %rax
    rep stosb

    /* Call C/Simple runtime initialization */
    call __spl_start_bare        /* Defined in crt_baremetal.c */

    /* If main returns, loop forever */
.Lhalt64:
    cli
    hlt
    jmp .Lhalt64

    .size _start, . - _start
