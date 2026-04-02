/*
 * crt0.s -- x86_64 Multiboot1 entry point
 *
 * Provides the Multiboot1 header (with framebuffer request) and the
 * _start symbol.  The header lives in .text.entry so the linker script
 * places it at the very beginning of the .text section, guaranteeing it
 * appears within the first 8 KiB of the ELF -- a Multiboot requirement.
 *
 * Flow:  QEMU/GRUB -> _start -> __simple_main (compiled Simple code)
 *
 * Multiboot1 spec: flags bit 2 (0x4) enables the video-mode fields.
 * We request 1024x768x32 linear framebuffer.
 */

.section .text.entry, "ax"
.code32
.align 4

/* ---- Multiboot1 header ------------------------------------------------ */
#define MB_MAGIC   0x1BADB002
#define MB_FLAGS   0x00000007   /* bits: 0=page-align, 1=meminfo, 2=video */

/* checksum: -(magic + flags), truncated to 32 bits */
#define MB_CHECKSUM  (-(MB_MAGIC + MB_FLAGS))

.global _multiboot_header
_multiboot_header:
    .long MB_MAGIC              /* magic */
    .long MB_FLAGS              /* flags */
    .long MB_CHECKSUM           /* checksum */

    /* --- address fields (unused when bit 16 is clear) --- */
    .long 0                     /* header_addr */
    .long 0                     /* load_addr   */
    .long 0                     /* load_end_addr */
    .long 0                     /* bss_end_addr  */
    .long 0                     /* entry_addr    */

    /* --- video mode fields (flags bit 2) --- */
    .long 0                     /* mode_type  0 = linear framebuffer */
    .long 1024                  /* width */
    .long 768                   /* height */
    .long 32                    /* depth (bpp) */

/* ---- Entry point ------------------------------------------------------ */
.global _start
_start:
    /* EAX = 0x2BADB002 (multiboot magic), EBX = multiboot info pointer */

    /* Set up a small stack (defined in linker script) */
    movl $_stack_top, %esp

    /* Save multiboot info pointer for later use */
    pushl $0        /* align: high 32 bits (zero for 32-bit ptr) */
    pushl %ebx      /* multiboot info struct pointer */
    pushl $0        /* align: high 32 bits */
    pushl %eax      /* multiboot magic */

    /* Clear BSS */
    movl $__bss_start, %edi
    movl $__bss_end, %ecx
    subl %edi, %ecx
    shrl $2, %ecx
    xorl %eax, %eax
    rep stosl

    /* Call the Simple runtime entry point */
    call __simple_main

    /* If __simple_main returns, halt */
.halt_loop:
    cli
    hlt
    jmp .halt_loop
