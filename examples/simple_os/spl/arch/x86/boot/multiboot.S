# x86 Multiboot v1 Header + Entry Point
#
# Provides the Multiboot header so GRUB/QEMU can load the kernel,
# sets up an initial stack, zeroes BSS, and calls kernel_main.
#
# Multiboot specification v1:
#   Magic:    0x1BADB002
#   Flags:    bit 0 = align modules on 4KB, bit 1 = provide memory map
#   Checksum: -(magic + flags)

.set MULTIBOOT_MAGIC,    0x1BADB002
.set MULTIBOOT_FLAGS,    0x00000003    # align + meminfo
.set MULTIBOOT_CHECKSUM, -(MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)

# ---------- Multiboot header ----------
# Must be within the first 8KB of the binary and 4-byte aligned.

.section .multiboot, "a"
.align 4
multiboot_header:
    .long MULTIBOOT_MAGIC
    .long MULTIBOOT_FLAGS
    .long MULTIBOOT_CHECKSUM

# ---------- Initial kernel stack ----------
# 16 KB stack, page-aligned.

.section .stack, "aw", @nobits
.align 4096
.global stack_bottom
stack_bottom:
    .skip 16384               # 16 KB
.global stack_top
stack_top:

# ---------- Entry point ----------
# The bootloader jumps here with:
#   eax = multiboot magic (0x2BADB002)
#   ebx = pointer to multiboot info structure

.section .text
.code32

.global _start
.type _start, @function
_start:
    # Disable interrupts until IDT is set up
    cli

    # Set up the kernel stack
    mov $stack_top, %esp
    mov %esp, %ebp

    # Save multiboot parameters
    push %eax                  # multiboot magic
    push %ebx                  # multiboot info pointer

    # Zero out BSS section
    # _bss_start and _bss_end are provided by the linker script
    .extern _bss_start
    .extern _bss_end
    mov $_bss_start, %edi
    mov $_bss_end, %ecx
    sub %edi, %ecx            # ecx = bss size in bytes
    shr $2, %ecx              # ecx = bss size in dwords
    xor %eax, %eax            # eax = 0
    cld
    rep stosl                  # zero dwords

    # Restore multiboot parameters and call kernel_main
    # kernel_main(multiboot_magic: u32, multiboot_info: u32)
    pop %ebx                  # multiboot info pointer
    pop %eax                  # multiboot magic

    push %ebx                 # arg1: multiboot info
    push %eax                 # arg0: multiboot magic

    .extern kernel_main
    call kernel_main

    # Clean up stack (in case kernel_main returns)
    add $8, %esp

    # Halt forever - kernel_main should never return
.global _halt
_halt:
    cli
.Lhalt:
    hlt
    jmp .Lhalt

.size _start, . - _start
