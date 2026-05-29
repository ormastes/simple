# x86_64 Bare-Metal Hello World
# Boots via Multiboot2, writes to VGA buffer, exits via ISA debug-exit

.section .multiboot2
.align 8
multiboot2_header:
    .long 0xE85250D6                    # Magic number
    .long 0                             # Architecture (i386)
    .long multiboot2_end - multiboot2_header  # Header length
    .long -(0xE85250D6 + 0 + (multiboot2_end - multiboot2_header))  # Checksum

    # End tag
    .word 0                             # Type
    .word 0                             # Flags
    .long 8                             # Size
multiboot2_end:

.section .text
.code64
.global _start
_start:
    # Set up long mode (assume bootloader already did this)
    # Write "Hello, x86_64!" to VGA buffer at 0xB8000
    movq $0xB8000, %rdi               # VGA buffer address
    leaq hello_msg(%rip), %rsi        # Message address (RIP-relative)
    movl $14, %ecx                    # Message length

write_loop:
    lodsb                             # Load byte from DS:RSI into AL
    movb $0x0F, %ah                   # White on black attribute
    stosw                             # Store AX to ES:RDI
    loop write_loop

    # Exit via ISA debug-exit device (QEMU)
    movl $0, %eax
    outb %al, $0xf4

    # Halt forever
halt:
    cli
    hlt
    jmp halt

.section .rodata
hello_msg:
    .ascii "Hello, x86_64!"

.section .bss
.align 16
stack_bottom:
    .skip 8192                        # 8 KB stack for 64-bit
stack_top:
