# x86 Bare-Metal Hello World
# Boots via Multiboot, writes to VGA buffer, exits via ISA debug-exit

.section .multiboot
.align 4
multiboot_header:
    .long 0x1BADB002                    # Magic number
    .long 0x00000000                    # Flags
    .long -(0x1BADB002 + 0x00000000)    # Checksum

.section .text
.global _start
_start:
    # Write "Hello, x86!" to VGA buffer at 0xB8000
    movl $0xB8000, %edi               # VGA buffer address
    movl $hello_msg, %esi             # Message address
    movl $12, %ecx                    # Message length

write_loop:
    lodsb                             # Load byte from DS:ESI into AL
    movb $0x0F, %ah                   # White on black attribute
    stosw                             # Store AX to ES:EDI
    loop write_loop

    # Exit via ISA debug-exit device (QEMU)
    # Write 0 to port 0xf4 to signal success
    movl $0, %eax
    outb %al, $0xf4

    # Halt forever (in case debug-exit doesn't work)
halt:
    cli
    hlt
    jmp halt

.section .rodata
hello_msg:
    .ascii "Hello, x86!"

.section .bss
.align 16
stack_bottom:
    .skip 4096                        # 4 KB stack
stack_top:
