# R_386_GOT32X with no base register (ModRM mod=00 rm=101): absolute G + A.
    .text
    .globl _start
_start:
    movl target@GOT, %ecx       # 8b 0d disp32: ecx = GOT[target] = &target
    movl (%ecx), %ebx           # ebx = 42
    movl $1, %eax
    int $0x80
    .data
    .globl target
target:
    .long 42
