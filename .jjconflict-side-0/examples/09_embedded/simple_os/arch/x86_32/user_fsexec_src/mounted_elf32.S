/* Real i386 filesystem-exec payload.  The future CPL3 owner passes the
 * validated nonce buffer in ECX and its bounded length in EDX.
 * SimpleOS x86_32 int80 ABI: EAX=id, EBX..=args. */
.section .text
.global _start
.type _start, @function
_start:
    movl    %ecx, %ebx
    movl    %edx, %ecx
    movl    $60, %eax
    int     $0x80
    movl    $37, %ebx
    xorl    %eax, %eax
    int     $0x80
1:
    hlt
    jmp     1b
.size _start, . - _start
