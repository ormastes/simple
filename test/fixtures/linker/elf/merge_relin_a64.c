/* Relocation-into-a-merge-section fixture (lane C1): .rodata.cst8 is
   SHF_MERGE with sh_entsize 8 AND holds `.quad target`, so a relocation
   points into it. ld.lld demotes such a section to a regular input section
   rather than erroring, and so must the internal linker. Exits 40 + 2 = 42. */
static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

long target = 2;
void _start(void) { long **pp; __asm__("adrp %0, .Lp\n\tadd %0, %0, :lo12:.Lp" : "=r"(pp)); sys3(93, 40 + **pp, 0, 0); for(;;){} }
__asm__(".section .rodata.cst8,\"aM\",@progbits,8\n.p2align 3\n.Lp: .quad target\n.text");
