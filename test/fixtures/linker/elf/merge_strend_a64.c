/* End-of-merged-section symbol fixture (lane C1): `strend` is a global defined
   at the very END of a SHF_MERGE|SHF_STRINGS section (st_value == sh_size, no
   bytes after it). ld.lld-23 -O1 links it: for a NAMED Defined symbol,
   splitSections (SyntheticSections.cpp) anchors any v >= size on the last
   piece; the `offset > size` error in Symbols.cpp getSymVA applies only to
   SECTION symbols plus addend. It must resolve exactly one past the last piece. _start exits 40 + 2 = 42 only when strend - abc is 4 in the output,
   i.e. when the end-of-section offset was mapped, not rejected or clamped. */
static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

extern const char abc[];
extern const char strend[];

__asm__(".section .rodata.str1.1,\"aMS\",@progbits,1\n"
        ".globl abc\n"
        "abc:\n"
        ".asciz \"abc\"\n"
        ".globl strend\n"
        "strend:\n"
        ".text");

void _start(void) {
    long ok = ((strend - abc) == 4) ? 2 : 0;
    sys3(93, 40 + ok, 0, 0);
    for (;;) {}
}
