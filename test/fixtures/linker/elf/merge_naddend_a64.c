/* Named-symbol + NON-ZERO addend into a merged section (lane C1+C2 merge).

   ld.lld Symbols.cpp getSymVA folds the addend into the merge piece lookup
   ONLY for an STT_SECTION symbol (`offset += addend` ... `va -= addend`); for
   a NAMED symbol it looks the piece up at st_value and applies the addend
   afterwards. x86_64 shows this as `R_X86_64_PC32 .L.str - 4`, which needs a
   glibc sysroot and qemu; this fixture pins the same rule natively on aarch64.

   `.rodata.str1.1` holds "dup\0" twice, so merging collapses both pieces onto
   one output address P. `s1` is the first copy, `s2` the second (st_value 4).
   The reference is `s2 - 4`:
     correct (piece at st_value 4, then + addend) -> P - 4
     folded  (piece at 4 + (-4) = 0)              -> P
   so `s1 - (s2 - 4)` is 4 when the addend is applied after the lookup and 0
   when it was folded in. Exit 40 + 2 = 42 merged, 40 unmerged (-O0: the copies
   stay 4 bytes apart, so s2 - 4 == s1), matching ld.lld -O1 / -O0. */
static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

__asm__(".section .rodata.str1.1,\"aMS\",@progbits,1\n"
        "s1:\n"
        ".asciz \"dup\"\n"
        "s2:\n"
        ".asciz \"dup\"\n"
        ".text");

static const char *at_s1(void) {
    const char *p;
    __asm__("adrp %0, s1\n\tadd %0, %0, :lo12:s1" : "=r"(p));
    return p;
}

static const char *at_s2_minus_4(void) {
    const char *p;
    __asm__("adrp %0, s2-4\n\tadd %0, %0, :lo12:s2-4" : "=r"(p));
    return p;
}

void _start(void) {
    long ok = ((at_s1() - at_s2_minus_4()) == 4) ? 2 : 0;
    sys3(93, 40 + ok, 0, 0);
    for (;;) {}
}
