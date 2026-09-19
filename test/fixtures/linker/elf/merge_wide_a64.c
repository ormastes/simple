/* Wide-literal fixture (lane C1): L"wide" lands in .rodata.str4.4, a
   SHF_MERGE|SHF_STRINGS section with sh_entsize 4. ld.lld links it (it just
   declines to split it), so the internal linker must keep it unmerged
   instead of failing. Exits 40 + 1 + 1 = 42. */
static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

typedef __WCHAR_TYPE__ wchar_t;
const wchar_t *w(void) { return L"wide"; }
void _start(void) { const wchar_t *p = w(); sys3(93, 40 + (p[0] == L'w') + (p[3] == L'e'), 0, 0); for(;;){} }
