/* Wide-literal fixture A (lane C1): L"wide" lands in .rodata.str4.4, a
   SHF_MERGE|SHF_STRINGS section with sh_entsize 4. It is shared with
   merge_wideb_a64.c, so a -O1 link must dedupe it across the two objects the
   way it dedupes byte strings. _start exits 40 + 2 = 42 only when the two
   copies resolved to ONE address. */
static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

typedef __WCHAR_TYPE__ wchar_t;
extern const wchar_t *wide_b(void);

const wchar_t *wide_a(void) { return L"wide"; }

void _start(void) {
    long same = (wide_a() == wide_b()) ? 2 : 0;
    sys3(93, 40 + same, 0, 0);
    for (;;) {}
}
