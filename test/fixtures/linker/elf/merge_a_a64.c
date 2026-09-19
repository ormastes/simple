/* String-merge fixture A (lane C1). Shares the literals "hi\n" and "dup\n"
   with merge_b_a64.c, and adds one of its own; a named const array lives in
   the same SHF_MERGE|SHF_STRINGS section, so a relocation against a defined
   symbol inside a merged section is exercised alongside the usual
   section-symbol + addend form. Writes "hi\n" and exits 40 + 2 = 42. */
extern long merge_b(const char *s);
extern const char *b_dup(void);

static long sys3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
    return x0;
}

const char *a_hi(void) { return "hi\n"; }
const char *a_dup(void) { return "dup\n"; }
const char *a_only(void) { return "only-a\n"; }

void _start(void) {
    sys3(64, 1, (long)a_hi(), 3);
    long same = (a_dup() == b_dup()) ? 2 : 0;   /* merged: one address */
    sys3(93, merge_b(a_only()) + same, 0, 0);
    for (;;) {}
}
