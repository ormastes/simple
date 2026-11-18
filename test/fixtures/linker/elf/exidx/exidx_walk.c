/* Freestanding .ARM.exidx walker: decodes the table between __exidx_start and
 * __exidx_end (PREL31 entries), checks strictly increasing addresses, a final
 * EXIDX_CANTUNWIND sentinel, and that a binary search finds this file's own
 * functions. Exits 0 on success, 1 on failure (Linux EABI svc exit, r7 = 1).
 * Built by C:/dev/wt/xc-wsl-scripts/ssos_exwalk.sh. */
extern const unsigned __exidx_start[], __exidx_end[];

static unsigned prel31(const unsigned *at) {
    unsigned v = *at & 0x7fffffffu;
    if (v & 0x40000000u) v |= 0x80000000u;
    return (unsigned)at + v;
}

static const unsigned *lookup(unsigned pc) {
    unsigned n = (unsigned)(__exidx_end - __exidx_start) / 2, lo = 0, hi = n;
    while (hi - lo > 1) {
        unsigned mid = (lo + hi) / 2;
        if (prel31(&__exidx_start[mid * 2]) <= pc) lo = mid; else hi = mid;
    }
    return n ? &__exidx_start[lo * 2] : 0;
}

__attribute__((noinline)) int helper(int x) { return x * 7 + 1; }

__attribute__((noreturn)) static void sys_exit(int code) {
    register int r0 __asm__("r0") = code;
    register int r7 __asm__("r7") = 1;
    __asm__ volatile("svc #0" :: "r"(r0), "r"(r7));
    for (;;) {}
}

int check(void) {
    unsigned n = (unsigned)(__exidx_end - __exidx_start);
    if (n < 4 || (n & 1)) return 1;
    for (unsigned i = 2; i < n; i += 2)
        if (prel31(&__exidx_start[i]) <= prel31(&__exidx_start[i - 2])) return 1;
    if (__exidx_start[n - 1] != 1) return 1;
    unsigned fns[2] = { (unsigned)&helper, (unsigned)&check };
    for (int k = 0; k < 2; k++) {
        const unsigned *e = lookup(fns[k]);
        if (!e || prel31(e) > fns[k] || e == &__exidx_start[n - 2]) return 1;
    }
    return helper(0) == 1 ? 0 : 1;
}

void _start(void) { sys_exit(check()); }
