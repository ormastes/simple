/* armv7 Thumb: general-dynamic access to an imported TLS variable and to a
   local one (TLS_GD32); getld() in dyn_tlsld_arm.s covers TLS_LDM32/LDO32. */
extern __thread int tv;                                   /* 37, in libtls_arm.so */
static __thread int lv = 3;
extern int getld(void);                                   /* 2 */

static int sys3(int n, int a, int b, int c) {
    register int r0 __asm__("r0") = a;
    register int r1 __asm__("r1") = b;
    register int r2 __asm__("r2") = c;
    register int r7 __asm__("r7") = n;
    __asm__ volatile("svc #0" : "+r"(r0) : "r"(r1), "r"(r2), "r"(r7) : "memory");
    return r0;
}

__attribute__((noinline)) int get(void) { return tv + lv + getld(); }

void _start(void) {
    sys3(1, get(), 0, 0);                                  /* exit(42) */
    for (;;) {}
}
