/* armv7 Thumb: a tail call to an imported function (b.w add_val, R_ARM_THM_JUMP24). */
extern int add_val(int x);
extern const char msg[];

static int sys3(int n, int a, int b, int c) {
    register int r0 __asm__("r0") = a;
    register int r1 __asm__("r1") = b;
    register int r2 __asm__("r2") = c;
    register int r7 __asm__("r7") = n;
    __asm__ volatile("svc #0" : "+r"(r0) : "r"(r1), "r"(r2), "r"(r7) : "memory");
    return r0;
}

__attribute__((noinline)) int tail(int x) { return add_val(x); }

void _start(void) {
    sys3(4, 1, (int)msg, 3);
    sys3(1, tail(40), 0, 0);
    for (;;) {}
}
