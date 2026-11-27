/* armv7 (Thumb) twin of start_x64.c for the ELF32 dynamic lane. */
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

void _start(void) {
    sys3(4, 1, (int)msg, 3);            /* write(1, msg, 3) */
    int r = add_val(40);                /* 40 + base(2) = 42 */
    sys3(1, r, 0, 0);                   /* exit(r) */
    for (;;) {}
}
