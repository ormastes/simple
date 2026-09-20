/* x86_64 twin of start_a64.c. */
extern long add_val(long x);
extern const char msg[];

static long sys3(long n, long a, long b, long c) {
    long ret;
    __asm__ volatile("syscall" : "=a"(ret) : "a"(n), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory");
    return ret;
}

void _start(void) {
    sys3(1, 1, (long)msg, 3);           /* write(1, msg, 3) */
    long r = add_val(40);               /* 40 + base(2) = 42 */
    sys3(60, r, 0, 0);                  /* exit(r) */
    for (;;) {}
}
