/* i386 twin of start_x64.c for the ELF32 dynamic lane. */
extern int add_val(int x);
extern const char msg[];

static int sys3(int n, int a, int b, int c) {
    int ret;
    __asm__ volatile("xchg %%ebx, %%edi\n\tint $0x80\n\txchg %%ebx, %%edi"
                     : "=a"(ret) : "a"(n), "D"(a), "c"(b), "d"(c) : "memory");
    return ret;
}

void _start(void) {
    sys3(4, 1, (int)msg, 3);            /* write(1, msg, 3) */
    int r = add_val(40);                /* 40 + base(2) = 42 */
    sys3(1, r, 0, 0);                   /* exit(r) */
    for (;;) {}
}
