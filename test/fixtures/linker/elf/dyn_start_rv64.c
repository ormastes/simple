/* riscv64 twin of dyn_start_arm.c: GOT (msg), CALL_PLT (add_val), exits 42. */
extern int add_val(int x);
extern const char msg[];

static long sys3(long n, long a, long b, long c) {
    register long a0 __asm__("a0") = a;
    register long a1 __asm__("a1") = b;
    register long a2 __asm__("a2") = c;
    register long a7 __asm__("a7") = n;
    __asm__ volatile("ecall" : "+r"(a0) : "r"(a1), "r"(a2), "r"(a7) : "memory");
    return a0;
}

void _start(void) {
    __asm__ volatile(".option push\n.option norelax\nla gp, __global_pointer$\n.option pop");
    sys3(64, 1, (long)msg, 3);          /* write(1, msg, 3) */
    sys3(93, add_val(40), 0, 0);        /* exit(42) */
    for (;;) {}
}
