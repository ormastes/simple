/*
 * Minimal bare-metal runtime glue for Simple-built test images.
 *
 * Provides the symbols expected by the startup assembly without pulling in
 * the hosted runtime or constructor support.
 */

extern long long __simple_main(void);
extern char __bss_start[];
extern char __bss_end[];

static void zero_bss(void) {
    for (char *p = __bss_start; p < __bss_end; p++) {
        *p = 0;
    }
}

void spl_thread_init(void) {}

void spl_init_args(int argc, char **argv) {
    (void)argc;
    (void)argv;
}

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    return (int)__simple_main();
}

void __spl_exit(int status) {
    (void)status;
#if defined(__x86_64__) || defined(__i386__)
    __asm__ volatile (
        "cli\n"
        "1: hlt\n"
        "jmp 1b\n"
    );
#elif defined(__aarch64__)
    __asm__ volatile (
        "msr daifset, #0xF\n"
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__arm__)
    __asm__ volatile (
        "cpsid if\n"
        "1: wfi\n"
        "b 1b\n"
    );
#elif defined(__riscv)
    __asm__ volatile (
        "csrci mstatus, 0x8\n"
        "1: wfi\n"
        "j 1b\n"
    );
#else
    for (;;) {}
#endif
    __builtin_unreachable();
}

void __spl_start_bare(void) {
    zero_bss();
    __spl_exit(main(0, (char **)0));
}
