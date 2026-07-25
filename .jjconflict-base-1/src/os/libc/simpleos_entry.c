/* Stable Simple-language entry shim for filesystem-linked user programs. */
extern void __simple_runtime_init(void);
extern long long __simple_main(void);
extern void __simple_runtime_shutdown(void);

int main(int argc, char **argv) {
    (void)argc;
    (void)argv;
    __simple_runtime_init();
    long long result = __simple_main();
    __simple_runtime_shutdown();
    return (int)result;
}
