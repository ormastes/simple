#include <stdint.h>
extern void spl_init_args(int, char **);
extern int __simple_startup_before_main(int, char **) __attribute__((weak));
extern void __simple_runtime_init(void);
extern void __simple_runtime_shutdown(void);
extern void rt_println_str(const uint8_t *, uint64_t);
long long __simple_main(void) {
    static const uint8_t message[] = "Hello World";
    rt_println_str(message, sizeof(message) - 1);
    return 0;
}
int main(int argc, char **argv) {
    spl_init_args(argc, argv);
    if (__simple_startup_before_main && __simple_startup_before_main(argc, argv) != 0) return 125;
    __simple_runtime_init();
    long long result = __simple_main();
    __simple_runtime_shutdown();
    return (int)result;
}
