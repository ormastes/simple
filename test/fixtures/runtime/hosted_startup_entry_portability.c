/* Mirrors compile_entry_point_c's generated pre-main ABI. This fixture is
 * compiled for ELF, Mach-O, MinGW, and MSVC by portability checks. */
extern void spl_init_args(int argc, char **argv);
#if defined(_MSC_VER)
int __simple_startup_before_main_default(int argc, char **argv) {
    (void)argc; (void)argv; return 0;
}
#if defined(_M_IX86)
#pragma comment(linker, "/alternatename:___simple_startup_before_main=___simple_startup_before_main_default")
#else
#pragma comment(linker, "/alternatename:__simple_startup_before_main=__simple_startup_before_main_default")
#endif
extern int __simple_startup_before_main(int argc, char **argv);
#elif defined(__APPLE__) || defined(_WIN32)
int __attribute__((weak)) __simple_startup_before_main(int argc, char **argv) {
    (void)argc; (void)argv; return 0;
}
#else
extern int __simple_startup_before_main(int argc, char **argv) __attribute__((weak));
#endif
extern void __simple_runtime_init(void);
extern long long __simple_main(void);
extern void __simple_runtime_shutdown(void);

int main(int argc, char **argv) {
    spl_init_args(argc, argv);
#if defined(__ELF__)
    if (__simple_startup_before_main &&
            __simple_startup_before_main(argc, argv) != 0) return 125;
#else
    if (__simple_startup_before_main(argc, argv) != 0) return 125;
#endif
    __simple_runtime_init();
    {
        long long result = __simple_main();
        __simple_runtime_shutdown();
        return (int)result;
    }
}
