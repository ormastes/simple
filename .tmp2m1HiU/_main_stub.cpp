
extern "C" {
    int __attribute__((weak)) spl_main(void);
    void __attribute__((weak)) rt_set_args(int argc, char** argv);
    void __attribute__((weak)) __simple_runtime_init(void);
    void __attribute__((weak)) __simple_runtime_shutdown(void);
    void __attribute__((weak)) __simple_call_module_inits(void);
}
int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (__simple_call_module_inits) __simple_call_module_inits();
    if (rt_set_args) rt_set_args(argc, argv);
    int r = spl_main ? spl_main() : 0;
    if (__simple_runtime_shutdown) __simple_runtime_shutdown();
    return r;
}
