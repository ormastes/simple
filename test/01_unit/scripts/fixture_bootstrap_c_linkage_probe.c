#ifdef __cplusplus
extern "C" {
#endif

extern int spl_main(void);
extern void rt_set_args(int, char**);

void __simple_call_module_inits(void) {
    char *argv[] = {0};
    rt_set_args(0, argv);
    (void)spl_main();
}

void __module_init_security_registry(void) {}

#ifdef __cplusplus
}
#endif
