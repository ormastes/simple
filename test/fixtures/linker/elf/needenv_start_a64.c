/* Executable defining environ (as FreeBSD crt1.o does), a weak
   _Jv_RegisterClasses, and a hidden symbol that must stay out of .dynsym. */
char **environ = 0;
__attribute__((visibility("hidden"))) int hidden_thing = 7;
__attribute__((weak)) void _Jv_RegisterClasses(void *p) { (void)p; }
long get_env(void);
void _start(void) { get_env(); for (;;) {} }
