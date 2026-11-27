/* DSO that, like FreeBSD libc.so.7, references data the executable defines. */
extern char **environ;
extern int hidden_thing;
extern void _Jv_RegisterClasses(void *) __attribute__((weak));
long get_env(void) { return (long)environ + hidden_thing + (_Jv_RegisterClasses ? 1 : 0); }
