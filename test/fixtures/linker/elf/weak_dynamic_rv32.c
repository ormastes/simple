/* musl crt shape: weak hidden _DYNAMIC, 0 in a static link (ld.lld). */
extern const unsigned long _DYNAMIC[] __attribute__((weak, visibility("hidden")));
const unsigned long *dyn_ptr = _DYNAMIC;
void _start(void) { __asm__ volatile("" :: "r"(dyn_ptr)); for (;;) {} }
