#ifdef WIN32
void init(void) { win_init(); }
#else
void init(void) { posix_init(); posix_extra(); }
#endif
