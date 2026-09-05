#ifdef WIN32
void init(void) { win_init(); win_extra(); }
#else
void init(void) { posix_init(); }
#endif
