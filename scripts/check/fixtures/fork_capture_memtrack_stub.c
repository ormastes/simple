/* Minimal memtrack stubs so runtime_fork.c links standalone in the guard. */
#include <stddef.h>
int g_memtrack_enabled = 0;
void spl_memtrack_record(void* p, size_t n, const char* tag) { (void)p; (void)n; (void)tag; }
void spl_memtrack_unrecord(void* p) { (void)p; }
