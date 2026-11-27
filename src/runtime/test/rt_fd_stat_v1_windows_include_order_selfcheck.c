/* Reproduce runtime_native.c's already-included Windows SDK context. */
#if defined(_WIN32)
#define _WIN32_WINNT 0x0601
#include <windows.h>
#endif

#include "rt_fd_stat_v1_selfcheck.c"

#if defined(_WIN32) && _WIN32_WINNT != 0x0601
#error "Descriptor snapshot header must preserve the caller's Windows target"
#endif
