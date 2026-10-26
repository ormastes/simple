/* Compile as a standalone C11 translation unit on Windows. No umbrella or
 * standard header may precede this include: the production header must own
 * every declaration used by its inline function bodies. UNRUN. */
#include "../platform/runtime_win_long_path.h"

#if !defined(_WIN32)
#error "This is a Windows header qualification fixture, not a POSIX skip."
#endif

int main(void) {
    wchar_t* current = rt_win_long_path_widen(".");
    if (!current) return 1;
    free(current);
    return 0;
}
