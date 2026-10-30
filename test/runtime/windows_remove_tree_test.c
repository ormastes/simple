/* Call the production owner, including the exact (ptr,len) core ABI. */
#include <windows.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "runtime.h"
#ifdef TEST_FULL_PLATFORM
#include "platform/platform_win.h"
#elif defined(TEST_SHARED_FULL_POLICY)
#include "platform/runtime_win_remove_tree.h"
#endif

int wmain(int argc, wchar_t** argv) {
    if (argc != 2) return 2;
    int size = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, argv[1], -1,
                                 NULL, 0, NULL, NULL);
    if (!size) return 3;
    char* path = malloc((size_t)size + 16);
    if (!path || !WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, argv[1], -1,
                                    path, size, NULL, NULL)) return 4;
#ifdef TEST_FULL_PLATFORM
    bool removed = rt_dir_remove_all_cpath(path);
#elif defined(TEST_SHARED_FULL_POLICY)
    bool removed = rt_win_remove_tree_utf8(path, false, false);
#else
    /* The bytes after the declared text length must never enter the path. */
    memcpy(path + size - 1, ".not-owned", 11);
    bool removed = rt_dir_remove_all((const uint8_t*)path, (uint64_t)size - 1);
#endif
    free(path);
    puts(removed ? "removed" : "refused");
    return removed ? 0 : 1;
}
