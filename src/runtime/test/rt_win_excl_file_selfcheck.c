/* Self-check for platform/runtime_win_excl_file.h (Windows exclusive no-follow
 * copy / hard link). Build: x86_64-w64-mingw32-clang -o t.exe this.c
 * On non-Windows hosts this compiles to a no-op (the POSIX twins are covered by
 * the SSpec test/02_integration/runtime/excl_copy_link_no_follow_spec.spl). */
#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32)
#include "../platform/runtime_win_excl_file.h"

static int fails = 0;
#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); fails++; } \
    else printf("ok: %s\n", #c); } while (0)

static void put(const char* p, const char* s) {
    FILE* f = fopen(p, "wb");
    if (f) { fputs(s, f); fclose(f); }
}
static long size_of(const char* p) {
    FILE* f = fopen(p, "rb");
    long n;
    if (!f) return -1;
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fclose(f);
    return n;
}

int main(void) {
    const char* d = "rt_win_excl_probe";
    char s[260], c[260], l[260], c2[260], jn[260];
    snprintf(s, sizeof s, "%s/s.o", d);
    snprintf(c, sizeof c, "%s/c.o", d);
    snprintf(l, sizeof l, "%s/l.o", d);
    snprintf(c2, sizeof c2, "%s/c2.o", d);
    snprintf(jn, sizeof jn, "%s/jn", d);
    CreateDirectoryA(d, NULL);
    DeleteFileA(s); DeleteFileA(c); DeleteFileA(l); DeleteFileA(c2);
    put(s, "complete-object-bytes");
    CHECK(rt_win_file_copy_create_excl_no_follow(s, c) == 1);
    CHECK(size_of(c) == 21);
    CHECK(rt_win_file_copy_create_excl_no_follow(s, c) == 0);
    CHECK(rt_win_file_link_create_excl_no_follow(s, l) == 1);
    CHECK(size_of(l) == 21);
    CHECK(rt_win_file_link_create_excl_no_follow(s, l) == 0);
    CHECK(rt_win_file_copy_create_excl_no_follow("rt_win_excl_probe/missing", c2) == 0);
    CHECK(rt_win_file_copy_create_excl_no_follow(d, c2) == 0);
    CHECK(GetFileAttributesA(c2) == INVALID_FILE_ATTRIBUTES);
    /* A directory junction is a reparse point: never a source, never a
     * destination (no privilege needed, unlike file symlinks). */
    {
        char cmd[600];
        RemoveDirectoryA(jn);
        snprintf(cmd, sizeof cmd, "cmd /c mklink /J \"%s\" \"%s\" >nul", jn, d);
        if (system(cmd) == 0) {
            CHECK(rt_win_file_copy_create_excl_no_follow(jn, c2) == 0);
            CHECK(rt_win_file_link_create_excl_no_follow(jn, c2) == 0);
            CHECK(rt_win_file_copy_create_excl_no_follow(s, jn) == 0);
            RemoveDirectoryA(jn);
        } else {
            printf("SKIP: junction creation unavailable\n");
        }
    }
    DeleteFileA(s); DeleteFileA(c); DeleteFileA(l);
    RemoveDirectoryA(d);
    printf("fails=%d\n", fails);
    return fails ? 1 : 0;
}
#else
int main(void) { printf("skipped: not Windows\n"); return 0; }
#endif
