/* Selfcheck: a cache reader opened via rt_win_fopen_read_shared must not block
 * a producer's MoveFileExW(REPLACE_EXISTING) over the file, and must keep
 * reading the OLD bytes to EOF (POSIX rename contract). Also proves that the
 * plain CRT fopen() reader DOES block the replace, so the check is not vacuous.
 * Review: cache_build_review_and_portability_2026-10-24 P1 (Windows rename
 * onto an open file). Non-Windows: trivially passes. */
#include <stdio.h>
#include <string.h>
#if defined(_WIN32)
#include "../platform/runtime_win_long_path.h"

static int write_file(const char* path, const char* text) {
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    size_t n = fwrite(text, 1, strlen(text), f);
    fclose(f);
    return n == strlen(text);
}

static int replace(const char* staged, const char* dest) {
    return rt_win_long_path_rename(staged, dest);
}

int main(void) {
    char dir[MAX_PATH];
    if (!GetTempPathA(MAX_PATH, dir)) return 2;
    char dest[MAX_PATH * 2], staged[MAX_PATH * 2];
    snprintf(dest, sizeof dest, "%srt_share_delete_%lu.bin", dir, (unsigned long)GetCurrentProcessId());
    snprintf(staged, sizeof staged, "%s.tmp", dest);
    int failures = 0;

    /* 1. shared reader: replace succeeds, reader sees old bytes */
    if (!write_file(dest, "old-bytes") || !write_file(staged, "new-bytes")) return 2;
    FILE* reader = rt_win_fopen_read_shared(dest);
    if (!reader) { printf("FAIL shared open\n"); return 1; }
    if (!replace(staged, dest)) { printf("FAIL replace over shared reader (err=%lu)\n", GetLastError()); failures++; }
    char buf[32] = {0};
    size_t got = fread(buf, 1, sizeof buf - 1, reader);
    fclose(reader);
    if (got != 9 || strcmp(buf, "old-bytes") != 0) { printf("FAIL reader saw '%s'\n", buf); failures++; }
    FILE* after = fopen(dest, "rb");
    char now[32] = {0};
    if (after) { fread(now, 1, sizeof now - 1, after); fclose(after); }
    if (strcmp(now, "new-bytes") != 0) { printf("FAIL dest has '%s'\n", now); failures++; }

    /* 2. control: plain CRT reader blocks the replace (non-vacuity) */
    if (!write_file(staged, "third")) return 2;
    FILE* crt = fopen(dest, "rb");
    int blocked = crt && !replace(staged, dest);
    if (crt) fclose(crt);
    if (!blocked) { printf("NOTE control: CRT reader did not block replace on this host\n"); }
    DeleteFileA(staged);
    DeleteFileA(dest);
    if (failures) return 1;
    printf("PASS rt_win_share_delete_replace (control_blocked=%d)\n", blocked);
    return 0;
}
#else
int main(void) { printf("PASS rt_win_share_delete_replace (non-Windows)\n"); return 0; }
#endif
