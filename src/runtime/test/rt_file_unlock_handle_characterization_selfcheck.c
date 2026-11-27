/*
 * Characterization (NOT a fix) of rt_file_lock / rt_file_unlock as owned by
 * runtime_host_file_exports.c. On Windows that owner returns a raw HANDLE
 * (CreateFileA) rather than the CRT fd returned by runtime_native.c's copy.
 * This pins the CURRENT behaviour so the divergence (filed as a bug) can be
 * reconciled later without surprise. Transcript is compared against
 * rt_file_unlock_handle_characterization.<os>.golden.txt.
 *
 * Build (Windows, llvm-mingw clang; Linux: wsl -d ubuntu-p2 -- clang-18):
 *   clang -std=c11 -Wall -Werror -Wno-unused-variable -I src/runtime \
 *     src/runtime/test/rt_file_unlock_handle_characterization_selfcheck.c \
 *     src/runtime/runtime_host_file_exports.c -o build/rt_char/unlock.exe
 */
#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

/* ---- shims for the tagged API the TU references but this test never
 *      reaches (mmap/byte-array paths) ---- */
int64_t rt_string_len(int64_t v) { (void)v; return -1; }
const uint8_t* rt_string_data(int64_t v) { (void)v; return NULL; }
SplArray* rt_byte_array_new_len(uint64_t n) { (void)n; return NULL; }
int64_t rt_array_bytes_store_checked(int64_t a, const uint8_t* b, int64_t n) {
    (void)a; (void)b; (void)n; return -1;
}
void rt_array_free(SplArray* a) { (void)a; }

static void show(const char* id, int64_t v) {
    printf("%-28s -> %s\n", id, v >= 0 ? "ok" : "-1");
}
static void showb(const char* id, bool v) { printf("%-28s -> %s\n", id, v ? "true" : "false"); }

static int64_t lock_path(const char* p, int64_t timeout) {
    return rt_file_lock((const uint8_t*)p, (uint64_t)strlen(p), timeout);
}

int main(void) {
    char path[512];
#ifdef _WIN32
    char tmp[MAX_PATH];
    GetTempPathA(sizeof(tmp), tmp);
    snprintf(path, sizeof(path), "%srt_unlock_char_%lu.lock", tmp, (unsigned long)GetCurrentProcessId());
    printf("os windows\n");
#else
    const char* tdir = getenv("TMPDIR");
    snprintf(path, sizeof(path), "%s/rt_unlock_char_%ld.lock", tdir && *tdir ? tdir : "/tmp", (long)getpid());
    printf("os posix\n");
#endif
    /* argument validation */
    show("lock_null_ptr", rt_file_lock(NULL, 5, 0));
    show("lock_len0", rt_file_lock((const uint8_t*)path, 0, 0));
    show("lock_embedded_nul", rt_file_lock((const uint8_t*)"a\0b", 3, 0));
    {
        char* big = (char*)malloc(4097);
        memset(big, 'a', 4096);
        big[4096] = 0;
        int64_t lb = rt_file_lock((const uint8_t*)big, 4095, 0);
        show("lock_len_4095", lb);
        if (lb >= 0) rt_file_unlock(lb);
        show("lock_len_4096", rt_file_lock((const uint8_t*)big, 4096, 0));
        free(big);
    }
    show("lock_missing_dir", lock_path("Z:/definitely/missing/dir/x.lock", 0));

    /* basic lock / unlock / relock */
    int64_t h = lock_path(path, 0);
    show("lock_t0", h);
    showb("unlock_once", rt_file_unlock(h));
    h = lock_path(path, 0);
    show("relock_t0", h);
    /* second owner in the SAME process: LockFileEx byte-range locks are
     * per-handle on Windows, flock is per-open-file-description on POSIX. */
    int64_t h2 = lock_path(path, 0);
    show("second_lock_same_process", h2);
    if (h2 >= 0) rt_file_unlock(h2);
    int64_t h3 = lock_path(path, 1);
    show("second_lock_timeout1", h3);
    if (h3 >= 0) rt_file_unlock(h3);
    showb("unlock_held", rt_file_unlock(h));

    /* unlock on invalid handles */
    showb("unlock_minus1", rt_file_unlock(-1));
    showb("unlock_zero", rt_file_unlock(0));
#ifdef _WIN32
    /* a real HANDLE that holds no lock: UnlockFileEx fails, CloseHandle ok */
    HANDLE plain = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE, NULL,
                               OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    showb("unlock_unlocked_handle", rt_file_unlock((int64_t)(intptr_t)plain));
    /* returned value is a HANDLE, not a small CRT fd */
    h = lock_path(path, 0);
    printf("%-28s -> %s\n", "handle_kind", (h >= 0 && GetFileType((HANDLE)(intptr_t)h) == FILE_TYPE_DISK) ? "win32_handle" : "other");
    rt_file_unlock(h);
    DeleteFileA(path);
#else
    showb("unlock_huge", rt_file_unlock((int64_t)1 << 40));
    unlink(path);
#endif
    return 0;
}
