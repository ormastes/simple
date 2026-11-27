/* Windows-only actual-handle retention regressions. NOT_RUN. Fault wrappers
 * leave the real handle live on selected failures, then invoke native retry. */
#if !defined(_WIN32)
#error "requires an authorized Windows native test slot"
#endif
#include <windows.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>
static int fail_unlock_once;
static int fail_close_once;
static int unlock_calls;
static int close_calls;
static int test_unlock(HANDLE handle, OVERLAPPED *overlapped) {
    ++unlock_calls;
    if (fail_unlock_once) { fail_unlock_once = 0; SetLastError(ERROR_ACCESS_DENIED); return 0; }
    return UnlockFileEx(handle, 0, MAXDWORD, MAXDWORD, overlapped) != 0;
}
static int test_close(HANDLE handle) {
    ++close_calls;
    if (fail_close_once) { fail_close_once = 0; SetLastError(ERROR_ACCESS_DENIED); return 0; }
    return CloseHandle(handle) != 0;
}
#define SPL_OWNED_LOCK_UNLOCK_V2(h, o) test_unlock((h), (o))
#define SPL_OWNED_LOCK_CLOSE_V2(h) test_close(h)
#include "../runtime_file_lock_owned_v2.c"
static int64_t acquire(const char *path) {
    return rt_file_lock_owned_acquire_v2((const uint8_t *)path, strlen(path), 0);
}
int main(void) {
    wchar_t temp[MAX_PATH], original[MAX_PATH], wide[MAX_PATH + 16];
    char path[4096];
    assert(GetTempPathW(MAX_PATH, temp));
    assert(GetTempFileNameW(temp, L"slk", 0, original));
    wcscpy(wide, original);
    wcscat(wide, L"-\u03bb");
    assert(MoveFileW(original, wide));
    assert(WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, wide, -1,
        path, sizeof(path), NULL, NULL) > 0);
    const uint8_t invalid_utf8[] = {0xff};
    assert(rt_file_lock_owned_acquire_v2(invalid_utf8, 1, 0) == 0);
    int64_t first = acquire(path);
    assert(first > 0 && rt_file_lock_owned_state_v2(first) == 1);
    int closes = close_calls;
    fail_unlock_once = 1;
    assert(rt_file_lock_owned_release_v2(first) == 2);
    assert(rt_file_lock_owned_state_v2(first) == 1 && close_calls == closes);
    /* Failed acquisition still returns the actual opened cleanup handle. */
    fail_close_once = 1;
    int64_t cleanup = acquire(path);
    assert(cleanup > 0 && cleanup != first);
    assert(rt_file_lock_owned_state_v2(cleanup) == 2);
    assert(rt_file_lock_owned_release_v2(cleanup) == 1);
    int unlocks = unlock_calls;
    fail_close_once = 1;
    assert(rt_file_lock_owned_release_v2(first) == 2);
    assert(rt_file_lock_owned_state_v2(first) == 2);
    assert(unlock_calls == unlocks + 1);
    assert(rt_file_lock_owned_release_v2(first) == 1);
    assert(unlock_calls == unlocks + 1); /* close retry never unlocks twice */
    int64_t replacement = acquire(path);
    assert(replacement > 0 && replacement != first);
    closes = close_calls;
    assert(rt_file_lock_owned_release_v2(first) == 0 && close_calls == closes);
    assert(rt_file_lock_owned_state_v2(replacement) == 1);
    assert(rt_file_lock_owned_release_v2(replacement) == 1);
    assert(DeleteFileW(wide));
    return 0;
}
