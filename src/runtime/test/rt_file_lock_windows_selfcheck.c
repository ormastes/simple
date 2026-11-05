/* Native Windows behavioral check, linked separately against runtime_native.c
 * and runtime_host_file_exports.c by check-bootstrap-windows-c-admission.shs. */
#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <windows.h>

extern int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs);
extern bool rt_file_unlock(int64_t handle);

typedef struct {
    const char* path;
    int64_t timeout_secs;
    int64_t handle;
    ULONGLONG elapsed_ms;
} LockAttempt;

static DWORD WINAPI attempt_main(void* opaque) {
    LockAttempt* attempt = (LockAttempt*)opaque;
    ULONGLONG started = GetTickCount64();
    attempt->handle = rt_file_lock((const uint8_t*)attempt->path, strlen(attempt->path), attempt->timeout_secs);
    attempt->elapsed_ms = GetTickCount64() - started;
    if (attempt->handle >= 0 && !rt_file_unlock(attempt->handle)) return 1;
    return 0;
}

static HANDLE start_attempt(LockAttempt* attempt, const char* path, int64_t timeout_secs) {
    attempt->path = path;
    attempt->timeout_secs = timeout_secs;
    attempt->handle = -2;
    attempt->elapsed_ms = 0;
    return CreateThread(NULL, 0, attempt_main, attempt, 0, NULL);
}

static int check_nonpositive(const char* path, int64_t timeout_secs) {
    int64_t holder = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (holder < 0) return 0;
    LockAttempt attempt;
    HANDLE thread = start_attempt(&attempt, path, timeout_secs);
    if (!thread) { rt_file_unlock(holder); return 0; }
    DWORD waited = WaitForSingleObject(thread, 2000);
    if (waited != WAIT_OBJECT_0) {
        rt_file_unlock(holder);
        WaitForSingleObject(thread, 2000);
    }
    DWORD thread_exit = 1;
    GetExitCodeThread(thread, &thread_exit);
    CloseHandle(thread);
    if (!rt_file_unlock(holder)) return 0;
    if (waited != WAIT_OBJECT_0 || thread_exit != 0 || attempt.handle != -1 || attempt.elapsed_ms >= 1000) return 0;
    int64_t again = rt_file_lock((const uint8_t*)path, strlen(path), timeout_secs);
    return again >= 0 && rt_file_unlock(again);
}

static int check_positive_expiry(const char* path) {
    int64_t holder = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (holder < 0) return 0;
    LockAttempt attempt;
    HANDLE thread = start_attempt(&attempt, path, 1);
    if (!thread) { rt_file_unlock(holder); return 0; }
    DWORD waited = WaitForSingleObject(thread, 3000);
    if (waited != WAIT_OBJECT_0) {
        rt_file_unlock(holder);
        WaitForSingleObject(thread, 2000);
    }
    CloseHandle(thread);
    if (!rt_file_unlock(holder)) return 0;
    return waited == WAIT_OBJECT_0 && attempt.handle == -1 &&
        attempt.elapsed_ms >= 800 && attempt.elapsed_ms < 3000;
}

static int check_positive_wait(const char* path) {
    int64_t holder = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (holder < 0) return 0;
    LockAttempt attempt;
    HANDLE thread = start_attempt(&attempt, path, 2);
    if (!thread) { rt_file_unlock(holder); return 0; }
    Sleep(200);
    if (!rt_file_unlock(holder)) { WaitForSingleObject(thread, 3000); CloseHandle(thread); return 0; }
    DWORD waited = WaitForSingleObject(thread, 3000);
    DWORD thread_exit = 1;
    GetExitCodeThread(thread, &thread_exit);
    CloseHandle(thread);
    return waited == WAIT_OBJECT_0 && thread_exit == 0 && attempt.handle >= 0 &&
        attempt.elapsed_ms >= 100 && attempt.elapsed_ms < 3000;
}

int main(void) {
    char directory[MAX_PATH];
    char path[MAX_PATH];
    if (!GetTempPathA(MAX_PATH, directory) || !GetTempFileNameA(directory, "sfl", 0, path)) return 1;
    if (rt_file_unlock(-1)) return 1;
    for (int timeout = -1; timeout <= 0; timeout++) {
        if (!check_nonpositive(path, timeout)) {
            fprintf(stderr, "FAIL: Windows nonpositive-timeout contention (%d)\n", timeout);
            return 1;
        }
    }
    if (!check_positive_expiry(path)) {
        fprintf(stderr, "FAIL: Windows positive-timeout expiration\n");
        return 1;
    }
    if (!check_positive_wait(path)) {
        fprintf(stderr, "FAIL: Windows positive-timeout acquisition after release\n");
        return 1;
    }
    DeleteFileA(path);
    puts("PASS: Windows C file-lock contention, timeouts, descriptor release, and reacquire");
    return 0;
}
