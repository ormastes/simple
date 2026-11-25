/*
 * Behavioral selfcheck for rt_file_lock / rt_file_unlock (runtime_native.c)
 * and rt_crt_close (runtime_crt_file.h):
 *   1. Valid rt_crt_open + rt_crt_close roundtrip on all platforms, plus POSIX
 *      EBADF invalid-fd / double-close safety (omitted on Windows UCRT where
 *      unguarded _close on negative/unopened/closed fds invokes _invoke_watson).
 *   2. rt_file_lock invalid-path / missing-directory error-path safety across
 *      nonpositive and positive timeouts.
 *   3. rt_file_unlock negative-fd safety (-1, -42, INT_MIN) on all platforms,
 *      plus POSIX unopened/double-unlock safety.
 *   4. Contended nonpositive (0, -1) and positive-timeout expiry (1s) closing
 *      descriptors cleanly across repeated attempts without leaking fds.
 */
#if !defined(_WIN32) && !defined(_POSIX_C_SOURCE)
#define _POSIX_C_SOURCE 200809L
#endif

#include "../runtime.h"
#include "../runtime_crt_file.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

#if defined(_WIN32)
#include <io.h>
#include <windows.h>
#else
#include <signal.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#endif

extern int64_t rt_file_lock(const uint8_t* path_ptr, uint64_t path_len, int64_t timeout_secs);
extern bool rt_file_unlock(int64_t handle);

static unsigned g_checks = 0;

#define CHECK(label, cond) do { \
    ++g_checks; \
    if (!(cond)) { \
        fprintf(stderr, "FAIL %s (check=%u line=%d errno=%d)\n", \
                (label), g_checks, __LINE__, errno); \
        return 1; \
    } \
} while (0)

#if defined(_WIN32)
typedef struct {
    const char* path;
    int64_t timeout_secs;
    int rounds;
    ULONGLONG elapsed_ms;
} ContendArgs;

static DWORD WINAPI contend_worker(void* opaque) {
    ContendArgs* args = (ContendArgs*)opaque;
    ULONGLONG started = GetTickCount64();
    for (int i = 0; i < args->rounds; i++) {
        int64_t h = rt_file_lock((const uint8_t*)args->path,
                                 (uint64_t)strlen(args->path),
                                 args->timeout_secs);
        if (h >= 0) {
            rt_file_unlock(h);
            return 2;
        }
        if (h != -1) return 3;
    }
    args->elapsed_ms = GetTickCount64() - started;
    return 0;
}

static int run_contended_rounds(const char* path, int64_t timeout_secs, int rounds,
                                unsigned long long* elapsed_ms_out) {
    ContendArgs* args = (ContendArgs*)calloc(1, sizeof(ContendArgs));
    if (!args) return 0;
    args->path = path;
    args->timeout_secs = timeout_secs;
    args->rounds = rounds;
    HANDLE thread = CreateThread(NULL, 0, contend_worker, args, 0, NULL);
    if (!thread) {
        free(args);
        return 0;
    }
    DWORD waited = WaitForSingleObject(thread, 10000);
    DWORD exit_code = 1;
    if (waited == WAIT_OBJECT_0) {
        GetExitCodeThread(thread, &exit_code);
        if (elapsed_ms_out) *elapsed_ms_out = (unsigned long long)args->elapsed_ms;
        CloseHandle(thread);
        free(args);
        return exit_code == 0;
    }
    /* Leave heap-allocated args intact if worker outlives timeout so worker
     * never touches freed memory while process exits on failure. */
    CloseHandle(thread);
    return 0;
}
#else
static void alarm_abort(int sig) {
    (void)sig;
    _exit(124);
}

static unsigned long long monotonic_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (unsigned long long)ts.tv_sec * 1000ULL + (unsigned long long)(ts.tv_nsec / 1000000L);
}

static int run_contended_rounds(const char* path, int64_t timeout_secs, int rounds,
                                unsigned long long* elapsed_ms_out) {
    unsigned long long started = monotonic_ms();
    pid_t child = fork();
    if (child < 0) return 0;
    if (child == 0) {
        signal(SIGALRM, alarm_abort);
        alarm((unsigned int)(timeout_secs > 0 ? timeout_secs + 4 : 4));
        for (int i = 0; i < rounds; i++) {
            int64_t h = rt_file_lock((const uint8_t*)path,
                                     (uint64_t)strlen(path),
                                     timeout_secs);
            if (h >= 0) {
                rt_file_unlock(h);
                _exit(2);
            }
            if (h != -1) _exit(3);
        }
        _exit(0);
    }
    int status = 0;
    pid_t rc;
    do {
        rc = waitpid(child, &status, 0);
    } while (rc < 0 && errno == EINTR);
    if (elapsed_ms_out) {
        unsigned long long ended = monotonic_ms();
        *elapsed_ms_out = ended >= started ? ended - started : 0;
    }
    return rc == child && WIFEXITED(status) && WEXITSTATUS(status) == 0;
}
#endif

static int format_path(char* dst, size_t cap, const char* dir, const char* sep,
                       const char* name, unsigned long pid) {
    int n = snprintf(dst, cap, "%s%s%s_%lu", dir, sep, name, pid);
    return n > 0 && (size_t)n < cap;
}

int main(void) {
    char crt_path[512];
    char lock_path[512];
    char missing_path[512];

#if defined(_WIN32)
    char dir[MAX_PATH];
    unsigned long pid = (unsigned long)GetCurrentProcessId();
    CHECK("GetTempPathA", GetTempPathA(MAX_PATH, dir) > 0);
    CHECK("format crt_path", format_path(crt_path, sizeof(crt_path), dir, "", "rt_crt_close_sc.tmp", pid));
    CHECK("format lock_path", format_path(lock_path, sizeof(lock_path), dir, "", "rt_lock_crt_sc.lock", pid));
    CHECK("format missing_path", format_path(missing_path, sizeof(missing_path), dir, "", "sfl_no_dir\\x.lock", pid));
#else
    const char* tmpdir = getenv("TMPDIR");
    const char* base = (tmpdir && *tmpdir) ? tmpdir : "/tmp";
    unsigned long pid = (unsigned long)getpid();
    CHECK("format crt_path", format_path(crt_path, sizeof(crt_path), base, "/", "rt_crt_close_sc.tmp", pid));
    CHECK("format lock_path", format_path(lock_path, sizeof(lock_path), base, "/", "rt_lock_crt_sc.lock", pid));
    CHECK("format missing_path", format_path(missing_path, sizeof(missing_path), base, "/", "sfl_no_dir/x.lock", pid));
#endif

    /* 1. Valid rt_crt_open + rt_crt_close roundtrip (+ POSIX EBADF checks). */
#if !defined(_WIN32)
    errno = 0;
    CHECK("rt_crt_close(-1) fails EBADF", rt_crt_close(-1) == -1 && errno == EBADF);
    errno = 0;
    CHECK("rt_crt_close(99999) fails EBADF", rt_crt_close(99999) == -1 && errno == EBADF);
#endif

#if defined(_WIN32)
    int raw_fd = rt_crt_open(crt_path, _O_RDWR | _O_CREAT | _O_TRUNC | _O_BINARY,
                             _S_IREAD | _S_IWRITE);
#else
    int raw_fd = rt_crt_open(crt_path, O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
#endif
    CHECK("rt_crt_open succeeds", raw_fd >= 0);
    CHECK("rt_crt_close(raw_fd) succeeds", rt_crt_close(raw_fd) == 0);
#if !defined(_WIN32)
    errno = 0;
    CHECK("rt_crt_close(closed fd) fails EBADF",
          rt_crt_close(raw_fd) == -1 && errno == EBADF);
#endif
    CHECK("rt_crt_unlink removes crt_path", rt_crt_unlink(crt_path) == 0);

    /* 2. rt_file_lock error paths (invalid pointers, empty, missing directory). */
    CHECK("rt_file_lock(NULL, 4, 0) == -1", rt_file_lock(NULL, 4, 0) == -1);
    CHECK("rt_file_lock(\"\", 0, 0) == -1",
          rt_file_lock((const uint8_t*)"", 0, 0) == -1);
    CHECK("rt_file_lock missing dir timeout=0",
          rt_file_lock((const uint8_t*)missing_path,
                       (uint64_t)strlen(missing_path), 0) == -1);
    CHECK("rt_file_lock missing dir timeout=1",
          rt_file_lock((const uint8_t*)missing_path,
                       (uint64_t)strlen(missing_path), 1) == -1);

    /* 3. rt_file_unlock negative-fd safety (guarded before UCRT/OS close). */
    CHECK("rt_file_unlock(-1) == false", !rt_file_unlock(-1));
    CHECK("rt_file_unlock(-42) == false", !rt_file_unlock(-42));
    CHECK("rt_file_unlock(INT_MIN) == false", !rt_file_unlock((int64_t)INT_MIN));
#if !defined(_WIN32)
    CHECK("rt_file_unlock(99999) == false", !rt_file_unlock(99999));
#endif

    /* 4. Uncontended acquire / unlock / reacquire. */
    int64_t h1 = rt_file_lock((const uint8_t*)lock_path,
                              (uint64_t)strlen(lock_path), 0);
    CHECK("uncontended rt_file_lock >= 0", h1 >= 0);
    CHECK("rt_file_unlock(h1) == true", rt_file_unlock(h1));
#if !defined(_WIN32)
    CHECK("double rt_file_unlock(h1) == false", !rt_file_unlock(h1));
#endif

    int64_t holder = rt_file_lock((const uint8_t*)lock_path,
                                  (uint64_t)strlen(lock_path), 0);
    CHECK("reacquire holder >= 0", holder >= 0);

    /* 5. Contended error paths close fd cleanly across repeated tries & timeout expiry. */
    CHECK("contended timeout=0 x32", run_contended_rounds(lock_path, 0, 32, NULL));
    CHECK("contended timeout=-1 x8", run_contended_rounds(lock_path, -1, 8, NULL));
    {
        unsigned long long elapsed_ms = 0;
        CHECK("contended timeout=1 expiry",
              run_contended_rounds(lock_path, 1, 1, &elapsed_ms) &&
              elapsed_ms >= 800 && elapsed_ms < 4000);
    }

#if !defined(_WIN32)
    /* Prove in-process contended rt_file_lock attempts do not leak fds on POSIX. */
    {
        int probe_before = open("/dev/null", O_RDONLY);
        CHECK("open /dev/null before", probe_before >= 0);
        CHECK("close probe_before", rt_crt_close(probe_before) == 0);
        for (int i = 0; i < 32; i++) {
            int64_t contended = rt_file_lock((const uint8_t*)lock_path,
                                             (uint64_t)strlen(lock_path), 0);
            CHECK("in-process contended rt_file_lock == -1", contended == -1);
        }
        int probe_after = open("/dev/null", O_RDONLY);
        CHECK("open /dev/null after", probe_after >= 0);
        CHECK("close probe_after", rt_crt_close(probe_after) == 0);
        CHECK("no in-process fd leak", probe_after == probe_before);
    }
#endif

    CHECK("rt_file_unlock(holder) == true", rt_file_unlock(holder));

    /* 6. Reacquire after holder release & remove lock file (Windows DeleteFileA
     *    additionally fails with ERROR_SHARING_VIOLATION if any CRT fd leaked). */
    int64_t final_lock = rt_file_lock((const uint8_t*)lock_path,
                                      (uint64_t)strlen(lock_path), 0);
    CHECK("reacquire after holder release >= 0", final_lock >= 0);
    CHECK("rt_file_unlock(final_lock) == true", rt_file_unlock(final_lock));
#if defined(_WIN32)
    CHECK("DeleteFileA(lock_path) succeeds", DeleteFileA(lock_path) != 0);
#else
    CHECK("unlink(lock_path) succeeds", unlink(lock_path) == 0);
#endif

    printf("PASS rt_file_lock_crt_close_selfcheck (%u checks)\n", g_checks);
    return 0;
}
