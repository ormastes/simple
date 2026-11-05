/* Focused behavior check for the hosted runtime-native file owner. */
#include "../runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#if !defined(_WIN32)
#include <errno.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>

static int check(int condition, const char* message) {
    if (condition) return 1;
    fprintf(stderr, "runtime_host_file_exports_selfcheck: %s\n", message);
    return 0;
}

static int check_contended_lock_returns(const char* path, int64_t timeout_secs) {
    pid_t child = fork();
    if (!check(child >= 0, "fork for lock contention failed")) return 0;
    if (child == 0) {
        alarm(2); /* Bound a regression to the old blocking attempt. */
        int64_t contender = rt_file_lock((const uint8_t*)path, strlen(path), timeout_secs);
        if (contender >= 0) {
            rt_file_unlock(contender);
            _exit(2);
        }
        _exit(0);
    }
    int status = 0;
    pid_t waited;
    do {
        waited = waitpid(child, &status, 0);
    } while (waited < 0 && errno == EINTR);
    if (!check(waited == child, "waitpid for lock contender failed")) {
        kill(child, SIGKILL);
        waitpid(child, &status, 0);
        return 0;
    }
    return check(WIFEXITED(status) && WEXITSTATUS(status) == 0,
                 "contended nonpositive-timeout lock did not promptly return -1");
}

int main(void) {
    static const uint8_t payload[] = {0x00, 0x7f, 0x80, 0xff, 0x2a};
    char path[] = "/tmp/simple-host-file-XXXXXX";
    int fd = mkstemp(path);
    if (!check(fd >= 0, "mkstemp failed")) return 1;
    if (!check(write(fd, payload, sizeof(payload)) == (ssize_t)sizeof(payload), "write failed")) return 1;
    if (!check(close(fd) == 0, "close failed")) return 1;

    int64_t bytes = rt_file_mmap_read_bytes((const uint8_t*)path, strlen(path));
    if (!check(bytes != 0, "mapped byte read returned nil")) return 1;
    if (!check(rt_array_bytes_validate(bytes) == (int64_t)sizeof(payload), "byte-array length mismatch")) return 1;
    uint8_t copied[sizeof(payload)];
    if (!check(rt_array_bytes_copy_checked(bytes, copied, sizeof(copied)) == (int64_t)sizeof(copied), "byte copy failed")) return 1;
    if (!check(memcmp(copied, payload, sizeof(payload)) == 0, "binary payload changed")) return 1;
    rt_array_free((SplArray*)(uintptr_t)bytes);

    if (!check(rt_file_fsync((const uint8_t*)path, strlen(path)) == 1, "durable sync failed")) return 1;
    int64_t lock = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (!check(lock >= 0, "zero-timeout uncontended lock failed")) return 1;
    int contention_ok = check_contended_lock_returns(path, 0);
    if (!check_contended_lock_returns(path, -1)) contention_ok = 0;
    if (!check(rt_file_unlock(lock), "unlock failed")) return 1;
    if (!contention_ok) return 1;
    lock = rt_file_lock((const uint8_t*)path, strlen(path), 0);
    if (!check(lock >= 0, "zero-timeout reacquire failed")) return 1;
    if (!check(rt_file_unlock(lock), "reacquired unlock failed")) return 1;

    int64_t tagged_path = rt_string_new((const uint8_t*)path, strlen(path));
    int64_t mapping = rt_mmap(tagged_path, sizeof(payload), 0, 1);
    if (!check(mapping != 0, "raw mmap failed")) return 1;
    if (!check(rt_madvise(mapping, sizeof(payload), 0), "madvise failed")) return 1;
    if (!check(rt_munmap(mapping, sizeof(payload)), "munmap failed")) return 1;
    rt_string_free(tagged_path);

    FILE* empty = fopen(path, "wb");
    if (!check(empty != NULL, "empty-file open failed")) return 1;
    if (!check(fclose(empty) == 0, "empty-file close failed")) return 1;
    int64_t empty_bytes = rt_file_mmap_read_bytes((const uint8_t*)path, strlen(path));
    if (!check(empty_bytes != 0, "valid empty file returned nil")) return 1;
    if (!check(rt_array_bytes_validate(empty_bytes) == 0, "empty array length mismatch")) return 1;
    rt_array_free((SplArray*)(uintptr_t)empty_bytes);

    static const char missing[] = "/tmp/simple-host-file-does-not-exist";
    if (!check(rt_file_mmap_read_bytes((const uint8_t*)missing, sizeof(missing) - 1U) == 0,
               "missing file did not return nil")) return 1;
    unlink(path);
    puts("PASS: runtime host-file owner behavior");
    return 0;
}
#else
int main(void) {
    puts("SKIP: runtime host-file behavior selfcheck is Unix-hosted");
    return 0;
}
#endif
