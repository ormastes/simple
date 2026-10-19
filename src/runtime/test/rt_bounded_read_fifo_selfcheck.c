/* Link the actual C provider, never a copied reader. TEXT_ONLY selects runtime.c;
 * the default selects runtime_native.c's text and byte-array entry points.
 * Usage: rt_bounded_read_fifo_selfcheck SCRATCH_PARENT
 * Each case has a child alarm and an independent parent deadline. A blocking
 * pre-fix FIFO open must fail, without hanging the test runner. */
#define _POSIX_C_SOURCE 200809L
#ifdef NDEBUG
#error "This contract requires enabled assertions"
#endif
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

extern int64_t rt_file_read_regular_no_follow_bounded(const uint8_t*, uint64_t, int64_t);
extern int64_t rt_file_read_regular_no_follow_last_failure(void);
extern int64_t rt_string_len(int64_t);
extern const uint8_t* rt_string_data(int64_t);
#ifndef TEXT_ONLY
typedef struct SplArray SplArray;
extern int64_t rt_file_read_regular_no_follow_bounded_bytes(const uint8_t*, uint64_t, int64_t);
extern int64_t rt_array_bytes_basis_len(SplArray*);
extern int64_t rt_array_bytes_basis_ptr(SplArray*);
#endif

struct read_case {
    const char* label;
    const char* path;
    int64_t limit;
    int64_t failure; /* 100 means success; existing C refusal codes otherwise. */
    const uint8_t* bytes;
    size_t length;
};

static int64_t milliseconds(void) {
    struct timespec now;
    assert(clock_gettime(CLOCK_MONOTONIC, &now) == 0);
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static void check_read(const struct read_case* item, int binary) {
    int64_t result;
#ifndef TEXT_ONLY
    if (binary) {
        result = rt_file_read_regular_no_follow_bounded_bytes(
            (const uint8_t*)item->path, strlen(item->path), item->limit);
    } else
#else
    (void)binary;
#endif
    {
        result = rt_file_read_regular_no_follow_bounded(
            (const uint8_t*)item->path, strlen(item->path), item->limit);
    }
    assert(rt_file_read_regular_no_follow_last_failure() == item->failure);
    if (item->failure != 100) {
        assert(result == 3);
        return;
    }
    assert(result != 3);
    int64_t length;
    const uint8_t* data;
#ifndef TEXT_ONLY
    if (binary) {
        length = rt_array_bytes_basis_len((SplArray*)(uintptr_t)result);
        data = (const uint8_t*)(uintptr_t)rt_array_bytes_basis_ptr((SplArray*)(uintptr_t)result);
    } else
#endif
    {
        length = rt_string_len(result);
        data = rt_string_data(result);
    }
    assert(length == (int64_t)item->length);
    assert(item->length == 0 || (data && memcmp(data, item->bytes, item->length) == 0));
    /* The child exits immediately; the OS reclaims the result allocation. */
}

static int run_case(const struct read_case* item, int binary) {
    const int64_t deadline = milliseconds() + 3000;
    pid_t child = fork();
    if (child < 0) { perror("fork"); return 0; }
    if (child == 0) {
        sigset_t signals;
        assert(sigemptyset(&signals) == 0);
        assert(sigaddset(&signals, SIGALRM) == 0);
        assert(sigprocmask(SIG_UNBLOCK, &signals, NULL) == 0);
        assert(signal(SIGALRM, SIG_DFL) != SIG_ERR);
        alarm(2);
        check_read(item, binary);
        _exit(0);
    }
    int status = 0;
    for (;;) {
        pid_t waited = waitpid(child, &status, WNOHANG);
        if (waited == child) break;
        if ((waited < 0 && errno != EINTR) || milliseconds() >= deadline) {
            (void)kill(child, SIGKILL);
            while (waitpid(child, &status, 0) < 0 && errno == EINTR) {}
            fprintf(stderr, "FAIL %s %s: parent deadline/wait error\n",
                binary ? "bytes" : "text", item->label);
            return 0;
        }
        const struct timespec pause = {0, 10000000};
        (void)nanosleep(&pause, NULL);
    }
    int ok = WIFEXITED(status) && WEXITSTATUS(status) == 0;
    printf("%s %s %s (wait_status=%d)\n", ok ? "PASS" : "FAIL",
        binary ? "bytes" : "text", item->label, status);
    fflush(stdout);
    return ok;
}

static int put_file(const char* path, const uint8_t* bytes, size_t length) {
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
    if (fd < 0) return 0;
    size_t written = 0;
    while (written < length) {
        ssize_t count = write(fd, bytes + written, length - written);
        if (count < 0 && errno == EINTR) continue;
        if (count <= 0) { close(fd); return 0; }
        written += (size_t)count;
    }
    return close(fd) == 0;
}

int main(int argc, char** argv) {
    if (argc != 2) { fprintf(stderr, "usage: %s SCRATCH_PARENT\n", argv[0]); return 2; }
    char root[4000], fifo[4096], regular[4096], empty[4096], link[4096];
    int size = snprintf(root, sizeof(root), "%s/bounded-fifo.XXXXXX", argv[1]);
    if (size < 0 || size >= (int)sizeof(root) || !mkdtemp(root)) {
        fprintf(stderr, "cannot create private fixture root\n"); return 2;
    }
    snprintf(fifo, sizeof(fifo), "%s/fifo", root);
    snprintf(regular, sizeof(regular), "%s/regular", root);
    snprintf(empty, sizeof(empty), "%s/empty", root);
    snprintf(link, sizeof(link), "%s/link", root);
    const uint8_t content[] = {'a', 0, 0xc3, 0xa9}; /* Counted NUL + valid UTF-8. */
    int result = 2;
    if (mkfifo(fifo, 0600) != 0 || !put_file(regular, content, sizeof(content)) ||
        !put_file(empty, NULL, 0) || symlink("regular", link) != 0) {
        perror("fixture creation"); goto cleanup;
    }
    const struct read_case cases[] = {
        {"FIFO without writer", fifo, 16, 5, NULL, 0},
        {"FIFO zero limit", fifo, 0, 5, NULL, 0},
        {"ordinary counted UTF-8/NUL", regular, 4, 100, content, 4},
        {"empty zero limit", empty, 0, 100, NULL, 0},
        {"oversize refusal", regular, 3, 5, NULL, 0},
        {"symlink refusal", link, 16, 4, NULL, 0},
        {"directory refusal", root, 16, 5, NULL, 0}
    };
    unsigned passed = 0, count = 0;
#ifdef TEXT_ONLY
    const int lanes = 1;
#else
    const int lanes = 2;
#endif
    for (int binary = 0; binary < lanes; binary++) {
        for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
            passed += (unsigned)run_case(&cases[i], binary);
            count++;
        }
    }
    printf("%s bounded FIFO provider contract: %u/%u cases\n",
        passed == count ? "PASS" : "FAIL", passed, count);
    result = passed == count ? 0 : 1;
cleanup:
    if (unlink(link) != 0 && errno != ENOENT) result = 2;
    if (unlink(empty) != 0 && errno != ENOENT) result = 2;
    if (unlink(regular) != 0 && errno != ENOENT) result = 2;
    if (unlink(fifo) != 0 && errno != ENOENT) result = 2;
    if (rmdir(root) != 0) result = 2;
    return result;
}
