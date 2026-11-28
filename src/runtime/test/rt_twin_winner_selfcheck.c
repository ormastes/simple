/* Behaviour that must hold whichever twin body the linker picks.
 *
 * runtime.c (with platform/unix_common.h) and runtime_native.c /
 * runtime_process.c define the same names; on ELF the first object on the link
 * line wins, on Mach-O the SPL_RUNTIME_NATIVE_TWIN copies are weak. Each case
 * below is one the two bodies used to answer differently (audit 2026-11-28).
 * scripts/check/check-runtime-c-twin-bodies.shs links this with runtime.o
 * first and with runtime.o last and requires both to pass. */
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

int64_t rt_string_new(const char* bytes, uint64_t len);
const char* rt_string_data(int64_t value);
int64_t rt_open_fd(int64_t path, int64_t flags, int64_t mode);
const char* rt_file_read_text_at(int64_t path, int64_t offset, int64_t size);
int64_t rt_remove(int64_t path);
int64_t spl_str_ptr(int64_t text);
int64_t rt_fd_write(int64_t fd, const char* data, int64_t len);
bool rt_dir_create_cpath(const char* path, bool recursive);
int64_t rt_file_lock(const char* path_ptr, uint64_t path_len, int64_t timeout_secs);
bool rt_file_unlock(int64_t handle);
int64_t rt_process_wait(int64_t pid, int64_t timeout_ms);
int64_t rt_process_last_child_peak_rss_kib(void);

static int failures = 0;
#define CHECK(cond, label) do { if (!(cond)) { failures++; printf("FAIL %s\n", label); } } while (0)

static void put(const char* path, const char* text) {
    FILE* f = fopen(path, "w");
    if (f) { fputs(text, f); fclose(f); }
}

int main(void) {
    char dir[] = "/tmp/rt_twin_winner_XXXXXX";
    if (!mkdtemp(dir) || chdir(dir) != 0) { printf("FAIL setup\n"); return 2; }
    put("f.txt", "hello world");

    /* A `text` argument reaches these as a tagged value or as its char* bytes,
     * depending on the caller's lowering; both must work. */
    int64_t tagged = rt_string_new("f.txt", 5);
    int64_t bytes = (int64_t)(uintptr_t)rt_string_data(tagged);
    int64_t fd = rt_open_fd(tagged, O_RDONLY, 0);
    CHECK(fd >= 0, "rt_open_fd(tagged text)");
    if (fd >= 0) close((int)fd);
    fd = rt_open_fd(bytes, O_RDONLY, 0);
    CHECK(fd >= 0, "rt_open_fd(text bytes)");
    if (fd >= 0) close((int)fd);
    CHECK(strcmp(rt_file_read_text_at(tagged, 0, 5), "hello") == 0, "rt_file_read_text_at(tagged text)");
    CHECK(strcmp(rt_file_read_text_at(bytes, 6, 5), "world") == 0, "rt_file_read_text_at(text bytes)");
    CHECK(spl_str_ptr(tagged) == bytes, "spl_str_ptr(tagged text) is the byte pointer");
    CHECK(spl_str_ptr(bytes) == bytes, "spl_str_ptr(text bytes) is unchanged");
    put("gone1", "x");
    put("gone2", "x");
    CHECK(rt_remove(rt_string_new("gone1", 5)) == 0 && access("gone1", F_OK) != 0, "rt_remove(tagged text)");
    CHECK(rt_remove((int64_t)(uintptr_t)rt_string_data(rt_string_new("gone2", 5))) == 0 && access("gone2", F_OK) != 0,
          "rt_remove(text bytes)");

    /* An empty write is not an error. */
    int out = open("out", O_CREAT | O_WRONLY, 0644);
    CHECK(rt_fd_write(out, "abc", 0) == 0, "rt_fd_write(len 0) == 0");
    CHECK(rt_fd_write(out, "abc", 3) == 3, "rt_fd_write(len 3) == 3");
    close(out);

    /* mkdir -p: an existing FILE is not a directory; the root is one. */
    CHECK(rt_dir_create_cpath("a/b/c/", true), "rt_dir_create_cpath(nested)");
    CHECK(!rt_dir_create_cpath("f.txt", true), "rt_dir_create_cpath(existing file) is false");
    CHECK(!rt_dir_create_cpath("f.txt/sub", true), "rt_dir_create_cpath(below a file) is false");
    CHECK(rt_dir_create_cpath("/", true), "rt_dir_create_cpath(/) is true");

    /* The lock descriptor must not leak into spawned children. */
    int64_t lock = rt_file_lock("lk", 2, 0);
    CHECK(lock >= 0, "rt_file_lock");
    if (lock >= 0) {
        CHECK((fcntl((int)lock, F_GETFD) & FD_CLOEXEC) != 0, "rt_file_lock descriptor is close-on-exec");
        CHECK(rt_file_unlock(lock), "rt_file_unlock");
    }
    CHECK(!rt_file_unlock(987), "rt_file_unlock(bad descriptor) is false");

    /* rt_process_wait reaps through the owner that records the child's rusage. */
    pid_t child = fork();
    if (child == 0) {
        char* block = (char*)malloc(8 << 20);
        if (block) memset(block, 1, 8 << 20);
        _exit(7);
    }
    CHECK(rt_process_wait(child, 0) == 7, "rt_process_wait exit code");
    CHECK(rt_process_last_child_peak_rss_kib() > 0, "rt_process_wait records the child's peak RSS");

    printf(failures == 0 ? "PASS rt_twin_winner_selfcheck\n" : "FAILED %d check(s)\n", failures);
    return failures == 0 ? 0 : 1;
}
