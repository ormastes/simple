/* UNEXECUTED: includes the actual proposed owner. Faults intercept OS calls;
 * no process/stream implementation is copied into this test.
 * Run in a fresh subprocess with an outer 15-second timeout. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static atomic_int fail_nonblock_countdown;
static atomic_int fail_write_eintr;
static atomic_int fail_wait_eintr;
static atomic_int failed_kill_count;
static atomic_int kill_failure_pid;
static atomic_int held_wait_pid;
static atomic_int wait_entered;
static atomic_int wait_release;
static atomic_int hold_sleep;
static atomic_int sleep_entered;
static atomic_int sleep_release;
static atomic_int check_unlocked_sleep;
static atomic_int unlocked_sleep_observed;
static void assert_registry_unlocked(void);

static int fault_fcntl(int fd, int command, ...) {
    if (command == F_GETFL || command == F_GETFD) return fcntl(fd, command);
    va_list args; va_start(args, command); int value = va_arg(args, int); va_end(args);
    if (command == F_SETFL && (value & O_NONBLOCK) &&
        atomic_load(&fail_nonblock_countdown) > 0 &&
        atomic_fetch_sub(&fail_nonblock_countdown, 1) == 1) {
        errno = EIO; return -1;
    }
    return fcntl(fd, command, value);
}
static ssize_t fault_write(int fd, const void* data, size_t length) {
    if (atomic_exchange(&fail_write_eintr, 0)) { errno = EINTR; return -1; }
    return write(fd, data, length);
}
static int fault_kill(pid_t pid, int signal_number) {
    int selected = atomic_load(&kill_failure_pid);
    if (selected > 0 && pid == -selected && signal_number == SIGKILL &&
        atomic_compare_exchange_strong(&kill_failure_pid, &selected, 0)) {
        atomic_fetch_add(&failed_kill_count, 1); errno = EPERM; return -1;
    }
    return kill(pid, signal_number);
}
static pid_t fault_waitpid(pid_t pid, int* status, int options) {
    if (atomic_exchange(&fail_wait_eintr, 0)) { errno = EINTR; return -1; }
    if (pid == atomic_load(&held_wait_pid) && (options & WNOHANG)) {
        atomic_store(&wait_entered, 1);
        while (!atomic_load(&wait_release)) {
            struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
        }
    }
    return waitpid(pid, status, options);
}
static int fault_nanosleep(const struct timespec* delay, struct timespec* remaining) {
    if (atomic_load(&check_unlocked_sleep)) {
        assert_registry_unlocked(); atomic_fetch_add(&unlocked_sleep_observed, 1);
    }
    if (atomic_load(&hold_sleep)) {
        atomic_store(&sleep_entered, 1);
        while (!atomic_load(&sleep_release)) {
            struct timespec short_delay = {0, 1000000}; nanosleep(&short_delay, NULL);
        }
    }
    return nanosleep(delay, remaining);
}
#define fcntl fault_fcntl
#define write fault_write
#define kill fault_kill
#define waitpid fault_waitpid
#define nanosleep fault_nanosleep
#include "../../../src/runtime/runtime_process.c"
#undef fcntl
#undef write
#undef kill
#undef waitpid
#undef nanosleep
/* Fixture failures clean up only the child PIDs this fixture created. */
#undef assert
#define assert(condition) do { if (!(condition)) { \
    fprintf(stderr, "assertion failed at %d: %s\n", __LINE__, #condition); exit(1); \
} } while (0)

static void assert_registry_unlocked(void) {
    assert(pthread_mutex_trylock(&s_proc_lock) == 0);
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
}
static int64_t children[16];
static void cleanup_children(void) {
    atomic_store(&sleep_release, 1); atomic_store(&hold_sleep, 0);
    atomic_store(&wait_release, 1); atomic_store(&held_wait_pid, 0);
    atomic_store(&kill_failure_pid, 0);
    for (size_t i = 0; i < 16; ++i) if (children[i] > 0) {
        (void)rt_process_close_piped(children[i]); children[i] = 0;
    }
}
static int64_t child(const char* command) {
    char* args[] = {"sh", "-c", (char*)command, NULL};
    int64_t pid = rt_process_spawn_piped_argv("/bin/sh", args, false, -1);
    assert(pid > 0);
    for (size_t i = 0; i < 16; ++i) if (!children[i]) { children[i] = pid; return pid; }
    assert(!"test child registry full"); return -1;
}
static void close_child(int64_t pid) {
    assert(rt_process_close_piped(pid));
    for (size_t i = 0; i < 16; ++i) if (children[i] == pid) children[i] = 0;
}
static void pause_ms(void) { struct timespec d = {0, 1000000}; nanosleep(&d, NULL); }
static void wait_dead(int64_t pid) {
    for (int i = 0; i < 3000; ++i) {
        if (!rt_process_is_alive(pid)) return;
        pause_ms();
    }
    assert(!"child did not exit");
}
static void drain_exact(int64_t pid, const char* expected) {
    char out[128] = {0}; size_t used = 0; bool eof = false;
    for (int i = 0; i < 3000; ++i) {
        const char* chunk = rt_process_read_stdout(pid); size_t length = strlen(chunk);
        assert(used + length < sizeof(out)); memcpy(out + used, chunk, length); used += length;
        int64_t state = rt_process_stdout_state(pid); assert(state >= 0);
        if (state == 1) { eof = true; break; }
        pause_ms();
    }
    assert(eof && used == strlen(expected) && memcmp(out, expected, used) == 0);
}
static void* close_thread(void* arg) {
    int64_t pid = *(int64_t*)arg;
    return (void*)(uintptr_t)(rt_process_close_piped(pid) ? 1 : 0);
}

static void* writer_thread(void* arg) {
    int64_t pid = *(int64_t*)arg;
    return (void*)(uintptr_t)(rt_process_write_stdin(pid, "must-not-reach-reused-fd") ? 1 : 0);
}

int main(void) {
    assert(atexit(cleanup_children) == 0);
    /* Fail the stdout nonblocking transition: no child or reserved slot escapes. */
    atomic_store(&fail_nonblock_countdown, 2);
    char* args[] = {"sh", "-c", "exit 0", NULL};
    assert(rt_process_spawn_piped_argv("/bin/sh", args, false, -1) == -1);
    assert(atomic_load(&fail_nonblock_countdown) == 0);
    for (int i = 0; i < RT_PROC_MAX; ++i) assert(s_procs[i].pid == 0);

    int64_t pid = child("printf '\\342\\202'");
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    struct RtProcSlot* slot = proc_find((pid_t)pid); assert(slot);
    assert((fcntl(slot->stdin_fd, F_GETFL) & O_NONBLOCK) != 0);
    assert((fcntl(slot->stdout_fd, F_GETFL) & O_NONBLOCK) != 0);
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    wait_dead(pid); drain_exact(pid, "\xef\xbf\xbd"); close_child(pid);

    /* A failed first group cleanup cannot permanently strand the reaped slot. */
    pid = child("exit 0"); atomic_store(&kill_failure_pid, (int)pid);
    wait_dead(pid); assert(atomic_load(&failed_kill_count) == 1);
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    slot = proc_find((pid_t)pid); assert(slot && slot->leader_reaped && !slot->tree_stopped);
    int old_stdin = slot->stdin_fd, old_stdout = slot->stdout_fd;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    close_child(pid);
    errno = 0; assert(fcntl(old_stdin, F_GETFD) == -1 && errno == EBADF);
    errno = 0; assert(fcntl(old_stdout, F_GETFD) == -1 && errno == EBADF);

    /* Real close is held inside waitpid; unrelated operations must still progress. */
    pid = child("sleep 5"); int64_t other = child("sleep 5");
    atomic_store(&held_wait_pid, (int)pid);
    pthread_t thread; assert(pthread_create(&thread, NULL, close_thread, &pid) == 0);
    for (int i = 0; i < 3000 && !atomic_load(&wait_entered); ++i) pause_ms();
    assert(atomic_load(&wait_entered)); assert_registry_unlocked();
    assert(rt_process_stdout_state(other) == 0);
    assert(strcmp(rt_process_read_stdout(other), "") == 0);
    assert(rt_process_stdout_state(pid) == -1); /* explicit close owns/discards stream */
    assert(!rt_process_close_piped(pid)); /* no second cleanup owner */
    atomic_store(&wait_release, 1); void* result = NULL;
    assert(pthread_join(thread, &result) == 0 && (uintptr_t)result == 1);
    for (size_t i = 0; i < 16; ++i) if (children[i] == pid) children[i] = 0;
    atomic_store(&held_wait_pid, 0); close_child(other);

    /* Interrupted write restores the signal mask and yields outside the mutex. */
    pid = child("IFS= read -r x; printf '%s' \"$x\"");
    sigset_t before, after; assert(pthread_sigmask(SIG_SETMASK, NULL, &before) == 0);
    atomic_store(&fail_write_eintr, 1);
    assert(rt_process_write_stdin_some(pid, "z\n", 2, 0, 2) == 0);
    assert(pthread_sigmask(SIG_SETMASK, NULL, &after) == 0);
    assert(sigismember(&before, SIGPIPE) == sigismember(&after, SIGPIPE));
    atomic_store(&check_unlocked_sleep, 1); atomic_store(&fail_write_eintr, 1);
    assert(rt_process_write_stdin(pid, "z\n"));
    assert(atomic_load(&unlocked_sleep_observed) >= 1);
    atomic_store(&check_unlocked_sleep, 0);
    wait_dead(pid); drain_exact(pid, "z"); close_child(pid);

    pid = child("sleep 5"); atomic_store(&fail_wait_eintr, 1);
    atomic_store(&unlocked_sleep_observed, 0); atomic_store(&check_unlocked_sleep, 1);
    assert(rt_process_is_alive(pid)); assert(atomic_load(&unlocked_sleep_observed) == 1);
    atomic_store(&check_unlocked_sleep, 0); close_child(pid);
    assert(!rt_process_write_stdin(pid, ""));
    assert(rt_process_write_stdin_some(pid, "", 0, 0, 1) == -1);

    /* Hold a real full writer between interrupted write attempts. Close its
     * child, reuse the exact descriptor number, and verify no bytes escape. */
    pid = child("sleep 5");
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    slot = proc_find((pid_t)pid); assert(slot); int reused_fd = slot->stdin_fd;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    atomic_store(&fail_write_eintr, 1); atomic_store(&hold_sleep, 1);
    assert(pthread_create(&thread, NULL, writer_thread, &pid) == 0);
    for (int i = 0; i < 3000 && !atomic_load(&sleep_entered); ++i) pause_ms();
    assert(atomic_load(&sleep_entered)); assert_registry_unlocked(); close_child(pid);
    int replacement[2]; assert(pipe(replacement) == 0);
    if (replacement[0] == reused_fd) {
        int moved = fcntl(replacement[0], F_DUPFD, reused_fd + 1); assert(moved >= 0);
        assert(close(replacement[0]) == 0); replacement[0] = moved;
    }
    if (replacement[1] != reused_fd) {
        assert(dup2(replacement[1], reused_fd) == reused_fd);
        assert(close(replacement[1]) == 0); replacement[1] = reused_fd;
    }
    int read_flags = fcntl(replacement[0], F_GETFL); assert(read_flags >= 0);
    assert(fcntl(replacement[0], F_SETFL, read_flags | O_NONBLOCK) == 0);
    atomic_store(&sleep_release, 1); result = NULL;
    assert(pthread_join(thread, &result) == 0 && (uintptr_t)result == 0);
    atomic_store(&hold_sleep, 0);
    char leaked; errno = 0;
    assert(read(replacement[0], &leaked, 1) == -1 && (errno == EAGAIN || errno == EWOULDBLOCK));
    assert(close(replacement[0]) == 0); assert(close(replacement[1]) == 0);

    /* No private identity wraps, even when all slots are free. */
    assert(pthread_mutex_lock(&s_proc_lock) == 0);
    uint64_t saved = s_proc_generation; s_proc_generation = UINT64_MAX;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    assert(proc_alloc(false) == NULL);
    assert(pthread_mutex_lock(&s_proc_lock) == 0); s_proc_generation = saved;
    assert(pthread_mutex_unlock(&s_proc_lock) == 0);
    puts("posix lifecycle source fixture PASS");
    return 0;
}
