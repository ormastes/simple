/* Authored NOT_RUN. Requires actual Linux user/PID namespace support; denied
 * unshare is failure/blocking evidence, never a skip or synthetic pass.
 * Each case gets a fresh real PID1 process, not a fake getpid provider. */
#if !defined(__linux__)
#error "requires an authorized Linux namespace native test slot"
#endif
#define _GNU_SOURCE 1
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static int namespace_stat_calls;
static int namespace_fault; /* 1 failed stat, 2 changed inode after actual stat */
static int fail_at_namespace_stat;
static int native_owner_closes;
static int origin_stat(struct stat *observed) {
    ++namespace_stat_calls;
    if (namespace_fault == 1 || namespace_stat_calls == fail_at_namespace_stat) {
        errno = ENOENT;
        return -1;
    }
    int result = stat("/proc/self/ns/pid", observed);
    if (result == 0 && namespace_fault == 2) observed->st_ino ^= (ino_t)1;
    return result;
}
static int owner_close(int fd) {
    ++native_owner_closes;
    return close(fd) == 0;
}
#define SPL_OWNED_LOCK_NAMESPACE_STAT_V2(observed) origin_stat(observed)
#define SPL_OWNED_LOCK_CLOSE_V2(fd) owner_close(fd)
#include "../runtime_file_lock_owned_v2.c"

static void bounded_failure(int signal_number) {
    (void)signal_number;
    _exit(124);
}
static int64_t acquire(const char *path) {
    return rt_file_lock_owned_acquire_v2((const uint8_t *)path, strlen(path), 0);
}
static void wait_success(pid_t child) {
    int status;
    assert(waitpid(child, &status, 0) == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
}
static void actual_lock_contended(const char *path) {
    int fd = open(path, O_RDWR | O_CLOEXEC);
    assert(fd >= 0);
    assert(flock(fd, LOCK_EX | LOCK_NB) != 0);
    assert(errno == EAGAIN || errno == EWOULDBLOCK);
    assert(close(fd) == 0);
}
static void unknown_without_effects(int64_t token, const char *path) {
    int closes = native_owner_closes;
    errno = E2BIG;
    assert(rt_file_lock_owned_state_v2(token) == 3);
    assert(rt_file_lock_owned_release_v2(token) == 3);
    assert(acquire(path) == 0);
    assert(errno == E2BIG);
    assert(native_owner_closes == closes);
}

/* Positive established-origin control uses actual syscall 0-success semantics;
 * it must not be satisfied merely because every guarded operation rejects. */
static void ordinary_success_case(const char *path) {
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        signal(SIGALRM, bounded_failure);
        alarm(4);
        int64_t token = acquire(path);
        assert(token > 0);
        errno = E2BIG;
        assert(spl_owned_lock_origin_check_v2() == 1);
        assert(errno == E2BIG);
        assert(rt_file_lock_owned_state_v2(token) == 1);
        assert(rt_file_lock_owned_release_v2(token) == 1);
        _exit(0);
    }
    wait_success(child);
}

/* Both getpid calls are actually 1. Child inherits the parent's actual held
 * gate and token, but its kernel PID namespace object is different. */
static void real_same_pid_namespace_case(const char *path) {
    assert(getpid() == 1);
    int64_t token = acquire(path);
    assert(token > 0 && rt_file_lock_owned_state_v2(token) == 1);
    struct stat parent_namespace;
    assert(stat("/proc/self/ns/pid", &parent_namespace) == 0);
    assert(spl_owned_lock_enter_v2());
    assert(unshare(CLONE_NEWPID) == 0);
    pid_t inner = fork();
    assert(inner >= 0);
    if (inner == 0) {
        signal(SIGALRM, bounded_failure);
        alarm(4);
        assert(getpid() == 1);
        struct stat current_namespace;
        assert(stat("/proc/self/ns/pid", &current_namespace) == 0);
        assert(current_namespace.st_dev != parent_namespace.st_dev ||
               current_namespace.st_ino != parent_namespace.st_ino);
        unknown_without_effects(token, path);
        assert(atomic_load_explicit(&spl_owned_lock_origin_phase_v2, memory_order_acquire) == 3);
        _exit(0);
    }
    wait_success(inner);
    /* Only the unchanged parent releases its own legitimately acquired gate. */
    spl_owned_lock_leave_v2();
    assert(rt_file_lock_owned_release_v2(token) == 1);
}

/* Actual namespace proof is established first. Only the later stat observer
 * is faulted. Restoration must not clear quarantine or enter the held gate. */
static void restored_observation_case(const char *path, int fault) {
    int64_t token = acquire(path);
    assert(token > 0);
    assert(spl_owned_lock_enter_v2());
    namespace_fault = fault;
    assert(rt_file_lock_owned_state_v2(token) == 3);
    namespace_fault = 0;
    struct stat actual;
    assert(stat("/proc/self/ns/pid", &actual) == 0);
    assert(actual.st_dev == spl_owned_lock_origin_device_v2);
    assert(actual.st_ino == spl_owned_lock_origin_inode_v2);
    int reads = namespace_stat_calls;
    unknown_without_effects(token, path);
    assert(namespace_stat_calls == reads); /* sticky refusal, no fresh probe */
    actual_lock_contended(path);
    /* No gate reset or raw-descriptor cleanup. Process death owns final reap. */
}

static void postpoll_origin_loss_case(const char *path) {
    /* Initial proof is the actual fstat/nsfs/ioctl sequence. The first later
     * stat is the initial gate post-check; the second is after actual flock. */
    fail_at_namespace_stat = 2;
    int64_t token = acquire(path);
    assert(token > 0);
    assert(namespace_stat_calls == 2);
    fail_at_namespace_stat = 0;
    SplOwnedLockSlotV2 *slot = spl_owned_lock_find_v2(token);
    assert(slot && atomic_load_explicit(&slot->state, memory_order_acquire) == 3);
    assert(slot->native >= 0); /* actual opened owner retained in canonical slot */
    assert(native_owner_closes == 0);
    unknown_without_effects(token, path);
    actual_lock_contended(path);
}

/* Main process never initializes the registry. Each controller creates a real
 * user/PID namespace, then its first child is actual PID1 with a virgin owner.
 * No /proc remount or caller-provided identity boolean is used. */
static void run_namespace_case(const char *path, int which) {
    pid_t controller = fork();
    assert(controller >= 0);
    if (controller == 0) {
        signal(SIGALRM, bounded_failure);
        alarm(20);
        assert(unshare(CLONE_NEWUSER | CLONE_NEWPID) == 0);
        pid_t init = fork();
        assert(init >= 0);
        if (init == 0) {
            signal(SIGALRM, bounded_failure);
            alarm(12);
            assert(getpid() == 1);
            if (which == 0) real_same_pid_namespace_case(path);
            if (which == 1) restored_observation_case(path, 1);
            if (which == 2) restored_observation_case(path, 2);
            if (which == 3) postpoll_origin_loss_case(path);
            _exit(0);
        }
        wait_success(init);
        _exit(0);
    }
    wait_success(controller);
    /* Observe actual release only after the entire owning process has died. */
    int fd = open(path, O_RDWR | O_CLOEXEC);
    assert(fd >= 0 && flock(fd, LOCK_EX | LOCK_NB) == 0);
    assert(flock(fd, LOCK_UN) == 0 && close(fd) == 0);
}
int main(void) {
    char root[] = "/tmp/simple-lock-origin-XXXXXX";
    assert(mkdtemp(root));
    char path[256];
    assert(snprintf(path, sizeof(path), "%s/parent.lock", root) > 0);
    int fd = open(path, O_RDWR | O_CREAT | O_CLOEXEC, 0600);
    assert(fd >= 0 && close(fd) == 0);
    ordinary_success_case(path);
    for (int which = 0; which < 4; ++which) run_namespace_case(path, which);
    assert(unlink(path) == 0 && rmdir(root) == 0);
    return 0;
}
