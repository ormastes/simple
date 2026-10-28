/* Inject kernel boundaries to exercise the real start/collect owner code.
 * This is lifecycle fault evidence, not cgroup containment qualification. */
#define _GNU_SOURCE
#include <assert.h>
#include <stdarg.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/sched.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int fail_clock, clone_calls, clock_calls, reap_ready, fail_remove;
static int wait_calls, blocking_wait_calls;
static const pid_t child_pid = 424242;
static const char *group_files[] = {"memory.max", "memory.swap.max",
    "memory.oom.group", "memory.peak", "memory.current", "cgroup.events",
    "cgroup.kill"};

static void write_leaf(int dir, const char *name, const char *value) {
    int fd = openat(dir, name, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
    assert(fd >= 0);
    assert(write(fd, value, strlen(value)) == (ssize_t)strlen(value));
    assert(close(fd) == 0);
}

static int test_mkdirat(int dir, const char *name, mode_t mode) {
    int result = mkdirat(dir, name, mode);
    if (result || strncmp(name, "simple-native-", 14)) return result;
    int group = openat(dir, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(group >= 0);
    for (size_t i = 0; i < sizeof(group_files) / sizeof(group_files[0]); i++)
        write_leaf(group, group_files[i], !strcmp(group_files[i], "cgroup.events")
            ? "populated 1\n" : "0");
    close(group);
    return 0;
}

static int test_unlinkat(int dir, const char *name, int flags) {
    if (flags == AT_REMOVEDIR && !strncmp(name, "simple-native-", 14)) {
        if (fail_remove) { errno = EBUSY; return -1; }
        int group = openat(dir, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        assert(group >= 0);
        for (size_t i = 0; i < sizeof(group_files) / sizeof(group_files[0]); i++)
            if (unlinkat(group, group_files[i], 0)) assert(errno == ENOENT);
        close(group);
    }
    return unlinkat(dir, name, flags);
}

static int test_clock_gettime(clockid_t clock_id, struct timespec *value) {
    (void)clock_id;
    clock_calls++;
    if (fail_clock) { errno = EIO; return -1; }
    *value = (struct timespec){.tv_sec = 10};
    return 0;
}

static long test_syscall(long number, ...) {
    va_list args;
    va_start(args, number);
    long result = -1;
    if (number == SYS_memfd_create) {
        const char *name = va_arg(args, const char *);
        int flags = va_arg(args, int);
        result = syscall(number, name, flags);
    } else if (number == SYS_clone3) {
        struct clone_args *clone = va_arg(args, struct clone_args *);
        assert(va_arg(args, size_t) == sizeof(*clone));
        assert(clone->flags == (CLONE_PIDFD | CLONE_INTO_CGROUP));
        assert(clone->exit_signal == SIGCHLD);
        assert(fcntl((int)clone->cgroup, F_GETFD) >= 0);
        *(int *)(uintptr_t)clone->pidfd = open("/dev/null", O_RDONLY | O_CLOEXEC);
        assert(*(int *)(uintptr_t)clone->pidfd >= 0);
        clone_calls++;
        result = child_pid;
    } else {
        assert(!"unexpected syscall in start ownership fixture");
    }
    va_end(args);
    return result;
}

static pid_t test_waitpid(pid_t pid, int *status, int options) {
    assert(pid == child_pid);
    wait_calls++;
    if (!(options & WNOHANG)) blocking_wait_calls++;
    if (status) *status = 0;
    return reap_ready || !(options & WNOHANG) ? child_pid : 0;
}

#define clock_gettime test_clock_gettime
#define syscall test_syscall
#define mkdirat test_mkdirat
#define unlinkat test_unlinkat
#define waitpid test_waitpid
#define main unavailable_fixture_main
#include "runtime_linux_group_owner_unavailable_selfcheck.c"
#undef main
#undef waitpid
#undef unlinkat
#undef mkdirat
#undef syscall
#undef clock_gettime

static void free_receipt(SplArray *receipt) {
    free(receipt->items); free(receipt);
}

static SplArray *start(const char *root, const char *identity) {
    char out[4096], err[4096];
    snprintf(out, sizeof(out), "%s/stdout", root);
    snprintf(err, sizeof(err), "%s/stderr", root);
    SplArray empty = {0};
    return rt_linux_group_start_v1("/bin/true", 9, identity, 64,
        &empty, &empty, root, strlen(root), root, strlen(root), identity, 64,
        1048576, 1000, out, strlen(out), err, strlen(err));
}

static void assert_owned(int parent, int group, int pidfd) {
    assert(rt_linux_group.active && !rt_linux_group.collected);
    assert(rt_linux_group.pid == child_pid);
    assert(rt_linux_group.parent_fd == parent && rt_linux_group.group_fd == group);
    assert(rt_linux_group.pidfd == pidfd);
    assert(fcntl(parent, F_GETFD) >= 0);
    assert(fcntl(group, F_GETFD) >= 0);
    assert(fcntl(pidfd, F_GETFD) >= 0);
}

static void check_cleanup_retry(int cancel) {
    char root[] = "/tmp/simple-group-retry-XXXXXX";
    assert(mkdtemp(root));
    int parent = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(parent >= 0 && test_mkdirat(parent, "simple-native-retry", 0700) == 0);
    int group = openat(parent, "simple-native-retry", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    int pidfd = open("/dev/null", O_RDONLY | O_CLOEXEC);
    assert(group >= 0 && pidfd >= 0);
    rt_linux_group = (RtLinuxGroup){.active=1, .parent_fd=parent, .group_fd=group,
        .pidfd=pidfd, .pid=child_pid, .started_ms=9000,
        .timeout_ms=cancel ? 0 : 1000};
    strcpy(rt_linux_group.name, "simple-native-retry");
    reap_ready = 0;
    assert(unlinkat(group, "cgroup.kill", 0) == 0);
    if (cancel) assert(rt_linux_group_cancel_v1(1) == ENOENT);
    /* A persistent failure remains an error on every poll/collect. Neither
     * the timeout flag nor cancellation intent means kill was delivered. */
    for (int attempt = 0; attempt < 3; attempt++) {
        SplArray *receipt = attempt == 1 ? rt_linux_group_collect_v1(1)
            : rt_linux_group_poll_v1(1);
        assert(receipt->items[0].as_int == ENOENT);
        assert(receipt->items[1].as_int == 0 && receipt->items[2].as_int == 0);
        assert(receipt->items[3].as_int == 0 && receipt->items[4].as_int == 1);
        assert(receipt->items[6].as_int == !cancel);
        assert(receipt->items[7].as_int == cancel);
        free_receipt(receipt);
        assert_owned(parent, group, pidfd);
    }
    /* Recovery retries without a second cancel request or resetting timeout. */
    write_leaf(group, "cgroup.kill", "0");
    SplArray *receipt = rt_linux_group_poll_v1(1);
    assert(receipt->items[0].as_int == 0 && receipt->items[1].as_int == 0);
    free_receipt(receipt);
    char killed[8];
    assert(rt_lg_read_at(group, "cgroup.kill", killed, sizeof(killed)));
    assert(!strcmp(killed, "1"));
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == EBUSY && receipt->items[1].as_int == 0);
    free_receipt(receipt);
    reap_ready = 1;
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == EBUSY && receipt->items[1].as_int == 0);
    free_receipt(receipt);
    assert_owned(parent, group, pidfd);
    write_leaf(group, "cgroup.events", "populated 0\n");
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == 0 && receipt->items[1].as_int == 1);
    assert(receipt->items[6].as_int == !cancel && receipt->items[7].as_int == cancel);
    free_receipt(receipt);
    assert(rt_linux_group.collected && blocking_wait_calls == 0);
    assert(fcntl(parent, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(group, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(pidfd, F_GETFD) == -1 && errno == EBADF);
    assert(rmdir(root) == 0);
    rt_linux_group = (RtLinuxGroup){0};
    reap_ready = 0;
    wait_calls = 0;
}

/* Descendant retirement cannot wait for unrelated resource telemetry. */
static void check_cleanup_telemetry_failure(const char *metric, int missing) {
    char root[] = "/tmp/simple-group-telemetry-XXXXXX";
    assert(mkdtemp(root));
    int parent = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(parent >= 0 && test_mkdirat(parent, "simple-native-telemetry", 0700) == 0);
    int group = openat(parent, "simple-native-telemetry", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    int pidfd = open("/dev/null", O_RDONLY | O_CLOEXEC);
    assert(group >= 0 && pidfd >= 0);
    rt_linux_group = (RtLinuxGroup){.active=1, .parent_fd=parent, .group_fd=group,
        .pidfd=pidfd, .pid=child_pid, .started_ms=10000, .timeout_ms=1000};
    strcpy(rt_linux_group.name, "simple-native-telemetry");
    reap_ready = 1;
    if (missing) assert(unlinkat(group, metric, 0) == 0);
    else write_leaf(group, metric, "invalid");
    SplArray *receipt = rt_linux_group_poll_v1(1);
    assert(receipt->items[0].as_int == EIO);
    assert(receipt->items[1].as_int == 0 && receipt->items[2].as_int == 1);
    assert(receipt->items[3].as_int == 0 && receipt->items[6].as_int == 0);
    free_receipt(receipt);
    char killed[8];
    assert(rt_lg_read_at(group, "cgroup.kill", killed, sizeof(killed)));
    assert(!strcmp(killed, "1"));
    assert_owned(parent, group, pidfd);
    /* Telemetry failure still blocks collection, even after population drops. */
    write_leaf(group, "cgroup.events", "populated 0\n");
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == EIO && receipt->items[1].as_int == 0);
    free_receipt(receipt);
    assert_owned(parent, group, pidfd);
    write_leaf(group, metric, "0");
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == 0 && receipt->items[1].as_int == 1);
    free_receipt(receipt);
    assert(rt_linux_group.collected && blocking_wait_calls == 0);
    assert(fcntl(parent, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(group, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(pidfd, F_GETFD) == -1 && errno == EBADF);
    assert(rmdir(root) == 0);
    rt_linux_group = (RtLinuxGroup){0};
    reap_ready = 0;
    wait_calls = 0;
}

int main(void) {
    check_cleanup_telemetry_failure("memory.current", 0);
    check_cleanup_telemetry_failure("memory.current", 1);
    check_cleanup_telemetry_failure("memory.peak", 0);
    check_cleanup_telemetry_failure("memory.peak", 1);
    check_cleanup_retry(0);
    check_cleanup_retry(1);
    char root[] = "/tmp/simple-group-start-XXXXXX";
    assert(mkdtemp(root));
    int root_fd = open(root, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(root_fd >= 0 && mkdirat(root_fd, "parent", 0700) == 0);
    int parent = openat(root_fd, "parent", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(parent >= 0);
    write_leaf(parent, "cgroup.subtree_control", "memory\n");
    struct stat info;
    assert(fstat(parent, &info) == 0);
    char identity[65]; memset(identity, '0', 64); identity[64] = 0;
    rt_lg_delegation.active = 1;
    rt_lg_delegation.root_fd = root_fd; rt_lg_delegation.parent_fd = parent;
    rt_lg_delegation.device = info.st_dev; rt_lg_delegation.inode = info.st_ino;
    strcpy(rt_lg_delegation.name, "parent");
    strcpy(rt_lg_delegation.attempt, root); strcpy(rt_lg_delegation.identity, identity);

    /* A failed clock must reject BEFORE execution, with no blocking reap. */
    fail_clock = 1;
    SplArray *receipt = start(root, identity);
    assert(receipt->items[0].as_int == 0 && receipt->items[1].as_int == EIO);
    assert(clone_calls == 0 && blocking_wait_calls == 0);
    assert(!rt_linux_group.active);
    free_receipt(receipt);
    /* The preflight may have created exclusive output files. */
    unlinkat(root_fd, "stdout", 0); unlinkat(root_fd, "stderr", 0);

    fail_clock = 0;
    int before_clock = clock_calls;
    receipt = start(root, identity);
    assert(receipt->items[0].as_int == 1 && receipt->items[1].as_int == 0);
    assert(clone_calls == 1 && clock_calls == before_clock + 1);
    assert(wait_calls == 0);
    free_receipt(receipt);
    int owned_parent = rt_linux_group.parent_fd, group = rt_linux_group.group_fd;
    int pidfd = rt_linux_group.pidfd;
    assert_owned(owned_parent, group, pidfd);

    /* Failed kill and failed collection retain every ownership handle. */
    assert(unlinkat(group, "cgroup.kill", 0) == 0);
    assert(rt_linux_group_cancel_v1(1) == ENOENT);
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == ENOENT);
    free_receipt(receipt);
    assert_owned(owned_parent, group, pidfd);
    assert(rt_linux_group_parent_release_v1(rt_lg_delegation.token) == EBUSY);

    write_leaf(group, "cgroup.kill", "0");
    assert(rt_linux_group_cancel_v1(1) == 0);
    reap_ready = 1;
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == EBUSY); /* leader alone is not proof */
    free_receipt(receipt);
    assert_owned(owned_parent, group, pidfd);
    write_leaf(group, "cgroup.events", "populated 0\n");
    fail_remove = 1;
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == EBUSY);
    free_receipt(receipt);
    assert_owned(owned_parent, group, pidfd);
    fail_remove = 0;
    receipt = rt_linux_group_collect_v1(1);
    assert(receipt->items[0].as_int == 0 && receipt->items[1].as_int == 1);
    free_receipt(receipt);
    assert(rt_linux_group.collected && blocking_wait_calls == 0);
    assert(fcntl(owned_parent, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(group, F_GETFD) == -1 && errno == EBADF);
    assert(fcntl(pidfd, F_GETFD) == -1 && errno == EBADF);
    assert(unlinkat(parent, "cgroup.subtree_control", 0) == 0);
    assert(rt_linux_group_parent_release_v1(rt_lg_delegation.token) == 0);
    char out[4096], err[4096];
    snprintf(out, sizeof(out), "%s/stdout", root); unlink(out);
    snprintf(err, sizeof(err), "%s/stderr", root); unlink(err);
    assert(rmdir(root) == 0);
    puts("runtime_linux_group_start_ownership: PASS (injected lifecycle only)");
    return 0;
}
