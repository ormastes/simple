/* Native Darwin snapshot process foundation.
 *
 * Scope: a cooperative caller owns this object exclusively, including wait4.
 * SIGCHLD must remain waitable (no SIG_IGN/SA_NOCLDWAIT or foreign reaper).
 * The image is either a cooperative snapshot or an explicitly AMFI-bound image.
 * This process component is NOT a sealed V4 provider. Group
 * retirement covers members that stay in the created process group. A child
 * may escape with setsid/setpgid; this is NOT strict descendant containment.
 * No V4 capabilities are advertised by this component.
 */
#ifndef RUNTIME_SOSIX_DARWIN_PROCESS_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_PROCESS_PRIVATE_H
#ifdef __APPLE__
#include "runtime_sosix_darwin_image_private.h"
#include <signal.h>
#include <poll.h>
#include <sys/sysctl.h>
#include <sys/proc.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <time.h>
#ifndef SOSIX_DARWIN_PROCESS_READ
#define SOSIX_DARWIN_PROCESS_READ read
#endif

typedef struct {
    int64_t wall_ns, term_grace_ns, cleanup_ns;
    size_t stdout_limit, stderr_limit;
} SosixDarwinProcessLimits;

typedef struct {
    uint64_t generation;
    pid_t pid;
    int stdout_fd, stderr_fd;
    unsigned char *stdout_bytes, *stderr_bytes;
    size_t stdout_kept, stderr_kept;
    uint64_t stdout_seen, stderr_seen;
    SosixDarwinProcessLimits limits;
    int64_t execution_deadline, kill_deadline, cleanup_deadline;
    int term_sent, kill_sent, timed_out, cancel_requested;
    int leader_exited, reaped, group_retired, frozen, wait_status;
    int stdout_error, stderr_error, cleanup_error;
    struct rusage usage;
} SosixDarwinProcess;

static int64_t sosix_darwin_process_now(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t)) return -1;
    if (t.tv_sec < 0 || t.tv_sec > INT64_MAX / 1000000000LL) return -1;
    return (int64_t)t.tv_sec * 1000000000LL + t.tv_nsec;
}

static int sosix_darwin_process_pipe(int fds[2]) {
    if (pipe(fds)) return errno;
    for (int i = 0; i < 2; i++) {
        if (fcntl(fds[i], F_SETFD, FD_CLOEXEC) < 0) {
            int e = errno; close(fds[0]); close(fds[1]); fds[0] = fds[1] = -1; return e;
        }
    }
    if (fcntl(fds[0], F_SETFL, O_NONBLOCK) < 0) {
        int e = errno; close(fds[0]); close(fds[1]); fds[0] = fds[1] = -1; return e;
    }
    return 0;
}

/* The unreaped leader pins the group ID throughout every snapshot and signal.
 * Exclude zombies: they cannot execute or hold capture descriptors. Snapshot
 * failure never means absence. Bound allocation/retries under process churn. */
static int sosix_darwin_process_group_live(pid_t group, size_t *live) {
    int mib[4] = {CTL_KERN, KERN_PROC, KERN_PROC_PGRP, group};
    for (int attempt = 0; attempt < 3; attempt++) {
        size_t bytes = 0;
        if (sysctl(mib, 4, NULL, &bytes, NULL, 0)) return errno;
        if (bytes > 16U * 1024U * 1024U) return EOVERFLOW;
        size_t capacity = bytes + 32 * sizeof(struct kinfo_proc);
        struct kinfo_proc *processes = malloc(capacity);
        if (!processes) return ENOMEM;
        bytes = capacity;
        if (sysctl(mib, 4, processes, &bytes, NULL, 0)) {
            int e = errno; free(processes); if (e == ENOMEM) continue; return e;
        }
        if (bytes % sizeof(*processes)) { free(processes); return EPROTO; }
        size_t count = 0;
        for (size_t i = 0; i < bytes / sizeof(*processes); i++)
            if (processes[i].kp_proc.p_stat != SZOMB) count++;
        free(processes); *live = count; return 0;
    }
    return EAGAIN;
}

static int sosix_darwin_process_start(SosixDarwinProcess *owner,
        SosixDarwinImage *image, uint64_t image_generation, int cwd_fd,
        char *const argv[], char *const environment[], SosixDarwinProcessLimits limits) {
    if (!owner || !argv || !argv[0] || !environment || cwd_fd < 0 ||
        limits.wall_ns < 0 || limits.term_grace_ns < 0 || limits.cleanup_ns <= 0 ||
        limits.stdout_limit > 16U * 1024U * 1024U || limits.stderr_limit > 16U * 1024U * 1024U)
        return EINVAL;
    int64_t now = sosix_darwin_process_now();
    if (now < 0) return EIO;
    if (limits.wall_ns > INT64_MAX - now ||
        limits.term_grace_ns > INT64_MAX - now - limits.wall_ns ||
        limits.cleanup_ns > INT64_MAX - now - limits.wall_ns - limits.term_grace_ns)
        return EOVERFLOW;
    /* Caller must supply a fresh object, and must not copy an active owner. */
    memset(owner, 0, sizeof(*owner)); owner->stdout_fd = owner->stderr_fd = -1;
    owner->stdout_bytes = malloc(limits.stdout_limit ? limits.stdout_limit : 1);
    owner->stderr_bytes = malloc(limits.stderr_limit ? limits.stderr_limit : 1);
    int error = (!owner->stdout_bytes || !owner->stderr_bytes) ? ENOMEM : 0;
    int out[2] = {-1,-1}, err[2] = {-1,-1};
    if (!error) error = sosix_darwin_process_pipe(out);
    if (!error) error = sosix_darwin_process_pipe(err);
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attributes;
    int actions_ready = 0, attributes_ready = 0;
    if (!error) { error = posix_spawn_file_actions_init(&actions); actions_ready = !error; }
    if (!error) { error = posix_spawnattr_init(&attributes); attributes_ready = !error; }
    if (!error) error = posix_spawn_file_actions_addopen(&actions, STDIN_FILENO, "/dev/null", O_RDONLY, 0);
    if (!error) error = posix_spawn_file_actions_adddup2(&actions, out[1], STDOUT_FILENO);
    if (!error) error = posix_spawn_file_actions_adddup2(&actions, err[1], STDERR_FILENO);
    if (!error) error = posix_spawn_file_actions_addfchdir_np(&actions, cwd_fd);
    if (!error) error = posix_spawnattr_setpgroup(&attributes, 0);
    sigset_t mask, defaults; sigemptyset(&mask); sigemptyset(&defaults);
    sigaddset(&defaults, SIGTERM); sigaddset(&defaults, SIGINT); sigaddset(&defaults, SIGPIPE);
    if (!error) error = posix_spawnattr_setsigmask(&attributes, &mask);
    if (!error) error = posix_spawnattr_setsigdefault(&attributes, &defaults);
    if (!error) error = posix_spawnattr_setflags(&attributes,
        POSIX_SPAWN_SETPGROUP | POSIX_SPAWN_CLOEXEC_DEFAULT | POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF);
    if (!error) error = sosix_darwin_image_spawn(image, image_generation, &owner->pid,
        &actions, &attributes, argv, environment);
    if (actions_ready) posix_spawn_file_actions_destroy(&actions);
    if (attributes_ready) posix_spawnattr_destroy(&attributes);
    if (out[1] >= 0) close(out[1]);
    if (err[1] >= 0) close(err[1]);
    if (error) {
        if (out[0] >= 0) close(out[0]);
        if (err[0] >= 0) close(err[0]);
        free(owner->stdout_bytes); free(owner->stderr_bytes);
        memset(owner, 0, sizeof(*owner)); return error;
    }
    /* No fallible operation after spawn may discard this child. */
    owner->stdout_fd = out[0]; owner->stderr_fd = err[0]; owner->limits = limits;
    owner->execution_deadline = limits.wall_ns ? now + limits.wall_ns : 0;
    do arc4random_buf(&owner->generation, sizeof(owner->generation)); while (!owner->generation);
    return 0;
}

static void sosix_darwin_process_drain(int *fd, unsigned char *bytes, size_t limit,
        size_t *kept, uint64_t *seen, int *error) {
    unsigned char buffer[4096]; size_t budget = 65536;
    while (*fd >= 0 && budget) {
        size_t want = budget < sizeof(buffer) ? budget : sizeof(buffer);
        ssize_t n = SOSIX_DARWIN_PROCESS_READ(*fd, buffer, want);
        if (n < 0) {
            if (errno == EINTR) { budget--; continue; }
            if (errno == EAGAIN || errno == EWOULDBLOCK) return;
            *error = errno; close(*fd); *fd = -1; return;
        }
        if (!n) { close(*fd); *fd = -1; return; }
        *seen += (uint64_t)n;
        size_t retain = (size_t)n < limit - *kept ? (size_t)n : limit - *kept;
        memcpy(bytes + *kept, buffer, retain); *kept += retain; budget -= (size_t)n;
    }
}

static int sosix_darwin_process_poll(SosixDarwinProcess *owner, uint64_t generation, int64_t wait_ns) {
    if (!owner || !generation || owner->generation != generation) return ESTALE;
    if (owner->frozen) return 0;
    if (wait_ns < 0 || wait_ns > 250000000LL) return EINVAL;
    int64_t now = sosix_darwin_process_now(); if (now < 0) return EIO;
    if (!owner->reaped) {
        siginfo_t information; memset(&information, 0, sizeof(information));
        if (waitid(P_PID, (id_t)owner->pid, &information, WEXITED | WNOHANG | WNOWAIT)) return errno;
        if (information.si_pid == owner->pid) owner->leader_exited = 1;
        int timeout = owner->execution_deadline && now >= owner->execution_deadline;
        if ((timeout || owner->cancel_requested || owner->leader_exited) && !owner->cleanup_deadline) {
            if (owner->limits.term_grace_ns > INT64_MAX - now ||
                owner->limits.cleanup_ns > INT64_MAX - now - owner->limits.term_grace_ns) return EOVERFLOW;
            owner->kill_deadline = now + owner->limits.term_grace_ns;
            owner->cleanup_deadline = owner->kill_deadline + owner->limits.cleanup_ns;
            if (timeout && !owner->leader_exited) owner->timed_out = 1;
        }
        if (owner->cleanup_deadline && !owner->term_sent && !owner->leader_exited) {
            if (!kill(-owner->pid, SIGTERM)) owner->term_sent = 1;
            else if (errno != ESRCH) return errno;
        }
        size_t live = 1;
        if (owner->leader_exited) {
            int error = sosix_darwin_process_group_live(owner->pid, &live); if (error) return error;
        }
        /* Do not re-signal a successfully killed leader while waitid is still
         * catching up. Darwin can return EPERM for a dying group's remaining
         * unsignalable members. Retry failed delivery; after leader exit,
         * a positive group sample independently requires descendant cleanup. */
        if (live && owner->cleanup_deadline &&
            (owner->leader_exited || (!owner->kill_sent && now >= owner->kill_deadline))) {
            if (!kill(-owner->pid, SIGKILL)) owner->kill_sent = 1;
            else if (errno != ESRCH) return errno;
        }
        if (owner->leader_exited && !live) {
            pid_t waited = wait4(owner->pid, &owner->wait_status, WNOHANG, &owner->usage);
            if (waited < 0) return errno;
            if (waited == owner->pid) owner->reaped = owner->group_retired = 1;
        }
    }
    sosix_darwin_process_drain(&owner->stdout_fd, owner->stdout_bytes, owner->limits.stdout_limit,
        &owner->stdout_kept, &owner->stdout_seen, &owner->stdout_error);
    sosix_darwin_process_drain(&owner->stderr_fd, owner->stderr_bytes, owner->limits.stderr_limit,
        &owner->stderr_kept, &owner->stderr_seen, &owner->stderr_error);
    if (owner->reaped && owner->stdout_fd < 0 && owner->stderr_fd < 0) { owner->frozen = 1; return 0; }
    if (owner->cleanup_deadline && now >= owner->cleanup_deadline) {
        owner->cleanup_error = ETIMEDOUT; return ETIMEDOUT; /* Retain ownership for retries. */
    }
    int64_t next = owner->cleanup_deadline ? owner->kill_deadline : owner->execution_deadline;
    if (next > now && wait_ns > next - now) wait_ns = next - now;
    struct pollfd fds[2] = {{owner->stdout_fd, POLLIN, 0}, {owner->stderr_fd, POLLIN, 0}};
    if (poll(fds, 2, (int)((wait_ns + 999999LL) / 1000000LL)) < 0 && errno != EINTR) return errno;
    return 0;
}

static int sosix_darwin_process_cancel(SosixDarwinProcess *owner, uint64_t generation) {
    if (!owner || !generation || owner->generation != generation) return ESTALE;
    if (owner->frozen) return 0;
    owner->cancel_requested = 1; return sosix_darwin_process_poll(owner, generation, 0);
}

static int sosix_darwin_process_ack(SosixDarwinProcess *owner, uint64_t generation) {
    if (!owner || !generation || owner->generation != generation) return ESTALE;
    if (!owner->frozen || !owner->reaped || !owner->group_retired) return EBUSY;
    free(owner->stdout_bytes); free(owner->stderr_bytes); memset(owner, 0, sizeof(*owner)); return 0;
}
#endif
#endif
