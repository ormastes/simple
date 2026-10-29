/* Direct-child canonical helper admission. This is separate from launchd label
 * observation: posix_spawn supplies authority and an explicit empty environment
 * before dyld runs. Caller supplies a trusted bound canonical helper image.
 * No workload launcher, disjoint coalition, descendant confinement or V4 claim.
 * Single owner: retain the image through spawn and never let a SIGCHLD handler
 * or another thread reap this child. The unreaped child pins its PID. */
#ifndef RUNTIME_SOSIX_DARWIN_BROKER_ADMISSION_PRIVATE_H
#define RUNTIME_SOSIX_DARWIN_BROKER_ADMISSION_PRIVATE_H
#ifdef __APPLE__
#include "runtime_sosix_darwin_image_private.h"
#include "runtime_sosix_darwin_broker_transport_private.h"
#include <poll.h>
#include <sys/wait.h>
#define SOSIX_DARWIN_BROKER_CLOSED_MODE "--sosix-darwin-broker-closed"

typedef struct {
    pid_t pid;
    SosixDarwinProcessIdentity identity;
    unsigned char cdhash[20];
    int admitted, reaped;
} SosixDarwinBrokerAdmission;

static int sosix_darwin_broker_read_byte(int fd, char *byte, unsigned timeout_ms) {
    if (fd < 0 || !byte || !timeout_ms || timeout_ms > 60000) return EINVAL;
    int64_t start = sosix_darwin_coalition_now_ns();
    if (start < 0) return EIO;
    int64_t deadline = start + (int64_t)timeout_ms * 1000000;
    for (;;) {
        int64_t now = sosix_darwin_coalition_now_ns();
        if (now < 0) return EIO;
        if (now >= deadline) return ETIMEDOUT;
        struct pollfd p = {fd, POLLIN, 0};
        int n = poll(&p, 1, (int)((deadline - now + 999999) / 1000000));
        if (n < 0) { if (errno == EINTR) continue; return errno; }
        if (!n) return ETIMEDOUT;
        if (!(p.revents & (POLLIN | POLLHUP))) return EIO;
        ssize_t count = recv(fd, byte, 1, MSG_DONTWAIT);
        if (count == 1) return 0;
        if (!count) return EPIPE;
        if (errno != EINTR && errno != EAGAIN) return errno;
    }
}
static int sosix_darwin_broker_send_byte(int fd, char byte) {
    int no_sigpipe = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &no_sigpipe, sizeof(no_sigpipe))) return errno;
    ssize_t count = send(fd, &byte, 1, MSG_DONTWAIT);
    return count == 1 ? 0 : (count < 0 ? errno : EIO);
}

/* Never let a replaced endpoint with a full backlog strand helper startup. */
static int sosix_darwin_broker_connect(int fd, const struct sockaddr_un *address, unsigned timeout_ms) {
    if (fd < 0 || !address || !timeout_ms || timeout_ms > 60000) return EINVAL;
    int flags = fcntl(fd, F_GETFL); if (flags < 0) return errno;
    if (fcntl(fd, F_SETFL, flags | O_NONBLOCK)) return errno;
    int64_t now = sosix_darwin_coalition_now_ns(); if (now < 0) return EIO;
    int64_t deadline = now + (int64_t)timeout_ms * 1000000;
    if (!connect(fd, (const struct sockaddr *)address, sizeof(*address))) return 0;
    if (errno != EINPROGRESS && errno != EINTR) return errno;
    for (;;) {
        now = sosix_darwin_coalition_now_ns(); if (now < 0) return EIO;
        if (now >= deadline) return ETIMEDOUT;
        struct pollfd p = {fd, POLLOUT, 0};
        int n = poll(&p, 1, (int)((deadline - now + 999999) / 1000000));
        if (n < 0) { if (errno == EINTR) continue; return errno; }
        if (!n) return ETIMEDOUT;
        int error = 0; socklen_t size = sizeof(error);
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &error, &size)) return errno;
        if (size != sizeof(error)) return EPROTO;
        return error;
    }
}

static int sosix_darwin_broker_spawn_closed(SosixDarwinImage *image, uint64_t generation,
        const char *endpoint, SosixDarwinBrokerAdmission *owner) {
    if (!image || !owner || !endpoint || endpoint[0] != '/') return EINVAL;
    if (owner->pid) return EALREADY;
    if (!image->kernel_bound) return ENOTSUP;
    if (strlen(endpoint) >= sizeof(((struct sockaddr_un *)0)->sun_path)) return ENAMETOOLONG;
    SosixDarwinProcessIdentity controller;
    int e = sosix_darwin_coalition_identity(getpid(), &controller, 0);
    if (e) return e;
    char controller_pid[24], controller_version[24];
    snprintf(controller_pid, sizeof(controller_pid), "%d", getpid());
    snprintf(controller_version, sizeof(controller_version), "%u", (unsigned)controller.pid_version);
    char *arguments[] = {image->path, SOSIX_DARWIN_BROKER_CLOSED_MODE, (char *)endpoint,
                        controller_pid, controller_version, NULL};
    char *environment[] = {NULL};
    posix_spawnattr_t attributes;
    e = posix_spawnattr_init(&attributes); if (e) return e;
    posix_spawn_file_actions_t actions;
    e = posix_spawn_file_actions_init(&actions);
    if (e) { posix_spawnattr_destroy(&attributes); return e; }
    sigset_t empty, defaults; sigemptyset(&empty); sigfillset(&defaults);
    sigdelset(&defaults, SIGKILL); sigdelset(&defaults, SIGSTOP);
    e = posix_spawnattr_setflags(&attributes, POSIX_SPAWN_CLOEXEC_DEFAULT | POSIX_SPAWN_SETSIGDEF | POSIX_SPAWN_SETSIGMASK);
    if (!e) e = posix_spawnattr_setsigmask(&attributes, &empty);
    if (!e) e = posix_spawnattr_setsigdefault(&attributes, &defaults);
    if (!e) e = posix_spawn_file_actions_addchdir_np(&actions, "/");
    for (int fd = 0; !e && fd < 3; ++fd)
        e = posix_spawn_file_actions_addopen(&actions, fd, "/dev/null", fd ? O_WRONLY : O_RDONLY, 0);
    pid_t child = 0;
    if (!e) e = sosix_darwin_image_spawn(image, generation, &child, &actions, &attributes, arguments, environment);
    posix_spawn_file_actions_destroy(&actions); posix_spawnattr_destroy(&attributes);
    if (e) return e;
    /* Record ownership even when the child exits before its identity query.
     * Caller must close/reap this object after every successful spawn. */
    memset(owner, 0, sizeof(*owner)); owner->pid = child;
    memcpy(owner->cdhash, image->cdhash, 20);
    e = sosix_darwin_coalition_identity(child, &owner->identity, 1);
    if (e) memset(&owner->identity, 0, sizeof(owner->identity));
    return 0;
}

/* A token on an accepted stream must name the direct unreaped child and its
 * spawn incarnation, not any job currently visible under a launchd label.
 * Caller owns fd; errors never set admitted and never send an admission byte
 * before authentication. Canonical helper does not fork, exec or pass sockets. */
static int sosix_darwin_broker_admit(SosixDarwinBrokerAdmission *owner, int fd, unsigned timeout_ms) {
    if (!owner || owner->pid <= 1 || fd < 0 || !timeout_ms || timeout_ms > 60000) return EINVAL;
    if (owner->reaped) return ESTALE;
    if (owner->admitted) return EALREADY;
    if (!owner->identity.unique_id) return ESTALE;
    audit_token_t token; SosixDarwinProcessIdentity identity;
    int e = sosix_darwin_broker_peer_identity(fd, owner->pid, (uint32_t)owner->identity.pid_version, &token, &identity);
    if (!e && identity.unique_id != owner->identity.unique_id) e = ESTALE;
    if (!e) e = sosix_darwin_broker_peer_cdhash(&token, owner->cdhash);
    if (e) return e;
    int64_t started = sosix_darwin_coalition_now_ns(); if (started < 0) return EIO;
    int64_t deadline = started + (int64_t)timeout_ms * 1000000;
    char byte;
    e = sosix_darwin_broker_read_byte(fd, &byte, timeout_ms);
    if (!e && byte != 'R') e = EPROTO;
    if (!e) e = sosix_darwin_broker_send_byte(fd, 'A');
    if (!e) {
        int64_t now = sosix_darwin_coalition_now_ns();
        if (now < 0) e = EIO;
        else if (now >= deadline) e = ETIMEDOUT;
        else e = sosix_darwin_broker_read_byte(fd, &byte, (unsigned)((deadline - now + 999999) / 1000000));
    }
    if (!e && byte != 'A') e = EPROTO;
    if (!e) owner->admitted = 1;
    return e;
}

/* Sole-reaper direct-child cleanup only. It is never a descendant receipt.
 * ECHILD means authority was lost; fail without signalling a recycled PID. */
static int sosix_darwin_broker_admission_close(SosixDarwinBrokerAdmission *owner, unsigned timeout_ms) {
    if (!owner || owner->pid <= 1 || !timeout_ms || timeout_ms > 60000) return EINVAL;
    if (owner->reaped) return EALREADY;
    int64_t now = sosix_darwin_coalition_now_ns(); if (now < 0) return EIO;
    int64_t deadline = now + (int64_t)timeout_ms * 1000000;
    int signalled = 0;
    for (;;) {
        int status; pid_t result = waitpid(owner->pid, &status, WNOHANG);
        if (result == owner->pid) { owner->reaped = 1; owner->admitted = 0; return 0; }
        if (result < 0 && errno != EINTR) return errno;
        if (!result && !signalled) {
            if (kill(owner->pid, SIGKILL) && errno != ESRCH) return errno;
            signalled = 1;
        }
        now = sosix_darwin_coalition_now_ns(); if (now < 0) return EIO;
        if (now >= deadline) return ETIMEDOUT;
        struct timespec delay = {0, 1000000}; nanosleep(&delay, NULL);
    }
}
#endif
#endif
