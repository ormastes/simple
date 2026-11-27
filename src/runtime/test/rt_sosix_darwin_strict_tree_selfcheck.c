/* Negative qualification: process groups are not a Darwin descendant owner.
 * Each escaped process has a pipe-driven exit and an independent watchdog.
 * No escaped PID is signalled; a potentially recycled PID is never authority.
 * PASS means the limitation was reproduced, never that strict V4 is available.
 */
#ifndef __APPLE__
#include <stdio.h>
int main(void) { puts("SKIP: Darwin strict-tree evidence requires macOS"); return 77; }
#else
#define _DARWIN_C_SOURCE
#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/event.h>
#include <sys/wait.h>
#include <unistd.h>
#include <sandbox.h>
#include <spawn.h>

static void transfer(int fd, void *buffer, size_t size, int writing) {
    unsigned char *bytes = buffer;
    while (size) {
        ssize_t n = writing ? write(fd, bytes, size) : read(fd, bytes, size);
        if (n < 0 && errno == EINTR) continue;
        assert(n > 0); bytes += n; size -= (size_t)n;
    }
}

static void escaped_worker(int output, int command) {
    alarm(8);
    pid_t self = getpid(); transfer(output, &self, sizeof(self), 1);
    char byte = 0; transfer(command, &byte, 1, 0); assert(byte == 'P');
    byte = 'L'; transfer(output, &byte, 1, 1);
    transfer(command, &byte, 1, 0); assert(byte == 'X');
    _exit(0);
}

static void escape_case(const char *method, int kill_leader) {
    int output[2], command[2], leader_ready[2];
    assert(pipe(output) == 0 && pipe(command) == 0 && pipe(leader_ready) == 0);
    pid_t leader = fork(); assert(leader >= 0);
    if (!leader) {
        alarm(8); close(output[0]); close(command[1]); close(leader_ready[0]);
        assert(setpgid(0, 0) == 0);
        pid_t child = fork(); assert(child >= 0);
        if (!child) {
            close(leader_ready[1]);
            if (!strcmp(method, "setpgid")) assert(setpgid(0, 0) == 0);
            else assert(setsid() == getpid());
            if (!strcmp(method, "double-fork")) {
                pid_t grandchild = fork(); assert(grandchild >= 0);
                if (grandchild) _exit(0);
            }
            escaped_worker(output[1], command[0]);
        }
        char ready = 'R'; transfer(leader_ready[1], &ready, 1, 1);
        if (kill_leader) for (;;) pause();
        _exit(0);
    }
    close(output[1]); close(command[0]); close(leader_ready[1]);
    char byte; transfer(leader_ready[0], &byte, 1, 0); assert(byte == 'R');
    close(leader_ready[0]);
    pid_t escaped; transfer(output[0], &escaped, sizeof(escaped), 0);
    assert(escaped != leader && getpgid(escaped) != leader);
    int queue = kqueue(); assert(queue >= 0);
    struct kevent event;
    EV_SET(&event, escaped, EVFILT_PROC, EV_ADD | EV_ONESHOT, NOTE_EXIT, 0, NULL);
    assert(kevent(queue, &event, 1, NULL, 0, NULL) == 0);
    if (kill_leader) assert(kill(-leader, SIGKILL) == 0);
    siginfo_t info; memset(&info, 0, sizeof(info));
    assert(waitid(P_PID, leader, &info, WEXITED | WNOWAIT) == 0);
    /* The unreaped leader pins its numeric group ID during this signal. */
    int signalled = kill(-leader, SIGKILL);
    assert(signalled == 0 || errno == ESRCH || errno == EPERM);
    byte = 'P'; transfer(command[1], &byte, 1, 1);
    transfer(output[0], &byte, 1, 0); assert(byte == 'L');
    /* Kernel wait authority remains with init/original parent, not observer. */
    int status; errno = 0;
    assert(waitpid(escaped, &status, WNOHANG) == -1 && errno == ECHILD);
    byte = 'X'; transfer(command[1], &byte, 1, 1);
    struct timespec deadline = {3, 0};
    assert(kevent(queue, NULL, 0, &event, 1, &deadline) == 1);
    assert(event.ident == (uintptr_t)escaped && (event.fflags & NOTE_EXIT));
    assert(waitpid(leader, &status, 0) == leader);
    if (kill_leader) assert(WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL);
    else assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    close(queue); close(output[0]); close(command[1]);
    printf("escape_%s_%s: reproduced\n", method, kill_leader ? "kill" : "exit");
}

static void no_recursive_kqueue(void) {
    int queue = kqueue(); assert(queue >= 0);
    struct kevent change, receipt;
    EV_SET(&change, getpid(), EVFILT_PROC, EV_ADD | EV_RECEIPT,
        NOTE_FORK | NOTE_TRACK, 0, NULL);
    struct timespec immediate = {0, 0};
    assert(kevent(queue, &change, 1, &receipt, 1, &immediate) == 1);
    assert((receipt.flags & EV_ERROR) && receipt.data == ENOTSUP);
    close(queue); puts("recursive_kqueue: unsupported");
}

static void sandbox_fork_denial(void) {
    pid_t child = fork(); assert(child >= 0);
    if (!child) {
        alarm(8);
        char *error = NULL;
        int installed = sandbox_init("(version 1)(allow default)(deny process-fork)", 0, &error);
        if (installed) { if (error) sandbox_free_error(error); _exit(77); }
        errno = 0; pid_t denied = fork();
        if (!denied) _exit(99);
        assert(denied == -1 && errno == EPERM);
        char *args[] = {"/usr/bin/true", NULL}, *env[] = {NULL};
        pid_t spawned = -1;
        assert(posix_spawn(&spawned, args[0], NULL, NULL, args, env) == EPERM);
        /* Fork denial does not restrict session/group membership itself. */
        assert(setsid() == getpid());
        _exit(0);
    }
    int status; assert(waitpid(child, &status, 0) == child && WIFEXITED(status));
    assert(WEXITSTATUS(status) == 0 || WEXITSTATUS(status) == 77);
    puts(WEXITSTATUS(status) == 0 ? "sandbox_no_fork: enforced_but_no_descendants" :
        "sandbox_no_fork: unavailable");
}

int main(void) {
    alarm(30);
    signal(SIGPIPE, SIG_DFL);
    no_recursive_kqueue();
    const char *methods[] = {"setsid", "setpgid", "double-fork"};
    for (size_t i = 0; i < 3; i++) {
        escape_case(methods[i], 0); escape_case(methods[i], 1);
    }
    sandbox_fork_denial();
    puts("strict_tree_authority: unavailable");
    puts("darwin_strict_tree_negative_qualification: pass");
    return 0;
}
#endif
