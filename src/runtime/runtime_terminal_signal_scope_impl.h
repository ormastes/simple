#ifndef SIMPLE_RUNTIME_TERMINAL_SIGNAL_SCOPE_IMPL_H
#define SIMPLE_RUNTIME_TERMINAL_SIGNAL_SCOPE_IMPL_H

#include <stdbool.h>
#include <stdint.h>
#include <errno.h>

#ifndef SPL_TERMINAL_SCOPE_BEGIN
#define SPL_TERMINAL_SCOPE_BEGIN rt_terminal_signal_scope_begin
#endif
#ifndef SPL_TERMINAL_SCOPE_READ
#define SPL_TERMINAL_SCOPE_READ rt_terminal_read_byte_interruptible
#endif
#ifndef SPL_TERMINAL_SCOPE_END
#define SPL_TERMINAL_SCOPE_END rt_terminal_signal_scope_end
#endif

#if defined(_WIN32)

int64_t SPL_TERMINAL_SCOPE_BEGIN(void) {
    errno = ENOSYS;
    return 0;
}

int64_t SPL_TERMINAL_SCOPE_READ(int64_t scope) {
    (void)scope;
    errno = EINVAL;
    return -4;
}

bool SPL_TERMINAL_SCOPE_END(int64_t scope) {
    (void)scope;
    errno = EINVAL;
    return false;
}

#else

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>

enum {
    SPL_TERMINAL_SCOPE_SIGNAL_COUNT = 4,
    SPL_TERMINAL_READ_EOF = -1,
    SPL_TERMINAL_READ_STOP = -2,
    SPL_TERMINAL_READ_RESIZE = -3,
    SPL_TERMINAL_READ_ERROR = -4
};

typedef struct SplTerminalSignalScopeState {
    bool active;
    int64_t handle;
    int pipe_read;
    int pipe_write;
    int installed_handlers;
    struct sigaction previous_handlers[SPL_TERMINAL_SCOPE_SIGNAL_COUNT];
    volatile sig_atomic_t stop_pending;
    volatile sig_atomic_t resize_pending;
} SplTerminalSignalScopeState;

static SplTerminalSignalScopeState spl_terminal_signal_scope = {
    false, 0, -1, -1, 0, {{0}}, 0, 0
};
static volatile sig_atomic_t spl_terminal_signal_pipe_write = -1;
static int64_t spl_terminal_signal_next_handle = 1;

static const int spl_terminal_managed_signals[SPL_TERMINAL_SCOPE_SIGNAL_COUNT] = {
    SIGHUP, SIGINT, SIGTERM, SIGWINCH
};

static void spl_terminal_managed_signal_set(sigset_t* signals) {
    sigemptyset(signals);
    for (int i = 0; i < SPL_TERMINAL_SCOPE_SIGNAL_COUNT; i++) {
        sigaddset(signals, spl_terminal_managed_signals[i]);
    }
}

static void spl_terminal_scope_signal_handler(int signum) {
    int saved_errno = errno;
    if (signum == SIGWINCH) {
        spl_terminal_signal_scope.resize_pending = 1;
    } else {
        spl_terminal_signal_scope.stop_pending = 1;
    }
    int fd = (int)spl_terminal_signal_pipe_write;
    if (fd >= 0) {
        unsigned char wake = (unsigned char)signum;
        (void)write(fd, &wake, 1);
    }
    errno = saved_errno;
}

static bool spl_terminal_configure_pipe_fd(int fd) {
    int status_flags = fcntl(fd, F_GETFL, 0);
    if (status_flags < 0 || fcntl(fd, F_SETFL, status_flags | O_NONBLOCK) < 0) {
        return false;
    }
    int descriptor_flags = fcntl(fd, F_GETFD, 0);
    return descriptor_flags >= 0 && fcntl(fd, F_SETFD, descriptor_flags | FD_CLOEXEC) == 0;
}

static void spl_terminal_restore_handlers(int installed_handlers, int* first_errno) {
    for (int i = installed_handlers - 1; i >= 0; i--) {
        if (sigaction(spl_terminal_managed_signals[i],
                      &spl_terminal_signal_scope.previous_handlers[i], NULL) != 0 &&
            *first_errno == 0) {
            *first_errno = errno;
        }
    }
}

static void spl_terminal_close_pipe(int* first_errno) {
    if (spl_terminal_signal_scope.pipe_read >= 0 &&
        close(spl_terminal_signal_scope.pipe_read) != 0 && *first_errno == 0) {
        *first_errno = errno;
    }
    if (spl_terminal_signal_scope.pipe_write >= 0 &&
        close(spl_terminal_signal_scope.pipe_write) != 0 && *first_errno == 0) {
        *first_errno = errno;
    }
    spl_terminal_signal_scope.pipe_read = -1;
    spl_terminal_signal_scope.pipe_write = -1;
}

static int64_t spl_terminal_take_pending_signal(void) {
    sigset_t managed;
    sigset_t previous_mask;
    spl_terminal_managed_signal_set(&managed);
    bool masked = sigprocmask(SIG_BLOCK, &managed, &previous_mask) == 0;
    sig_atomic_t stop = spl_terminal_signal_scope.stop_pending;
    sig_atomic_t resize = spl_terminal_signal_scope.resize_pending;
    spl_terminal_signal_scope.stop_pending = 0;
    spl_terminal_signal_scope.resize_pending = 0;
    if (masked) {
        (void)sigprocmask(SIG_SETMASK, &previous_mask, NULL);
    }
    if (stop) return SPL_TERMINAL_READ_STOP;
    if (resize) return SPL_TERMINAL_READ_RESIZE;
    return 0;
}

static void spl_terminal_drain_signal_pipe(void) {
    unsigned char buffer[64];
    while (read(spl_terminal_signal_scope.pipe_read, buffer, sizeof(buffer)) > 0) {
    }
}

int64_t SPL_TERMINAL_SCOPE_BEGIN(void) {
    if (spl_terminal_signal_scope.active) {
        errno = EBUSY;
        return 0;
    }

    sigset_t managed;
    sigset_t previous_mask;
    spl_terminal_managed_signal_set(&managed);
    if (sigprocmask(SIG_BLOCK, &managed, &previous_mask) != 0) return 0;

    int pipe_fds[2] = {-1, -1};
    int failure_errno = 0;
    if (pipe(pipe_fds) != 0 ||
        !spl_terminal_configure_pipe_fd(pipe_fds[0]) ||
        !spl_terminal_configure_pipe_fd(pipe_fds[1])) {
        failure_errno = errno;
        if (pipe_fds[0] >= 0) (void)close(pipe_fds[0]);
        if (pipe_fds[1] >= 0) (void)close(pipe_fds[1]);
        (void)sigprocmask(SIG_SETMASK, &previous_mask, NULL);
        errno = failure_errno;
        return 0;
    }

    spl_terminal_signal_scope.pipe_read = pipe_fds[0];
    spl_terminal_signal_scope.pipe_write = pipe_fds[1];
    spl_terminal_signal_scope.stop_pending = 0;
    spl_terminal_signal_scope.resize_pending = 0;
    spl_terminal_signal_scope.installed_handlers = 0;
    spl_terminal_signal_pipe_write = pipe_fds[1];

    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = spl_terminal_scope_signal_handler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;
    for (int i = 0; i < SPL_TERMINAL_SCOPE_SIGNAL_COUNT; i++) {
        if (sigaction(spl_terminal_managed_signals[i], &action,
                      &spl_terminal_signal_scope.previous_handlers[i]) != 0) {
            failure_errno = errno;
            spl_terminal_signal_pipe_write = -1;
            spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                          &failure_errno);
            spl_terminal_close_pipe(&failure_errno);
            spl_terminal_signal_scope.installed_handlers = 0;
            (void)sigprocmask(SIG_SETMASK, &previous_mask, NULL);
            errno = failure_errno;
            return 0;
        }
        spl_terminal_signal_scope.installed_handlers++;
    }

    int64_t handle = spl_terminal_signal_next_handle++;
    if (handle <= 0) {
        spl_terminal_signal_next_handle = 2;
        handle = 1;
    }
    spl_terminal_signal_scope.handle = handle;
    spl_terminal_signal_scope.active = true;
    if (sigprocmask(SIG_SETMASK, &previous_mask, NULL) != 0) {
        failure_errno = errno;
        spl_terminal_signal_scope.active = false;
        spl_terminal_signal_scope.handle = 0;
        spl_terminal_signal_pipe_write = -1;
        spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                      &failure_errno);
        spl_terminal_close_pipe(&failure_errno);
        spl_terminal_signal_scope.installed_handlers = 0;
        errno = failure_errno;
        return 0;
    }
    return handle;
}

int64_t SPL_TERMINAL_SCOPE_READ(int64_t scope) {
    if (!spl_terminal_signal_scope.active || scope <= 0 ||
        scope != spl_terminal_signal_scope.handle) {
        errno = EINVAL;
        return SPL_TERMINAL_READ_ERROR;
    }

    for (;;) {
        int64_t pending = spl_terminal_take_pending_signal();
        if (pending != 0) return pending;

        struct pollfd fds[2];
        fds[0].fd = STDIN_FILENO;
        fds[0].events = POLLIN | POLLHUP;
        fds[0].revents = 0;
        fds[1].fd = spl_terminal_signal_scope.pipe_read;
        fds[1].events = POLLIN | POLLHUP;
        fds[1].revents = 0;
        int ready = poll(fds, 2, -1);
        if (ready < 0) {
            if (errno == EINTR) continue;
            return SPL_TERMINAL_READ_ERROR;
        }

        if (fds[1].revents != 0) {
            spl_terminal_drain_signal_pipe();
            pending = spl_terminal_take_pending_signal();
            if (pending != 0) return pending;
            if (fds[1].revents & (POLLERR | POLLNVAL | POLLHUP)) {
                errno = EIO;
                return SPL_TERMINAL_READ_ERROR;
            }
        }

        if (fds[0].revents & POLLIN) {
            unsigned char byte = 0;
            ssize_t count = read(STDIN_FILENO, &byte, 1);
            if (count == 1) return (int64_t)byte;
            if (count == 0) return SPL_TERMINAL_READ_EOF;
            if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) continue;
            return SPL_TERMINAL_READ_ERROR;
        }
        if (fds[0].revents & POLLHUP) return SPL_TERMINAL_READ_EOF;
        if (fds[0].revents & (POLLERR | POLLNVAL)) {
            errno = EIO;
            return SPL_TERMINAL_READ_ERROR;
        }
    }
}

bool SPL_TERMINAL_SCOPE_END(int64_t scope) {
    if (!spl_terminal_signal_scope.active || scope <= 0 ||
        scope != spl_terminal_signal_scope.handle) {
        errno = EINVAL;
        return false;
    }

    sigset_t managed;
    sigset_t previous_mask;
    spl_terminal_managed_signal_set(&managed);
    bool masked = sigprocmask(SIG_BLOCK, &managed, &previous_mask) == 0;
    int first_errno = masked ? 0 : errno;

    spl_terminal_signal_pipe_write = -1;
    spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                  &first_errno);
    spl_terminal_close_pipe(&first_errno);
    spl_terminal_signal_scope.active = false;
    spl_terminal_signal_scope.handle = 0;
    spl_terminal_signal_scope.installed_handlers = 0;
    spl_terminal_signal_scope.stop_pending = 0;
    spl_terminal_signal_scope.resize_pending = 0;

    if (masked && sigprocmask(SIG_SETMASK, &previous_mask, NULL) != 0 &&
        first_errno == 0) {
        first_errno = errno;
    }
    if (first_errno != 0) {
        errno = first_errno;
        return false;
    }
    return true;
}

#endif

#undef SPL_TERMINAL_SCOPE_BEGIN
#undef SPL_TERMINAL_SCOPE_READ
#undef SPL_TERMINAL_SCOPE_END

#endif
