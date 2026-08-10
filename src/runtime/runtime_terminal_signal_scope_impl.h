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
#ifndef SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE
#define SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE rt_terminal_signal_scope_emergency_restore
#endif

#ifndef SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED
#define SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED(target) ((void)(target))
#endif
#ifndef SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE
#define SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE() ((void)0)
#endif
#ifndef SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT
#define SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT() ((void)0)
#endif
#ifndef SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE
#define SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE(target) ((void)(target))
#endif

#if defined(_WIN32)

#include <io.h>
#include <windows.h>

enum {
    SPL_TERMINAL_SCOPE_IDLE = 0,
    SPL_TERMINAL_SCOPE_ACTIVE = 1,
    SPL_TERMINAL_SCOPE_CLOSING = 2,
    SPL_TERMINAL_READ_EOF = -1,
    SPL_TERMINAL_READ_STOP = -2,
    SPL_TERMINAL_READ_RESIZE = -3,
    SPL_TERMINAL_READ_ERROR = -4
};

static PVOID volatile spl_terminal_signal_event;
static volatile LONG spl_terminal_stop_pending;
static volatile LONG spl_terminal_scope_lifecycle;
static volatile LONG spl_terminal_handlers_inflight;
static int64_t spl_terminal_scope_handle;

static BOOL WINAPI spl_terminal_console_handler(DWORD event) {
    if (event == CTRL_C_EVENT || event == CTRL_BREAK_EVENT ||
        event == CTRL_CLOSE_EVENT || event == CTRL_LOGOFF_EVENT ||
        event == CTRL_SHUTDOWN_EVENT) {
        InterlockedIncrement(&spl_terminal_handlers_inflight);
        InterlockedExchange(&spl_terminal_stop_pending, 1);
        HANDLE wake = (HANDLE)InterlockedCompareExchangePointer(
            &spl_terminal_signal_event, NULL, NULL);
        SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED(wake);
        if (wake != NULL) SetEvent(wake);
        InterlockedDecrement(&spl_terminal_handlers_inflight);
        return TRUE;
    }
    return FALSE;
}

static void spl_terminal_wait_for_console_handlers(void) {
    while (InterlockedCompareExchange(&spl_terminal_handlers_inflight, 0, 0) != 0) {
        SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT();
        SwitchToThread();
    }
}

int64_t SPL_TERMINAL_SCOPE_BEGIN(void) {
    if (InterlockedCompareExchange(&spl_terminal_scope_lifecycle,
                                   SPL_TERMINAL_SCOPE_ACTIVE,
                                   SPL_TERMINAL_SCOPE_IDLE) != SPL_TERMINAL_SCOPE_IDLE) {
        errno = EBUSY;
        return 0;
    }
    HANDLE wake = CreateEventW(NULL, TRUE, FALSE, NULL);
    InterlockedExchangePointer(&spl_terminal_signal_event, wake);
    if (wake == NULL || !SetConsoleCtrlHandler(spl_terminal_console_handler, TRUE)) {
        HANDLE rollback = (HANDLE)InterlockedExchangePointer(
            &spl_terminal_signal_event, NULL);
        if (rollback != NULL) CloseHandle(rollback);
        InterlockedExchange(&spl_terminal_scope_lifecycle, SPL_TERMINAL_SCOPE_IDLE);
        errno = EIO;
        return 0;
    }
    InterlockedExchange(&spl_terminal_stop_pending, 0);
    spl_terminal_scope_handle++;
    if (spl_terminal_scope_handle <= 0) spl_terminal_scope_handle = 1;
    return spl_terminal_scope_handle;
}

int64_t SPL_TERMINAL_SCOPE_READ(int64_t scope) {
    if (InterlockedCompareExchange(&spl_terminal_scope_lifecycle, 0, 0) !=
            SPL_TERMINAL_SCOPE_ACTIVE ||
        scope <= 0 || scope != spl_terminal_scope_handle) {
        errno = EINVAL;
        return SPL_TERMINAL_READ_ERROR;
    }
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE wake = (HANDLE)InterlockedCompareExchangePointer(
        &spl_terminal_signal_event, NULL, NULL);
    if (input == NULL || input == INVALID_HANDLE_VALUE || wake == NULL) {
        errno = EIO;
        return SPL_TERMINAL_READ_ERROR;
    }
    HANDLE waits[2] = {input, wake};
    for (;;) {
        if (InterlockedExchange(&spl_terminal_stop_pending, 0) != 0)
            return SPL_TERMINAL_READ_STOP;
        DWORD ready = WaitForMultipleObjects(2, waits, FALSE, INFINITE);
        if (ready == WAIT_OBJECT_0 + 1) {
            ResetEvent(wake);
            if (InterlockedExchange(&spl_terminal_stop_pending, 0) != 0)
                return SPL_TERMINAL_READ_STOP;
            continue;
        }
        if (ready != WAIT_OBJECT_0) {
            errno = EIO;
            return SPL_TERMINAL_READ_ERROR;
        }

        DWORD console_mode = 0;
        if (GetConsoleMode(input, &console_mode)) {
            for (;;) {
                INPUT_RECORD record;
                DWORD available = 0;
                if (!PeekConsoleInputW(input, &record, 1, &available)) {
                    errno = EIO;
                    return SPL_TERMINAL_READ_ERROR;
                }
                if (available == 0) break;
                if (record.EventType == WINDOW_BUFFER_SIZE_EVENT) {
                    DWORD consumed = 0;
                    if (!ReadConsoleInputW(input, &record, 1, &consumed) || consumed != 1) {
                        errno = EIO;
                        return SPL_TERMINAL_READ_ERROR;
                    }
                    return SPL_TERMINAL_READ_RESIZE;
                }
                if (record.EventType == KEY_EVENT && record.Event.KeyEvent.bKeyDown) break;
                DWORD consumed = 0;
                if (!ReadConsoleInputW(input, &record, 1, &consumed) || consumed != 1) {
                    errno = EIO;
                    return SPL_TERMINAL_READ_ERROR;
                }
            }
        }
        unsigned char byte = 0;
        int count = _read(0, &byte, 1);
        if (count == 1) return (int64_t)byte;
        if (count == 0) return SPL_TERMINAL_READ_EOF;
        if (errno == EINTR) continue;
        return SPL_TERMINAL_READ_ERROR;
    }
}

bool SPL_TERMINAL_SCOPE_END(int64_t scope) {
    if (scope <= 0 || scope != spl_terminal_scope_handle ||
        InterlockedCompareExchange(&spl_terminal_scope_lifecycle,
                                   SPL_TERMINAL_SCOPE_CLOSING,
                                   SPL_TERMINAL_SCOPE_ACTIVE) != SPL_TERMINAL_SCOPE_ACTIVE) {
        errno = EINVAL;
        return false;
    }
    if (!SetConsoleCtrlHandler(spl_terminal_console_handler, FALSE)) {
        InterlockedExchange(&spl_terminal_scope_lifecycle, SPL_TERMINAL_SCOPE_ACTIVE);
        errno = EIO;
        return false;
    }
    HANDLE wake = (HANDLE)InterlockedExchangePointer(&spl_terminal_signal_event, NULL);
    SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE();
    spl_terminal_wait_for_console_handlers();
    bool ok = true;
    if (wake != NULL) {
        SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE(wake);
        if (!CloseHandle(wake)) ok = false;
    }
    spl_terminal_scope_handle = 0;
    InterlockedExchange(&spl_terminal_stop_pending, 0);
    InterlockedExchange(&spl_terminal_scope_lifecycle, SPL_TERMINAL_SCOPE_IDLE);
    if (!ok) errno = EIO;
    return ok;
}

void SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE(void) {
    if (InterlockedCompareExchange(&spl_terminal_scope_lifecycle, 0, 0) ==
        SPL_TERMINAL_SCOPE_ACTIVE)
        (void)SPL_TERMINAL_SCOPE_END(spl_terminal_scope_handle);
}

#else

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdatomic.h>
#include <string.h>
#include <unistd.h>

#ifndef SPL_TERMINAL_SCOPE_SIGACTION
#define SPL_TERMINAL_SCOPE_SIGACTION(signum, action, previous) \
    sigaction((signum), (action), (previous))
#endif

_Static_assert(ATOMIC_INT_LOCK_FREE == 2,
               "terminal signal handler descriptors require lock-free atomics");

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
} SplTerminalSignalScopeState;

static SplTerminalSignalScopeState spl_terminal_signal_scope = {
    .active = false,
    .handle = 0,
    .pipe_read = -1,
    .pipe_write = -1,
    .installed_handlers = 0,
    .previous_handlers = {{{0}}}
};
static _Atomic int spl_terminal_signal_pipe_write = -1;
static _Atomic unsigned spl_terminal_signal_handlers_inflight = 0;
static _Atomic int spl_terminal_stop_pending = 0;
static _Atomic int spl_terminal_resize_pending = 0;
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
    atomic_fetch_add_explicit(&spl_terminal_signal_handlers_inflight, 1,
                              memory_order_acquire);
    if (signum == SIGWINCH) {
        atomic_store_explicit(&spl_terminal_resize_pending, 1, memory_order_release);
    } else {
        atomic_store_explicit(&spl_terminal_stop_pending, 1, memory_order_release);
    }
    int fd = atomic_load_explicit(&spl_terminal_signal_pipe_write,
                                  memory_order_acquire);
    SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED(fd);
    if (fd >= 0) {
        unsigned char wake = (unsigned char)signum;
        (void)write(fd, &wake, 1);
    }
    atomic_fetch_sub_explicit(&spl_terminal_signal_handlers_inflight, 1,
                              memory_order_release);
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
        if (SPL_TERMINAL_SCOPE_SIGACTION(
                spl_terminal_managed_signals[i],
                &spl_terminal_signal_scope.previous_handlers[i], NULL) != 0 &&
            *first_errno == 0) {
            *first_errno = errno;
        }
    }
}

static void spl_terminal_wait_for_handlers(void) {
    while (atomic_load_explicit(&spl_terminal_signal_handlers_inflight,
                                memory_order_acquire) != 0) {
        SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT();
    }
}

static void spl_terminal_close_pipe(int* first_errno) {
    if (spl_terminal_signal_scope.pipe_read >= 0) {
        SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE(spl_terminal_signal_scope.pipe_read);
        if (close(spl_terminal_signal_scope.pipe_read) != 0 && *first_errno == 0) {
            *first_errno = errno;
        }
    }
    if (spl_terminal_signal_scope.pipe_write >= 0) {
        SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE(spl_terminal_signal_scope.pipe_write);
        if (close(spl_terminal_signal_scope.pipe_write) != 0 && *first_errno == 0) {
            *first_errno = errno;
        }
    }
    spl_terminal_signal_scope.pipe_read = -1;
    spl_terminal_signal_scope.pipe_write = -1;
}

static void spl_terminal_retire_restore_wait_close(int installed_handlers,
                                                   int* first_errno) {
    atomic_store_explicit(&spl_terminal_signal_pipe_write, -1,
                          memory_order_release);
    SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE();
    spl_terminal_restore_handlers(installed_handlers, first_errno);
    spl_terminal_wait_for_handlers();
    spl_terminal_close_pipe(first_errno);
}

static int64_t spl_terminal_take_pending_signal(void) {
    sigset_t managed;
    sigset_t previous_mask;
    spl_terminal_managed_signal_set(&managed);
    bool masked = sigprocmask(SIG_BLOCK, &managed, &previous_mask) == 0;
    int stop = atomic_exchange_explicit(&spl_terminal_stop_pending, 0,
                                        memory_order_acq_rel);
    int resize = atomic_exchange_explicit(&spl_terminal_resize_pending, 0,
                                          memory_order_acq_rel);
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
    atomic_store(&spl_terminal_stop_pending, 0);
    atomic_store(&spl_terminal_resize_pending, 0);
    spl_terminal_signal_scope.installed_handlers = 0;
    atomic_store_explicit(&spl_terminal_signal_pipe_write, pipe_fds[1],
                          memory_order_release);

    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = spl_terminal_scope_signal_handler;
    sigemptyset(&action.sa_mask);
    action.sa_flags = 0;
    for (int i = 0; i < SPL_TERMINAL_SCOPE_SIGNAL_COUNT; i++) {
        if (SPL_TERMINAL_SCOPE_SIGACTION(
                spl_terminal_managed_signals[i], &action,
                &spl_terminal_signal_scope.previous_handlers[i]) != 0) {
            failure_errno = errno;
            spl_terminal_retire_restore_wait_close(
                spl_terminal_signal_scope.installed_handlers, &failure_errno);
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
        spl_terminal_retire_restore_wait_close(
            spl_terminal_signal_scope.installed_handlers, &failure_errno);
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

    spl_terminal_retire_restore_wait_close(
        spl_terminal_signal_scope.installed_handlers, &first_errno);
    spl_terminal_signal_scope.active = false;
    spl_terminal_signal_scope.handle = 0;
    spl_terminal_signal_scope.installed_handlers = 0;
    atomic_store(&spl_terminal_stop_pending, 0);
    atomic_store(&spl_terminal_resize_pending, 0);

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

void SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE(void) {
    if (spl_terminal_signal_scope.active)
        (void)SPL_TERMINAL_SCOPE_END(spl_terminal_signal_scope.handle);
}

#endif

#undef SPL_TERMINAL_SCOPE_BEGIN
#undef SPL_TERMINAL_SCOPE_READ
#undef SPL_TERMINAL_SCOPE_END
#undef SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE
#undef SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED
#undef SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE
#undef SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT
#undef SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE
#ifdef SPL_TERMINAL_SCOPE_SIGACTION
#undef SPL_TERMINAL_SCOPE_SIGACTION
#endif

#endif
