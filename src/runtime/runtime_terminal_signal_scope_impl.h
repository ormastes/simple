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

#if defined(_WIN32)

#include <io.h>
#include <windows.h>

static PVOID volatile spl_terminal_signal_event;
static volatile LONG spl_terminal_stop_pending;
static volatile LONG spl_terminal_scope_active;
static volatile LONG spl_terminal_signal_handlers_inflight;
static int64_t spl_terminal_scope_handle;
static unsigned char spl_terminal_utf8_pending[4];
static int spl_terminal_utf8_pending_index;
static int spl_terminal_utf8_pending_len;
static WCHAR spl_terminal_pending_high_surrogate;

static BOOL WINAPI spl_terminal_console_handler(DWORD event) {
    InterlockedIncrement(&spl_terminal_signal_handlers_inflight);
    BOOL handled = FALSE;
    if (event == CTRL_C_EVENT || event == CTRL_BREAK_EVENT ||
        event == CTRL_CLOSE_EVENT || event == CTRL_LOGOFF_EVENT ||
        event == CTRL_SHUTDOWN_EVENT) {
        InterlockedExchange(&spl_terminal_stop_pending, 1);
        HANDLE signal_event = (HANDLE)InterlockedCompareExchangePointer(
            &spl_terminal_signal_event, NULL, NULL);
        if (signal_event != NULL) (void)SetEvent(signal_event);
        handled = TRUE;
    }
    InterlockedDecrement(&spl_terminal_signal_handlers_inflight);
    return handled;
}

static int64_t spl_terminal_windows_key_byte(WCHAR value) {
    if (value == 0) return -5;
    WCHAR text[2];
    int text_len = 1;
    if (value >= 0xd800 && value <= 0xdbff) {
        spl_terminal_pending_high_surrogate = value;
        return -5;
    }
    if (value >= 0xdc00 && value <= 0xdfff &&
        spl_terminal_pending_high_surrogate != 0) {
        text[0] = spl_terminal_pending_high_surrogate;
        text[1] = value;
        text_len = 2;
        spl_terminal_pending_high_surrogate = 0;
    } else {
        spl_terminal_pending_high_surrogate = 0;
        text[0] = value;
    }
    int count = WideCharToMultiByte(CP_UTF8, WC_ERR_INVALID_CHARS, text, text_len,
                                    (char*)spl_terminal_utf8_pending,
                                    (int)sizeof(spl_terminal_utf8_pending),
                                    NULL, NULL);
    if (count <= 0) return -4;
    spl_terminal_utf8_pending_index = 1;
    spl_terminal_utf8_pending_len = count;
    return spl_terminal_utf8_pending[0];
}

int64_t SPL_TERMINAL_SCOPE_BEGIN(void) {
    if (InterlockedCompareExchange(&spl_terminal_scope_active, 1, 0) != 0) {
        errno = EBUSY;
        return 0;
    }
    HANDLE signal_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    if (signal_event == NULL) {
        InterlockedExchange(&spl_terminal_scope_active, 0);
        errno = EIO;
        return 0;
    }
    InterlockedExchangePointer(&spl_terminal_signal_event, signal_event);
    InterlockedExchange(&spl_terminal_stop_pending, 0);
    spl_terminal_utf8_pending_index = 0;
    spl_terminal_utf8_pending_len = 0;
    spl_terminal_pending_high_surrogate = 0;
    if (
        !SetConsoleCtrlHandler(spl_terminal_console_handler, TRUE)) {
        InterlockedExchangePointer(&spl_terminal_signal_event, NULL);
        CloseHandle(signal_event);
        InterlockedExchange(&spl_terminal_scope_active, 0);
        errno = EIO;
        return 0;
    }
    spl_terminal_scope_handle++;
    if (spl_terminal_scope_handle <= 0) spl_terminal_scope_handle = 1;
    return spl_terminal_scope_handle;
}

int64_t SPL_TERMINAL_SCOPE_READ(int64_t scope) {
    if (InterlockedCompareExchange(&spl_terminal_scope_active, 1, 1) == 0 ||
        scope <= 0 || scope != spl_terminal_scope_handle) {
        errno = EINVAL;
        return -4;
    }
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    HANDLE signal_event = (HANDLE)InterlockedCompareExchangePointer(
        &spl_terminal_signal_event, NULL, NULL);
    if (input == NULL || input == INVALID_HANDLE_VALUE || signal_event == NULL) {
        errno = EIO;
        return -4;
    }
    HANDLE waits[2] = {input, signal_event};
    for (;;) {
        if (spl_terminal_utf8_pending_index < spl_terminal_utf8_pending_len) {
            return spl_terminal_utf8_pending[spl_terminal_utf8_pending_index++];
        }
        DWORD ready = WaitForMultipleObjects(2, waits, FALSE, INFINITE);
        if (ready == WAIT_OBJECT_0 + 1) {
            ResetEvent(signal_event);
            if (InterlockedExchange(&spl_terminal_stop_pending, 0) != 0) return -2;
            continue;
        }
        if (ready != WAIT_OBJECT_0) { errno = EIO; return -4; }
        INPUT_RECORD record;
        DWORD count = 0;
        if (!ReadConsoleInputW(input, &record, 1, &count)) {
            errno = EIO;
            return -4;
        }
        if (count == 0) continue;
        if (record.EventType == WINDOW_BUFFER_SIZE_EVENT) return -3;
        if (record.EventType != KEY_EVENT || !record.Event.KeyEvent.bKeyDown) continue;
        int64_t byte = spl_terminal_windows_key_byte(
            record.Event.KeyEvent.uChar.UnicodeChar);
        if (byte == -5) continue;
        return byte;
    }
}

bool SPL_TERMINAL_SCOPE_END(int64_t scope) {
    if (InterlockedCompareExchange(&spl_terminal_scope_active, 1, 1) == 0 ||
        scope <= 0 || scope != spl_terminal_scope_handle) {
        errno = EINVAL;
        return false;
    }
    HANDLE event = (HANDLE)InterlockedExchangePointer(
        &spl_terminal_signal_event, NULL);
    bool ok = SetConsoleCtrlHandler(spl_terminal_console_handler, FALSE) != 0;
    while (InterlockedCompareExchange(&spl_terminal_signal_handlers_inflight,
                                      0, 0) != 0) {
        Sleep(0);
    }
    InterlockedExchange(&spl_terminal_scope_active, 0);
    InterlockedExchange(&spl_terminal_stop_pending, 0);
    spl_terminal_utf8_pending_index = 0;
    spl_terminal_utf8_pending_len = 0;
    spl_terminal_pending_high_surrogate = 0;
    if (event != NULL && !CloseHandle(event)) ok = false;
    if (!ok) errno = EIO;
    return ok;
}

void SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE(void) {
    if (InterlockedCompareExchange(&spl_terminal_scope_active, 1, 1) != 0)
        (void)SPL_TERMINAL_SCOPE_END(spl_terminal_scope_handle);
}

#else

#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdatomic.h>
#include <string.h>
#include <unistd.h>

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
    false, 0, -1, -1, 0, {{0}}
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
        if (sigaction(spl_terminal_managed_signals[i],
                      &spl_terminal_signal_scope.previous_handlers[i], NULL) != 0 &&
            *first_errno == 0) {
            *first_errno = errno;
        }
    }
}

static void spl_terminal_wait_for_handlers(void) {
    while (atomic_load_explicit(&spl_terminal_signal_handlers_inflight,
                                memory_order_acquire) != 0) {
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
        if (sigaction(spl_terminal_managed_signals[i], &action,
                      &spl_terminal_signal_scope.previous_handlers[i]) != 0) {
            failure_errno = errno;
            atomic_store_explicit(&spl_terminal_signal_pipe_write, -1,
                                  memory_order_release);
            spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                          &failure_errno);
            spl_terminal_wait_for_handlers();
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
        atomic_store_explicit(&spl_terminal_signal_pipe_write, -1,
                              memory_order_release);
        spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                      &failure_errno);
        spl_terminal_wait_for_handlers();
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

    atomic_store_explicit(&spl_terminal_signal_pipe_write, -1,
                          memory_order_release);
    spl_terminal_restore_handlers(spl_terminal_signal_scope.installed_handlers,
                                  &first_errno);
    spl_terminal_wait_for_handlers();
    spl_terminal_close_pipe(&first_errno);
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

#endif
