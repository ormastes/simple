/*
 * Fork-without-exec implementation for test runner isolation.
 *
 * Key design decisions:
 * - Uses pipe() + fork() + dup2() for stdio capture
 * - poll() multiplexes reads from stdout/stderr pipes (avoids deadlock)
 * - Fixed-size head/tail buffers for bounded test output
 * - _exit() in child to avoid atexit handlers and double-flush
 * - SIGKILL on timeout (clean kill, OS reclaims everything)
 * - Signal handlers reset in child after fork
 * - FFI-friendly: wait stores results, getters retrieve them
 */

#ifdef _WIN32
/* Windows stub: fork not available */

#include "runtime_fork.h"
#include <string.h>
#include <stdlib.h>

int64_t rt_fork_child_setup(void) {
    return -1; /* Not supported on Windows */
}

int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms,
                                    uint64_t max_output_bytes) {
    (void)child_pid;
    (void)timeout_ms;
    (void)max_output_bytes;
    return -1;
}

int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms) {
    return rt_fork_parent_wait_bounded(child_pid, timeout_ms, 0);
}

bool rt_fork_parent_timed_out(void) { return false; }
bool rt_fork_parent_signaled(void) { return false; }

const char* rt_fork_parent_stdout(void) { return ""; }
const char* rt_fork_parent_stderr(void) { return "fork not supported on Windows"; }

void rt_fork_child_exit(int64_t exit_code) {
    exit((int)exit_code);
}

#else /* POSIX */

#include "runtime_fork.h"
#include "runtime_memtrack.h"

#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <sys/wait.h>
#include <poll.h>
#include <errno.h>
#include <fcntl.h>
#include <time.h>

/* Per-fork pipe state (stored by parent after fork) */
static int s_stdout_read_fd = -1;
static int s_stderr_read_fd = -1;

/* Stored results from last rt_fork_parent_wait() */
static char* s_result_stdout = NULL;
static char* s_result_stderr = NULL;
static bool s_result_timed_out = false;
static bool s_result_signaled = false;

/* Each stream retains at most 4 MiB of child output, split head/tail. */
#define FORK_CAPTURE_LIMIT (4U * 1024U * 1024U)
#define FORK_CAPTURE_HEAD (FORK_CAPTURE_LIMIT / 2U)
#define FORK_CAPTURE_TAIL (FORK_CAPTURE_LIMIT - FORK_CAPTURE_HEAD)
#define FORK_CAPTURE_MARKER_MAX 96U
#define PIPE_READ_CHUNK 4096U

typedef struct {
    char* data;
    uint64_t total;
    size_t head_len;
    size_t tail_len;
    size_t tail_start;
    size_t head_limit;
    size_t tail_limit;
} ForkCapture;

static void drain_capture_fds(int stdout_fd, ForkCapture* stdout_capture,
                              int stderr_fd, ForkCapture* stderr_capture);

static void reverse_bytes(char* data, size_t len) {
    for (size_t left = 0, right = len ? len - 1 : 0; left < right; left++, right--) {
        char tmp = data[left];
        data[left] = data[right];
        data[right] = tmp;
    }
}

static void capture_append(ForkCapture* capture, const char* bytes, size_t len) {
    if (UINT64_MAX - capture->total < len) capture->total = UINT64_MAX;
    else capture->total += (uint64_t)len;

    size_t head_add = capture->head_limit - capture->head_len;
    if (head_add > len) head_add = len;
    memcpy(capture->data + capture->head_len, bytes, head_add);
    capture->head_len += head_add;
    bytes += head_add;
    len -= head_add;
    if (len == 0) return;

    if (capture->tail_limit == 0) return;
    char* tail = capture->data + capture->head_limit;
    if (len >= capture->tail_limit) {
        memcpy(tail, bytes + len - capture->tail_limit, capture->tail_limit);
        capture->tail_start = 0;
        capture->tail_len = capture->tail_limit;
        return;
    }

    size_t overflow = capture->tail_len + len > capture->tail_limit
        ? capture->tail_len + len - capture->tail_limit : 0;
    capture->tail_start = (capture->tail_start + overflow) % capture->tail_limit;
    capture->tail_len -= overflow;
    size_t write_at = (capture->tail_start + capture->tail_len) % capture->tail_limit;
    size_t first = capture->tail_limit - write_at;
    if (first > len) first = len;
    memcpy(tail + write_at, bytes, first);
    memcpy(tail, bytes + first, len - first);
    capture->tail_len += len;
}

static size_t capture_finish(ForkCapture* capture) {
    char* tail = capture->data + capture->head_limit;
    if (capture->tail_start != 0 && capture->tail_len != 0) {
        reverse_bytes(tail, capture->tail_start);
        reverse_bytes(tail + capture->tail_start, capture->tail_len - capture->tail_start);
        reverse_bytes(tail, capture->tail_len);
        capture->tail_start = 0;
    }

    size_t marker_len = 0;
    if (capture->total > capture->head_len + capture->tail_len) {
        char marker[FORK_CAPTURE_MARKER_MAX];
        uint64_t omitted = capture->total - capture->head_len - capture->tail_len;
        int written = snprintf(marker, sizeof(marker), "\n[output truncated: %llu bytes omitted]\n",
                               (unsigned long long)omitted);
        if (written > 0) marker_len = (size_t)written;
        memmove(capture->data + capture->head_len + marker_len, tail, capture->tail_len);
        memcpy(capture->data + capture->head_len, marker, marker_len);
    } else {
        memmove(capture->data + capture->head_len, tail, capture->tail_len);
    }
    size_t result_len = capture->head_len + marker_len + capture->tail_len;
    capture->data[result_len] = '\0';
    return result_len;
}

static void set_nonblocking(int fd) {
    int flags = fcntl(fd, F_GETFL, 0);
    if (flags >= 0) {
        fcntl(fd, F_SETFL, flags | O_NONBLOCK);
    }
}

/* Free previous results */
static void free_results(void) {
    if (s_result_stdout) { SPL_FREE(s_result_stdout); s_result_stdout = NULL; }
    if (s_result_stderr) { SPL_FREE(s_result_stderr); s_result_stderr = NULL; }
}

static pid_t waitpid_nointr(pid_t pid, int* status, int options) {
    pid_t waited;
    do {
        waited = waitpid(pid, status, options);
    } while (waited < 0 && errno == EINTR);
    return waited;
}

int64_t rt_fork_child_setup(void) {
    int stdout_pipe[2]; /* [0]=read, [1]=write */
    int stderr_pipe[2];

    if (pipe(stdout_pipe) < 0) {
        return -1;
    }
    if (pipe(stderr_pipe) < 0) {
        close(stdout_pipe[0]);
        close(stdout_pipe[1]);
        return -1;
    }

    /* Flush parent stdio before fork to avoid double-output */
    fflush(stdout);
    fflush(stderr);

    pid_t pid = fork();
    if (pid < 0) {
        /* Fork failed */
        close(stdout_pipe[0]);
        close(stdout_pipe[1]);
        close(stderr_pipe[0]);
        close(stderr_pipe[1]);
        return -1;
    }

    if (pid == 0) {
        /* === CHILD PROCESS === */

        /* Own a process group so timeout cleanup includes descendants. */
        (void)setpgid(0, 0);

        /* Close read ends (parent uses these) */
        close(stdout_pipe[0]);
        close(stderr_pipe[0]);

        /* Redirect stdout/stderr to pipe write ends */
        dup2(stdout_pipe[1], STDOUT_FILENO);
        dup2(stderr_pipe[1], STDERR_FILENO);

        /* Close original write ends (now duped to fd 1/2) */
        close(stdout_pipe[1]);
        close(stderr_pipe[1]);

        /* Reset signal handlers to default (avoid inheriting parent's handlers) */
        signal(SIGINT, SIG_DFL);
        signal(SIGTERM, SIG_DFL);
        signal(SIGPIPE, SIG_DFL);

        return 0; /* Child returns 0 */
    }

    /* === PARENT PROCESS === */

    /* Close the race where the parent reaches timeout before the child sets it. */
    (void)setpgid(pid, pid);

    /* Close write ends (child uses these) */
    close(stdout_pipe[1]);
    close(stderr_pipe[1]);

    /* Store read ends for rt_fork_parent_wait */
    s_stdout_read_fd = stdout_pipe[0];
    s_stderr_read_fd = stderr_pipe[0];

    return (int64_t)pid;
}

int64_t rt_fork_parent_wait_bounded(int64_t child_pid, int64_t timeout_ms,
                                    uint64_t max_output_bytes) {
    /* Reject invalid pids: kill(-1)/waitpid(-1) would signal/reap every
     * process the user owns (e.g. when a failed fork's -1 is passed in). */
    if (child_pid <= 0) {
        return -1;
    }
    if (max_output_bytes > SIZE_MAX - FORK_CAPTURE_MARKER_MAX - 1U) return -1;

    /* Free any previous results */
    free_results();
    s_result_timed_out = false;
    s_result_signaled = false;

    int stdout_fd = s_stdout_read_fd;
    int stderr_fd = s_stderr_read_fd;
    s_stdout_read_fd = -1;
    s_stderr_read_fd = -1;

    size_t capture_limit = (size_t)max_output_bytes;
    /* Allocate bounded captures, plus marker and terminator space. */
    char* out_buf = (char*)SPL_MALLOC(capture_limit + FORK_CAPTURE_MARKER_MAX + 1U, "fork_buf");
    char* err_buf = (char*)SPL_MALLOC(capture_limit + FORK_CAPTURE_MARKER_MAX + 1U, "fork_buf");
    if (!out_buf || !err_buf) {
        if (out_buf) SPL_FREE(out_buf);
        if (err_buf) SPL_FREE(err_buf);
        if (kill(-(pid_t)child_pid, SIGKILL) != 0) {
            (void)kill((pid_t)child_pid, SIGKILL);
        }
        int status;
        (void)waitpid_nointr((pid_t)child_pid, &status, 0);
        close(stdout_fd);
        close(stderr_fd);
        return -1;
    }
    size_t head_limit = capture_limit / 2U + capture_limit % 2U;
    size_t tail_limit = capture_limit / 2U;
    ForkCapture out_capture = {out_buf, 0, 0, 0, 0, head_limit, tail_limit};
    ForkCapture err_capture = {err_buf, 0, 0, 0, 0, head_limit, tail_limit};

    /* Set non-blocking for poll */
    set_nonblocking(stdout_fd);
    set_nonblocking(stderr_fd);

    /* poll() loop: read from both pipes until both close */
    int stdout_open = 1;
    int stderr_open = 1;
    int timed_out = 0;
    int child_exited = 0;
    int child_status = 0;
    int cleanup_descendants = 0;
    int wait_failed = 0;

    /* Calculate deadline */
    struct timespec ts_start;
    clock_gettime(CLOCK_MONOTONIC, &ts_start);
    int64_t deadline_ms = 0;
    if (timeout_ms > 0) {
        deadline_ms = (ts_start.tv_sec * 1000 + ts_start.tv_nsec / 1000000) + timeout_ms;
    }

    while (stdout_open || stderr_open) {
        if (!child_exited) {
            pid_t waited = waitpid_nointr((pid_t)child_pid, &child_status, WNOHANG);
            if (waited == (pid_t)child_pid) child_exited = 1;
        }
        struct pollfd fds[2];
        int nfds = 0;

        if (stdout_open) {
            fds[nfds].fd = stdout_fd;
            fds[nfds].events = POLLIN;
            fds[nfds].revents = 0;
            nfds++;
        }
        if (stderr_open) {
            fds[nfds].fd = stderr_fd;
            fds[nfds].events = POLLIN;
            fds[nfds].revents = 0;
            nfds++;
        }

        /* Calculate remaining time */
        /* Wake periodically to observe a child whose descendants retain pipe fds. */
        int poll_timeout = 50;
        if (timeout_ms > 0) {
            struct timespec ts_now;
            clock_gettime(CLOCK_MONOTONIC, &ts_now);
            int64_t now_ms = ts_now.tv_sec * 1000 + ts_now.tv_nsec / 1000000;
            int64_t remaining = deadline_ms - now_ms;
            if (remaining <= 0) {
                timed_out = 1;
                break;
            }
            if (remaining < poll_timeout) poll_timeout = (int)remaining;
        }

        int ret = poll(fds, nfds, poll_timeout);
        if (ret < 0) {
            if (errno == EINTR) continue;
            wait_failed = 1;
            break;
        }
        if (ret == 0) {
            if (child_exited) {
                cleanup_descendants = stdout_open || stderr_open;
                break;
            }
            continue;
        }

        /* Process events */
        for (int i = 0; i < nfds; i++) {
            if (fds[i].revents & (POLLIN | POLLHUP)) {
                /* Determine which bounded capture owns this pipe. */
                ForkCapture* capture;
                int* open_ptr;

                if (fds[i].fd == stdout_fd) {
                    capture = &out_capture;
                    open_ptr = &stdout_open;
                } else {
                    capture = &err_capture;
                    open_ptr = &stderr_open;
                }

                /* Read available data */
                while (1) {
                    char chunk[PIPE_READ_CHUNK];
                    ssize_t n = read(fds[i].fd, chunk, sizeof(chunk));
                    if (n > 0) {
                        capture_append(capture, chunk, (size_t)n);
                    } else if (n == 0) {
                        /* EOF */
                        *open_ptr = 0;
                        break;
                    } else {
                        /* EAGAIN = no more data right now */
                        if (errno == EAGAIN || errno == EWOULDBLOCK) break;
                        *open_ptr = 0;
                        break;
                    }
                }
            }
            if (fds[i].revents & (POLLERR | POLLNVAL)) {
                if (fds[i].fd == stdout_fd) stdout_open = 0;
                else stderr_open = 0;
            }
        }
        if (child_exited) {
            cleanup_descendants = stdout_open || stderr_open;
            break;
        }
    }

    int forced_cleanup = cleanup_descendants || timed_out || wait_failed;
    if (forced_cleanup) {
        if (kill(-(pid_t)child_pid, SIGKILL) != 0) {
            (void)kill((pid_t)child_pid, SIGKILL);
        }
        if (!child_exited) {
            pid_t waited = waitpid_nointr((pid_t)child_pid, &child_status, 0);
            child_exited = waited == (pid_t)child_pid;
        }
        drain_capture_fds(stdout_fd, &out_capture, stderr_fd, &err_capture);
    }

    close(stdout_fd);
    close(stderr_fd);

    /* Linearize retained head/tail data and insert truncation markers. */
    (void)capture_finish(&out_capture);
    (void)capture_finish(&err_capture);

    /* Store results for getter functions */
    s_result_stdout = out_buf;
    s_result_stderr = err_buf;

    /* Timeout/wait failure cleanup completed before the final pipe drain. */
    if (timed_out || wait_failed) {
        s_result_timed_out = timed_out != 0;
        return -1;
    }

    /* Wait for child to finish */
    int status = child_status;
    pid_t waited = child_exited ? (pid_t)child_pid : waitpid_nointr((pid_t)child_pid, &status, 0);

    if (waited < 0) {
        return -1;
    } else if (WIFEXITED(status)) {
        return (int64_t)WEXITSTATUS(status);
    } else if (WIFSIGNALED(status)) {
        s_result_signaled = true;
        return (int64_t)(128 + WTERMSIG(status));
    }
    return -1;
}

static void drain_capture_fds(int stdout_fd, ForkCapture* stdout_capture,
                              int stderr_fd, ForkCapture* stderr_capture) {
    struct pollfd fds[2] = {
        {stdout_fd, POLLIN | POLLHUP, 0},
        {stderr_fd, POLLIN | POLLHUP, 0},
    };
    ForkCapture* captures[2] = {stdout_capture, stderr_capture};
    struct timespec started;
    clock_gettime(CLOCK_MONOTONIC, &started);
    int64_t deadline_ms = started.tv_sec * 1000 + started.tv_nsec / 1000000 + 100;

    while (fds[0].fd >= 0 || fds[1].fd >= 0) {
        struct timespec now;
        clock_gettime(CLOCK_MONOTONIC, &now);
        int64_t remaining = deadline_ms - (now.tv_sec * 1000 + now.tv_nsec / 1000000);
        if (remaining <= 0) break;
        int ready = poll(fds, 2, (int)remaining);
        if (ready < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (ready == 0) break;

        for (int index = 0; index < 2; index++) {
            if (fds[index].fd < 0 || fds[index].revents == 0) continue;
            if (fds[index].revents & POLLNVAL) {
                fds[index].fd = -1;
                continue;
            }
            for (;;) {
                char chunk[PIPE_READ_CHUNK];
                ssize_t count = read(fds[index].fd, chunk, sizeof(chunk));
                if (count > 0) {
                    capture_append(captures[index], chunk, (size_t)count);
                } else if (count == 0) {
                    fds[index].fd = -1;
                    break;
                } else if (errno == EINTR) {
                    continue;
                } else {
                    if (errno != EAGAIN && errno != EWOULDBLOCK) fds[index].fd = -1;
                    break;
                }
            }
            fds[index].revents = 0;
        }
    }
}

int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms) {
    return rt_fork_parent_wait_bounded(child_pid, timeout_ms, FORK_CAPTURE_LIMIT);
}

bool rt_fork_parent_timed_out(void) {
    return s_result_timed_out;
}

bool rt_fork_parent_signaled(void) {
    return s_result_signaled;
}

const char* rt_fork_parent_stdout(void) {
    return s_result_stdout ? s_result_stdout : "";
}

const char* rt_fork_parent_stderr(void) {
    return s_result_stderr ? s_result_stderr : "";
}

void rt_fork_child_exit(int64_t exit_code) {
    _exit((int)exit_code);
}

#endif /* _WIN32 / POSIX */
