/*
 * Fork-without-exec implementation for test runner isolation.
 *
 * Key design decisions:
 * - Uses pipe() + fork() + dup2() for stdio capture
 * - poll() multiplexes reads from stdout/stderr pipes (avoids deadlock)
 * - Growing buffers via realloc for large test output
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

int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms) {
    (void)child_pid;
    (void)timeout_ms;
    return -1;
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

/* Initial and growth size for pipe read buffers */
#define PIPE_BUF_INIT  4096
#define PIPE_BUF_GROW  4096

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

int64_t rt_fork_parent_wait(int64_t child_pid, int64_t timeout_ms) {
    /* Reject invalid pids: kill(-1)/waitpid(-1) would signal/reap every
     * process the user owns (e.g. when a failed fork's -1 is passed in). */
    if (child_pid <= 0) {
        return -1;
    }

    /* Free any previous results */
    free_results();
    s_result_timed_out = false;
    s_result_signaled = false;

    int stdout_fd = s_stdout_read_fd;
    int stderr_fd = s_stderr_read_fd;
    s_stdout_read_fd = -1;
    s_stderr_read_fd = -1;

    /* Allocate growing buffers */
    size_t out_cap = PIPE_BUF_INIT;
    size_t out_len = 0;
    char* out_buf = (char*)SPL_MALLOC(out_cap, "fork_buf");
    if (!out_buf) {
        out_cap = 1;
        out_buf = (char*)SPL_CALLOC(1, 1, "fork_buf");
    }

    size_t err_cap = PIPE_BUF_INIT;
    size_t err_len = 0;
    char* err_buf = (char*)SPL_MALLOC(err_cap, "fork_buf");
    if (!err_buf) {
        err_cap = 1;
        err_buf = (char*)SPL_CALLOC(1, 1, "fork_buf");
    }
    if (!out_buf || !err_buf) {
        if (out_buf) SPL_FREE(out_buf);
        if (err_buf) SPL_FREE(err_buf);
        close(stdout_fd);
        close(stderr_fd);
        if (kill(-(pid_t)child_pid, SIGKILL) != 0) {
            (void)kill((pid_t)child_pid, SIGKILL);
        }
        int status;
        (void)waitpid_nointr((pid_t)child_pid, &status, 0);
        return -1;
    }

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
    int capture_failed = 0;
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
                /* Determine which buffer */
                char** buf_ptr;
                size_t* len_ptr;
                size_t* cap_ptr;
                int* open_ptr;

                if (fds[i].fd == stdout_fd) {
                    buf_ptr = &out_buf;
                    len_ptr = &out_len;
                    cap_ptr = &out_cap;
                    open_ptr = &stdout_open;
                } else {
                    buf_ptr = &err_buf;
                    len_ptr = &err_len;
                    cap_ptr = &err_cap;
                    open_ptr = &stderr_open;
                }

                /* Read available data */
                while (1) {
                    /* Grow buffer if needed */
                    if (*len_ptr + PIPE_BUF_GROW > *cap_ptr) {
                        size_t new_cap = *cap_ptr;
                        while (*len_ptr + PIPE_BUF_GROW > new_cap) new_cap *= 2;
                        char* new_buf = (char*)SPL_REALLOC(*buf_ptr, new_cap, "fork_buf");
                        if (!new_buf) {
                            capture_failed = 1;
                            *open_ptr = 0;
                            break;
                        }
                        *buf_ptr = new_buf;
                        *cap_ptr = new_cap;
                    }

                    ssize_t n = read(fds[i].fd, *buf_ptr + *len_ptr, *cap_ptr - *len_ptr - 1);
                    if (n > 0) {
                        *len_ptr += n;
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
        if (capture_failed) break;
        if (child_exited) {
            cleanup_descendants = stdout_open || stderr_open;
            break;
        }
    }

    /* Close pipe read ends */
    close(stdout_fd);
    close(stderr_fd);

    if (cleanup_descendants) {
        (void)kill(-(pid_t)child_pid, SIGKILL);
    }

    /* Null-terminate buffers */
    out_buf[out_len] = '\0';
    err_buf[err_len] = '\0';

    /* Store results for getter functions */
    s_result_stdout = out_buf;
    s_result_stderr = err_buf;

    /* Handle timeout: kill child */
    if (timed_out || wait_failed || capture_failed) {
        s_result_timed_out = timed_out != 0;
        if (kill(-(pid_t)child_pid, SIGKILL) != 0) {
            (void)kill((pid_t)child_pid, SIGKILL);
        }
        int status;
        (void)waitpid_nointr((pid_t)child_pid, &status, 0);
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
