/*
 * Piped-process support for the editor LSP transport.
 *
 * Implements rt_process_spawn_piped / rt_process_write_stdin /
 * rt_process_read_stdout / rt_process_is_alive.
 *
 * rt_process_kill is provided by platform/unix_common.h (raw-pid kill).
 *
 * Design:
 * - Static process table keyed by PID (linear scan, max 16 entries)
 * - rt_process_spawn_piped returns the real OS PID as the handle
 * - rt_process_is_alive lazy-closes fds when child exits
 * - rt_process_read_stdout is non-blocking (O_NONBLOCK); returns "" if no data
 * - Single static read buffer per call (same pattern as runtime_fork.c)
 *
 * Build: cc -c -fPIC -O2 -std=gnu11 -I src/runtime src/runtime/runtime_process.c
 */

#ifdef _WIN32

/* Windows stub — exec/pipe process management not yet supported */
#include "runtime.h"
#include <string.h>

int64_t rt_process_spawn_piped(const char* cmd, SplArray* args) {
    (void)cmd; (void)args;
    return -1;
}
bool rt_process_write_stdin(int64_t pid, const char* data) {
    (void)pid; (void)data;
    return false;
}
const char* rt_process_read_stdout(int64_t pid) {
    (void)pid;
    return "";
}
bool rt_process_is_alive(int64_t pid) {
    (void)pid;
    return false;
}

#else /* POSIX */

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <errno.h>

/* ===== Process table ===== */

#define RT_PROC_MAX 16
#define RT_PROC_READ_BUF 8192

struct RtProcSlot {
    pid_t pid;       /* 0 = empty */
    int   stdin_fd;  /* parent writes here  → child's stdin */
    int   stdout_fd; /* parent reads here   ← child's stdout */
};

static struct RtProcSlot s_procs[RT_PROC_MAX];

/* Static read buffer — returned pointer is valid until the next call */
static char s_read_buf[RT_PROC_READ_BUF];

/* ===== Internal helpers ===== */

static struct RtProcSlot* proc_find(pid_t pid) {
    for (int i = 0; i < RT_PROC_MAX; i++) {
        if (s_procs[i].pid == pid) return &s_procs[i];
    }
    return NULL;
}

static struct RtProcSlot* proc_alloc(void) {
    for (int i = 0; i < RT_PROC_MAX; i++) {
        if (s_procs[i].pid == 0) return &s_procs[i];
    }
    return NULL;
}

static void proc_free(struct RtProcSlot* slot) {
    if (!slot) return;
    if (slot->stdin_fd >= 0)  { close(slot->stdin_fd);  slot->stdin_fd  = -1; }
    if (slot->stdout_fd >= 0) { close(slot->stdout_fd); slot->stdout_fd = -1; }
    slot->pid = 0;
}

/* ===== Public API ===== */

/*
 * Fork + exec `cmd` with `args`, wiring up stdin/stdout pipes.
 * Returns the child PID on success, -1 on error.
 */
int64_t rt_process_spawn_piped(const char* cmd, SplArray* args) {
    if (!cmd || !*cmd) return -1;

    struct RtProcSlot* slot = proc_alloc();
    if (!slot) return -1;

    /* stdin_pipe[0] = child reads, stdin_pipe[1] = parent writes */
    int stdin_pipe[2];
    /* stdout_pipe[0] = parent reads, stdout_pipe[1] = child writes */
    int stdout_pipe[2];

    if (pipe(stdin_pipe) < 0) return -1;
    if (pipe(stdout_pipe) < 0) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        return -1;
    }

    /* Build argv from SplArray */
    int64_t argc = args ? spl_array_len(args) : 0;
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        return -1;
    }
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < argc; i++) {
        SplValue v = spl_array_get(args, i);
        argv[i + 1] = (char*)(v.tag == SPL_STRING ? spl_as_str(v) : "");
    }
    argv[argc + 1] = NULL;

    fflush(stdout);
    fflush(stderr);

    pid_t pid = fork();
    if (pid < 0) {
        free(argv);
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        return -1;
    }

    if (pid == 0) {
        /* === CHILD === */
        /* Wire pipes to stdio */
        dup2(stdin_pipe[0],  STDIN_FILENO);
        dup2(stdout_pipe[1], STDOUT_FILENO);

        /* Close all parent-side fds */
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);

        /* Reset signal handlers */
        signal(SIGINT,  SIG_DFL);
        signal(SIGTERM, SIG_DFL);
        signal(SIGPIPE, SIG_DFL);

        execvp(cmd, argv);
        _exit(127); /* exec failed */
    }

    /* === PARENT === */
    free(argv);

    /* Close child-side ends */
    close(stdin_pipe[0]);
    close(stdout_pipe[1]);

    /* Set stdout_fd non-blocking so reads don't hang */
    int flags = fcntl(stdout_pipe[0], F_GETFL, 0);
    if (flags >= 0) fcntl(stdout_pipe[0], F_SETFL, flags | O_NONBLOCK);

    slot->pid       = pid;
    slot->stdin_fd  = stdin_pipe[1];
    slot->stdout_fd = stdout_pipe[0];

    return (int64_t)pid;
}

/*
 * Write `data` to the process's stdin.
 * Returns true on success, false on error or unknown pid.
 */
bool rt_process_write_stdin(int64_t pid, const char* data) {
    if (pid <= 0 || !data) return false;
    struct RtProcSlot* slot = proc_find((pid_t)pid);
    if (!slot || slot->stdin_fd < 0) return false;

    size_t len = strlen(data);
    if (len == 0) return true;

    ssize_t written = write(slot->stdin_fd, data, len);
    return written == (ssize_t)len;
}

/*
 * Non-blocking read from the process's stdout.
 * Returns available data (may be partial), or "" if nothing ready.
 * The returned pointer is valid until the next call.
 */
const char* rt_process_read_stdout(int64_t pid) {
    s_read_buf[0] = '\0';
    if (pid <= 0) return s_read_buf;

    struct RtProcSlot* slot = proc_find((pid_t)pid);
    if (!slot || slot->stdout_fd < 0) return s_read_buf;

    ssize_t n = read(slot->stdout_fd, s_read_buf, RT_PROC_READ_BUF - 1);
    if (n > 0) {
        s_read_buf[n] = '\0';
    } else {
        s_read_buf[0] = '\0';
    }
    return s_read_buf;
}

/*
 * Returns true if the process is still alive.
 * Lazily closes fds and clears the table entry when death is detected.
 */
bool rt_process_is_alive(int64_t pid) {
    if (pid <= 0) return false;
    struct RtProcSlot* slot = proc_find((pid_t)pid);
    if (!slot) return false;

    int status;
    pid_t result = waitpid(slot->pid, &status, WNOHANG);
    if (result == 0) return true;   /* still running */

    /* Process exited or error — clean up */
    proc_free(slot);
    return false;
}

#endif /* POSIX */
