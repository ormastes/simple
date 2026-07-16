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

SplArray* rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms) {
    (void)cmd; (void)cmd_len; (void)args; (void)timeout_ms;
    const char* error = "rt_process_run_timeout unsupported on Windows";
    SplArray* result = rt_array_new(3);
    rt_array_push(result, rt_string_new((const uint8_t*)"", 0));
    rt_array_push(result, rt_string_new((const uint8_t*)error, (uint64_t)strlen(error)));
    rt_array_push(result, rt_value_int(-1));
    return result;
}

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
#include "runtime_fork.h"

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

static SplArray* process_timeout_result(const char* stdout_text, const char* stderr_text, int64_t code, int timed_out, int64_t timeout_ms) {
    const char* out = stdout_text ? stdout_text : "";
    const char* err = stderr_text ? stderr_text : "";
    char* timeout_error = NULL;
    if (timed_out) {
        char marker[96];
        snprintf(marker, sizeof(marker), "[TIMEOUT: Process killed after %lldms]", (long long)timeout_ms);
        size_t err_len = strlen(err);
        size_t marker_len = strlen(marker);
        timeout_error = (char*)malloc(err_len + marker_len + 2);
        if (timeout_error) {
            memcpy(timeout_error, err, err_len);
            if (err_len > 0) timeout_error[err_len++] = '\n';
            memcpy(timeout_error + err_len, marker, marker_len + 1);
            err = timeout_error;
        }
    }
    SplArray* result = rt_array_new(3);
    rt_array_push(result, rt_string_new((const uint8_t*)out, (uint64_t)strlen(out)));
    rt_array_push(result, rt_string_new((const uint8_t*)err, (uint64_t)strlen(err)));
    rt_array_push(result, rt_value_int(code));
    free(timeout_error);
    return result;
}

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

static int64_t rt_process_spawn_piped_argv(const char* cmd, char** argv) {
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

    fflush(stdout);
    fflush(stderr);

    pid_t pid = fork();
    if (pid < 0) {
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
 * Fork + exec `cmd` with `args`, wiring up stdin/stdout pipes.
 * Returns the child PID on success, -1 on error.
 */
int64_t rt_process_spawn_piped(const char* cmd, SplArray* args) {
    int64_t argc = args ? spl_array_len(args) : 0;
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) return -1;
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < argc; i++) {
        SplValue v = spl_array_get(args, i);
        argv[i + 1] = (char*)(v.tag == SPL_STRING ? spl_as_str(v) : "");
    }
    argv[argc + 1] = NULL;
    int64_t pid = rt_process_spawn_piped_argv(cmd, argv);
    free(argv);
    return pid;
}

SplArray* rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms) {
    if (!cmd || cmd_len == 0 || cmd_len > SIZE_MAX - 1) {
        return process_timeout_result("", "missing command", -1, 0, timeout_ms);
    }

    char* cmd_c = (char*)malloc((size_t)cmd_len + 1);
    if (!cmd_c) return process_timeout_result("", "process spawn failed", -1, 0, timeout_ms);
    memcpy(cmd_c, cmd, (size_t)cmd_len);
    cmd_c[cmd_len] = '\0';

    int64_t argc = args ? rt_array_len(args) : 0;
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) {
        free(cmd_c);
        return process_timeout_result("", "process spawn failed", -1, 0, timeout_ms);
    }
    argv[0] = cmd_c;
    for (int64_t i = 0; i < argc; i++) {
        const uint8_t* data = rt_string_data(rt_array_get(args, i));
        argv[i + 1] = (char*)(data ? data : (const uint8_t*)"");
    }
    argv[argc + 1] = NULL;

    int64_t child_pid = rt_fork_child_setup();
    if (child_pid == 0) {
        int null_fd = open("/dev/null", O_RDONLY);
        if (null_fd >= 0) {
            (void)dup2(null_fd, STDIN_FILENO);
            close(null_fd);
        }
        (void)unsetenv("_SIMPLE_STACK_SET");
        execvp(cmd_c, argv);
        perror("rt_process_run_timeout execvp");
        rt_fork_child_exit(127);
    }

    free(argv);
    free(cmd_c);
    if (child_pid < 0) return process_timeout_result("", "process spawn failed", -1, 0, timeout_ms);

    int64_t code = rt_fork_parent_wait(child_pid, timeout_ms > 0 ? timeout_ms : 0);
    int timed_out = rt_fork_parent_timed_out() ? 1 : 0;
    if (rt_fork_parent_signaled()) code = -1;
    const char* out = rt_fork_parent_stdout();
    const char* err = rt_fork_parent_stderr();
    if (code == 127 && err && strstr(err, "rt_process_run_timeout execvp") != NULL) code = -1;
    return process_timeout_result(out, err, code, timed_out, timeout_ms);
}

int64_t rt_editor_spawn_simple_dap(void) {
    char* argv[] = {
        "src/compiler_rust/target/debug/simple",
        "run",
        "src/app/dap/simple_dap_main.spl",
        NULL
    };
    return rt_process_spawn_piped_argv(argv[0], argv);
}

bool rt_editor_start_simple_dap(int64_t pid) {
    const char* init = "Content-Length: 84\r\n\r\n{\"seq\":1,\"type\":\"request\",\"command\":\"initialize\",\"arguments\":{\"adapterID\":\"simple\"}}";
    const char* launch = "Content-Length: 113\r\n\r\n{\"seq\":2,\"type\":\"request\",\"command\":\"launch\",\"arguments\":{\"program\":\"src/app/dap/simple_dap_main.spl\",\"cwd\":\".\"}}";
    return rt_process_write_stdin(pid, init) && rt_process_write_stdin(pid, launch);
}

bool rt_editor_poll_simple_dap_stopped(int64_t pid) {
    static char dap_buf[65536];
    static size_t dap_len = 0;
    for (int i = 0; i < 16; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        if (!chunk || !*chunk) break;
        size_t n = strlen(chunk);
        if (dap_len + n >= sizeof(dap_buf)) {
            dap_len = 0;
        }
        memcpy(dap_buf + dap_len, chunk, n);
        dap_len += n;
        dap_buf[dap_len] = '\0';
    }
    return strstr(dap_buf, "\"type\":\"event\"") != NULL && strstr(dap_buf, "\"event\":\"stopped\"") != NULL;
}

bool rt_editor_wait_simple_dap_stopped(int64_t pid) {
    for (int i = 0; i < 40; i++) {
        if (rt_editor_poll_simple_dap_stopped(pid)) return true;
        usleep(100000);
    }
    return false;
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
