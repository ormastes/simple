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
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0600
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0600
#endif
#endif

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

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

#ifdef _WIN32

/* Windows process timeout/capture owner. */
#include <windows.h>

struct WinCapture {
    char* data;
    size_t len;
    size_t cap;
};

static void win_close_handle(HANDLE* handle) {
    if (*handle && *handle != INVALID_HANDLE_VALUE) CloseHandle(*handle);
    *handle = NULL;
}

static int win_capture_drain(HANDLE pipe, struct WinCapture* capture, size_t budget) {
    size_t drained = 0;
    for (;;) {
        DWORD available = 0;
        if (!PeekNamedPipe(pipe, NULL, 0, NULL, &available, NULL)) {
            return GetLastError() == ERROR_BROKEN_PIPE;
        }
        if (available == 0 || drained >= budget) return 1;

        DWORD chunk = available > 65536 ? 65536 : available;
        size_t remaining = budget - drained;
        if (remaining < chunk) chunk = (DWORD)remaining;
        if (capture->len > SIZE_MAX - (size_t)chunk - 1) return 0;
        size_t needed = capture->len + (size_t)chunk + 1;
        if (needed > capture->cap) {
            size_t new_cap = capture->cap ? capture->cap : 4096;
            while (new_cap < needed) {
                if (new_cap > SIZE_MAX / 2) {
                    new_cap = needed;
                    break;
                }
                new_cap *= 2;
            }
            char* grown = (char*)realloc(capture->data, new_cap);
            if (!grown) return 0;
            capture->data = grown;
            capture->cap = new_cap;
        }

        DWORD read_count = 0;
        if (!ReadFile(pipe, capture->data + capture->len, chunk, &read_count, NULL)) {
            return GetLastError() == ERROR_BROKEN_PIPE;
        }
        capture->len += (size_t)read_count;
        drained += (size_t)read_count;
        capture->data[capture->len] = '\0';
        if (read_count == 0) return 1;
    }
}

static char* win_filtered_environment(void) {
    static const char hidden[] = "_SIMPLE_STACK_SET=";
    LPCH source = GetEnvironmentStringsA();
    if (!source) return NULL;

    size_t total = 1;
    for (const char* entry = source; *entry; entry += strlen(entry) + 1) {
        size_t len = strlen(entry);
        if (_strnicmp(entry, hidden, sizeof(hidden) - 1) != 0) {
            if (total > SIZE_MAX - len - 1) {
                FreeEnvironmentStringsA(source);
                return NULL;
            }
            total += len + 1;
        }
    }
    if (total < 2) total = 2;

    char* filtered = (char*)malloc(total);
    if (!filtered) {
        FreeEnvironmentStringsA(source);
        return NULL;
    }
    char* out = filtered;
    for (const char* entry = source; *entry; entry += strlen(entry) + 1) {
        size_t len = strlen(entry);
        if (_strnicmp(entry, hidden, sizeof(hidden) - 1) != 0) {
            memcpy(out, entry, len + 1);
            out += len + 1;
        }
    }
    *out++ = '\0';
    if (out == filtered + 1) *out = '\0';
    FreeEnvironmentStringsA(source);
    return filtered;
}

SplArray* rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms) {
    const char* failure = NULL;
    const char** child_args = NULL;
    char* cmd_c = NULL;
    char* cmdline = NULL;
    char* environment = NULL;
    HANDLE stdout_read = NULL;
    HANDLE stdout_write = NULL;
    HANDLE stderr_read = NULL;
    HANDLE stderr_write = NULL;
    HANDLE null_input = NULL;
    HANDLE job = NULL;
    LPPROC_THREAD_ATTRIBUTE_LIST attributes = NULL;
    int attributes_initialized = 0;
    PROCESS_INFORMATION process = {0};
    struct WinCapture stdout_capture = {0};
    struct WinCapture stderr_capture = {0};
    int assigned_to_job = 0;
    int process_done = 0;
    int timed_out = 0;
    int64_t code = -1;

    if (!cmd || cmd_len == 0 || cmd_len > SIZE_MAX - 1 || memchr(cmd, '\0', (size_t)cmd_len)) {
        return process_timeout_result("", "missing command", -1, 0, timeout_ms);
    }
    cmd_c = (char*)malloc((size_t)cmd_len + 1);
    if (!cmd_c) return process_timeout_result("", "process spawn failed", -1, 0, timeout_ms);
    memcpy(cmd_c, cmd, (size_t)cmd_len);
    cmd_c[cmd_len] = '\0';

    int64_t argc = args ? rt_array_len(args) : 0;
    if (argc < 0 || (uint64_t)argc > SIZE_MAX / sizeof(char*)) {
        failure = "process spawn failed";
        goto finish;
    }
    if (argc > 0) {
        child_args = (const char**)malloc(sizeof(char*) * (size_t)argc);
        if (!child_args) {
            failure = "process spawn failed";
            goto finish;
        }
        for (int64_t i = 0; i < argc; i++) {
            const uint8_t* data = rt_string_data(rt_array_get(args, i));
            child_args[i] = (const char*)(data ? data : (const uint8_t*)"");
        }
    }
    cmdline = rt_windows_build_command_line(cmd_c, child_args, argc);
    environment = win_filtered_environment();
    if (!cmdline || !environment) {
        failure = "process spawn failed";
        goto finish;
    }

    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    if (!CreatePipe(&stdout_read, &stdout_write, &security, 0) ||
        !SetHandleInformation(stdout_read, HANDLE_FLAG_INHERIT, 0) ||
        !CreatePipe(&stderr_read, &stderr_write, &security, 0) ||
        !SetHandleInformation(stderr_read, HANDLE_FLAG_INHERIT, 0)) {
        failure = "process spawn failed";
        goto finish;
    }
    null_input = CreateFileA("NUL", GENERIC_READ, FILE_SHARE_READ | FILE_SHARE_WRITE,
                             &security, OPEN_EXISTING, FILE_ATTRIBUTE_NORMAL, NULL);
    if (null_input == INVALID_HANDLE_VALUE) {
        failure = "process spawn failed";
        goto finish;
    }

    job = CreateJobObjectA(NULL, NULL);
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits = {0};
    limits.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!job || !SetInformationJobObject(job, JobObjectExtendedLimitInformation,
                                          &limits, sizeof(limits))) {
        failure = "process spawn failed";
        goto finish;
    }

    SIZE_T attributes_size = 0;
    (void)InitializeProcThreadAttributeList(NULL, 1, 0, &attributes_size);
    if (attributes_size == 0) {
        failure = "process spawn failed";
        goto finish;
    }
    attributes = (LPPROC_THREAD_ATTRIBUTE_LIST)malloc(attributes_size);
    if (!attributes || !InitializeProcThreadAttributeList(attributes, 1, 0, &attributes_size)) {
        failure = "process spawn failed";
        goto finish;
    }
    attributes_initialized = 1;
    HANDLE inherited[] = {null_input, stdout_write, stderr_write};
    if (!UpdateProcThreadAttribute(attributes, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
                                   inherited, sizeof(inherited), NULL, NULL)) {
        failure = "process spawn failed";
        goto finish;
    }

    STARTUPINFOEXA startup = {0};
    startup.StartupInfo.cb = sizeof(startup);
    startup.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    startup.StartupInfo.hStdInput = null_input;
    startup.StartupInfo.hStdOutput = stdout_write;
    startup.StartupInfo.hStdError = stderr_write;
    DWORD creation_flags = CREATE_SUSPENDED | EXTENDED_STARTUPINFO_PRESENT | CREATE_NO_WINDOW;
    if (!CreateProcessA(NULL, cmdline, NULL, NULL, TRUE, creation_flags, environment, NULL,
                        &startup.StartupInfo, &process)) {
        failure = "process spawn failed";
        goto finish;
    }
    if (!AssignProcessToJobObject(job, process.hProcess)) {
        failure = "process spawn failed";
        goto finish;
    }
    assigned_to_job = 1;
    if (ResumeThread(process.hThread) == (DWORD)-1) {
        failure = "process spawn failed";
        goto finish;
    }

    win_close_handle(&process.hThread);
    win_close_handle(&stdout_write);
    win_close_handle(&stderr_write);
    win_close_handle(&null_input);

    ULONGLONG started = GetTickCount64();
    for (;;) {
        if (!win_capture_drain(stdout_read, &stdout_capture, 65536) ||
            !win_capture_drain(stderr_read, &stderr_capture, 65536)) {
            failure = "process capture failed";
            break;
        }

        DWORD wait_result = WaitForSingleObject(process.hProcess, 0);
        if (wait_result == WAIT_FAILED) {
            failure = "process wait failed";
            break;
        }
        DWORD wait_ms = 10;
        if (wait_result == WAIT_TIMEOUT && timeout_ms > 0) {
            ULONGLONG elapsed = GetTickCount64() - started;
            if (elapsed >= (ULONGLONG)timeout_ms) {
                timed_out = 1;
                break;
            }
            ULONGLONG remaining = (ULONGLONG)timeout_ms - elapsed;
            if (remaining < wait_ms) wait_ms = (DWORD)remaining;
        }
        if (wait_result == WAIT_TIMEOUT) {
            wait_result = WaitForSingleObject(process.hProcess, wait_ms);
        }
        if (wait_result == WAIT_OBJECT_0) {
            DWORD exit_code = 0;
            if (!GetExitCodeProcess(process.hProcess, &exit_code)) {
                failure = "process wait failed";
            } else {
                code = (int64_t)(int32_t)exit_code;
                process_done = 1;
            }
            break;
        }
        if (wait_result == WAIT_FAILED) {
            failure = "process wait failed";
            break;
        }
    }

finish:
    if (process.hProcess) {
        BOOL termination_requested = TRUE;
        if (assigned_to_job) {
            termination_requested = TerminateJobObject(job, 1);
            if (!termination_requested) {
                termination_requested = TerminateProcess(process.hProcess, 1);
                BOOL job_closed = CloseHandle(job);
                job = NULL;
                termination_requested = termination_requested || job_closed;
            }
        } else if (!process_done) {
            termination_requested = TerminateProcess(process.hProcess, 1);
        }
        if (!process_done && termination_requested) {
            process_done = WaitForSingleObject(process.hProcess, 5000) == WAIT_OBJECT_0;
        }
        if (!process_done) failure = "process termination failed";
    }
    win_close_handle(&process.hThread);
    win_close_handle(&stdout_write);
    win_close_handle(&stderr_write);
    win_close_handle(&null_input);
    if (stdout_read) (void)win_capture_drain(stdout_read, &stdout_capture, 1048576);
    if (stderr_read) (void)win_capture_drain(stderr_read, &stderr_capture, 1048576);

    const char* result_error = failure ? failure : stderr_capture.data;
    SplArray* result = process_timeout_result(stdout_capture.data, result_error,
                                              failure ? -1 : code, timed_out, timeout_ms);
    win_close_handle(&stdout_read);
    win_close_handle(&stderr_read);
    win_close_handle(&process.hProcess);
    win_close_handle(&job);
    if (attributes_initialized) DeleteProcThreadAttributeList(attributes);
    free(attributes);
    free(environment);
    free(cmdline);
    free(cmd_c);
    free(child_args);
    free(stdout_capture.data);
    free(stderr_capture.data);
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

#include "runtime_fork.h"

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
