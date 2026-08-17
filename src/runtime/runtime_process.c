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

#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(SIMPLE_CORE_C_STANDALONE)
#ifdef _WIN32
#include <windows.h>
#else
#include <errno.h>
#include <signal.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

/*
 * The standalone core-C archive does not compile platform/platform.h, whose
 * normal hosted owner provides these two lifecycle helpers. MCP and LSP keep
 * process sessions in their reachable entry closure even when startup only
 * performs initialize/tools-list, so leaving the symbols absent makes a fresh
 * native server abort in dyld before main.
 */
bool rt_process_is_running(int64_t pid) {
    if (pid <= 0) return false;
#ifdef _WIN32
    HANDLE process = OpenProcess(SYNCHRONIZE, FALSE, (DWORD)pid);
    if (!process) return false;
    DWORD status = WaitForSingleObject(process, 0);
    CloseHandle(process);
    return status == WAIT_TIMEOUT;
#else
    int status = 0;
    pid_t waited = waitpid((pid_t)pid, &status, WNOHANG);
    if (waited == 0) return true;
    if (waited == (pid_t)pid) return false;
    if (errno == ECHILD) return kill((pid_t)pid, 0) == 0 || errno == EPERM;
    return false;
#endif
}

bool rt_process_kill(int64_t pid) {
    if (pid <= 0) return false;
#ifdef _WIN32
    HANDLE process = OpenProcess(PROCESS_TERMINATE | SYNCHRONIZE, FALSE, (DWORD)pid);
    if (!process) return false;
    BOOL terminated = TerminateProcess(process, 1);
    if (terminated) WaitForSingleObject(process, 1000);
    CloseHandle(process);
    return terminated != 0;
#else
    if (kill((pid_t)pid, SIGTERM) != 0 && errno != ESRCH) return false;
    return true;
#endif
}
#endif

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
#include "platform/windows_command_line_private.h"

struct WinCapture {
    char* data;
    size_t len;
    size_t cap;
    uint64_t total;
    size_t limit;
    size_t head_len;
    size_t tail_len;
    size_t tail_start;
};

#define WIN_CAPTURE_MARKER_MAX 96U

static void win_reverse_bytes(char* data, size_t len) {
    for (size_t left = 0, right = len ? len - 1 : 0; left < right; left++, right--) {
        char byte = data[left];
        data[left] = data[right];
        data[right] = byte;
    }
}

static int win_capture_append(struct WinCapture* capture, const char* bytes, size_t len) {
    if (capture->limit == SIZE_MAX) {
        if (capture->len > SIZE_MAX - len - 1) return 0;
        size_t needed = capture->len + len + 1;
        if (needed > capture->cap) {
            size_t new_cap = capture->cap ? capture->cap : 4096;
            while (new_cap < needed) {
                if (new_cap > SIZE_MAX / 2) { new_cap = needed; break; }
                new_cap *= 2;
            }
            char* grown = (char*)realloc(capture->data, new_cap);
            if (!grown) return 0;
            capture->data = grown;
            capture->cap = new_cap;
        }
        memcpy(capture->data + capture->len, bytes, len);
        capture->len += len;
        capture->data[capture->len] = '\0';
        return 1;
    }

    if (UINT64_MAX - capture->total < len) capture->total = UINT64_MAX;
    else capture->total += (uint64_t)len;
    if (!capture->data) {
        if (capture->limit > SIZE_MAX - WIN_CAPTURE_MARKER_MAX - 1U) return 0;
        capture->cap = capture->limit + WIN_CAPTURE_MARKER_MAX + 1U;
        capture->data = (char*)malloc(capture->cap);
        if (!capture->data) return 0;
    }

    size_t head_limit = capture->limit / 2U + capture->limit % 2U;
    size_t tail_limit = capture->limit / 2U;
    size_t head_add = head_limit - capture->head_len;
    if (head_add > len) head_add = len;
    memcpy(capture->data + capture->head_len, bytes, head_add);
    capture->head_len += head_add;
    bytes += head_add;
    len -= head_add;
    if (len == 0 || tail_limit == 0) return 1;

    char* tail = capture->data + head_limit;
    if (len >= tail_limit) {
        memcpy(tail, bytes + len - tail_limit, tail_limit);
        capture->tail_start = 0;
        capture->tail_len = tail_limit;
        return 1;
    }
    size_t overflow = capture->tail_len + len > tail_limit
        ? capture->tail_len + len - tail_limit : 0;
    capture->tail_start = (capture->tail_start + overflow) % tail_limit;
    capture->tail_len -= overflow;
    size_t write_at = (capture->tail_start + capture->tail_len) % tail_limit;
    size_t first = tail_limit - write_at;
    if (first > len) first = len;
    memcpy(tail + write_at, bytes, first);
    memcpy(tail, bytes + first, len - first);
    capture->tail_len += len;
    return 1;
}

static void win_capture_finish(struct WinCapture* capture) {
    if (capture->limit == SIZE_MAX || !capture->data) return;
    size_t head_limit = capture->limit / 2U + capture->limit % 2U;
    char* tail = capture->data + head_limit;
    if (capture->tail_start != 0 && capture->tail_len != 0) {
        win_reverse_bytes(tail, capture->tail_start);
        win_reverse_bytes(tail + capture->tail_start, capture->tail_len - capture->tail_start);
        win_reverse_bytes(tail, capture->tail_len);
    }
    size_t marker_len = 0;
    if (capture->total > capture->head_len + capture->tail_len) {
        char marker[WIN_CAPTURE_MARKER_MAX];
        uint64_t omitted = capture->total - capture->head_len - capture->tail_len;
        int written = snprintf(marker, sizeof(marker), "\n[output truncated: %llu bytes omitted]\n",
                               (unsigned long long)omitted);
        if (written > 0) marker_len = (size_t)written;
        memmove(capture->data + capture->head_len + marker_len, tail, capture->tail_len);
        memcpy(capture->data + capture->head_len, marker, marker_len);
    } else {
        memmove(capture->data + capture->head_len, tail, capture->tail_len);
    }
    capture->len = capture->head_len + marker_len + capture->tail_len;
    capture->data[capture->len] = '\0';
}

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
        char bytes[65536];
        DWORD read_count = 0;
        if (!ReadFile(pipe, bytes, chunk, &read_count, NULL)) {
            return GetLastError() == ERROR_BROKEN_PIPE;
        }
        drained += (size_t)read_count;
        if (!win_capture_append(capture, bytes, (size_t)read_count)) return 0;
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

static SplArray* win_process_run_capture(const char* cmd, uint64_t cmd_len, SplArray* args,
                                         int64_t timeout_ms, int64_t max_output_bytes) {
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
    if (max_output_bytes < -1 ||
        (max_output_bytes >= 0 && (uint64_t)max_output_bytes > SIZE_MAX - WIN_CAPTURE_MARKER_MAX - 1U)) {
        return process_timeout_result("", "", -1, 0, timeout_ms);
    }
    stdout_capture.limit = max_output_bytes < 0 ? SIZE_MAX : (size_t)max_output_bytes;
    stderr_capture.limit = stdout_capture.limit;
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
    cmdline = win_cmd_build_line(cmd_c, child_args, argc);
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
    win_capture_finish(&stdout_capture);
    win_capture_finish(&stderr_capture);

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

/* (cmd_ptr, cmd_len, args, timeout_ms) -> RuntimeValue (array), per
 * runtime_sffi.rs:1423. The result is built by win_process_run_capture with
 * rt_array_new / rt_string_new, so it is already a properly tagged
 * RuntimeValue; only the C return type was spelled `SplArray*`. See the POSIX
 * twin below. */
int64_t rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms) {
    return (int64_t)(uintptr_t)win_process_run_capture(cmd, cmd_len, args, timeout_ms, -1);
}

SplArray* rt_process_run_bounded(const char* cmd, uint64_t cmd_len, SplArray* args,
                                 int64_t timeout_ms, int64_t max_output_bytes) {
    return win_process_run_capture(cmd, cmd_len, args, timeout_ms, max_output_bytes);
}

struct WinPipedSlot {
    DWORD pid;
    HANDLE process;
    HANDLE job;
    HANDLE stdin_write;
    HANDLE stdin_event;
    OVERLAPPED stdin_overlapped;
    char stdin_pending_data[4096];
    DWORD stdin_pending_len;
    int64_t stdin_pending_data_len;
    int64_t stdin_pending_offset;
    HANDLE stdout_read;
};

#define WIN_PIPED_MAX 16
#define WIN_PIPED_READ_BUF 8192

static struct WinPipedSlot win_piped_slots[WIN_PIPED_MAX];
static char win_piped_read_buf[WIN_PIPED_READ_BUF];
static char win_browser_renderer_stdin_buf[WIN_PIPED_READ_BUF];

static bool win_random_pipe_name(char* name, size_t name_size) {
    typedef LONG (WINAPI *BCryptGenRandomFn)(
        void*, unsigned char*, unsigned long, unsigned long);
    unsigned char random[16];
    HMODULE bcrypt = LoadLibraryA("bcrypt.dll");
    if (!bcrypt) return false;
    BCryptGenRandomFn generate = (BCryptGenRandomFn)(
        void*)GetProcAddress(bcrypt, "BCryptGenRandom");
    LONG status = generate
        ? generate(NULL, random, sizeof(random), 0x00000002UL)
        : -1;
    FreeLibrary(bcrypt);
    if (status != 0) return false;
    int written = snprintf(
        name, name_size,
        "\\\\.\\pipe\\simple-piped-%02x%02x%02x%02x%02x%02x%02x%02x"
        "%02x%02x%02x%02x%02x%02x%02x%02x",
        random[0], random[1], random[2], random[3],
        random[4], random[5], random[6], random[7],
        random[8], random[9], random[10], random[11],
        random[12], random[13], random[14], random[15]);
    return written > 0 && (size_t)written < name_size;
}

static void win_piped_cancel_pending(struct WinPipedSlot* slot) {
    if (!slot || slot->stdin_pending_len == 0) return;
    (void)CancelIoEx(slot->stdin_write, &slot->stdin_overlapped);
    DWORD ignored = 0;
    (void)GetOverlappedResult(
        slot->stdin_write, &slot->stdin_overlapped, &ignored, TRUE);
    slot->stdin_pending_len = 0;
    slot->stdin_pending_data_len = 0;
    slot->stdin_pending_offset = 0;
    memset(&slot->stdin_overlapped, 0, sizeof(slot->stdin_overlapped));
    slot->stdin_overlapped.hEvent = slot->stdin_event;
}

static struct WinPipedSlot* win_piped_find(DWORD pid) {
    for (int i = 0; i < WIN_PIPED_MAX; i++) {
        if (win_piped_slots[i].pid == pid) return &win_piped_slots[i];
    }
    return NULL;
}

static struct WinPipedSlot* win_piped_alloc(void) {
    for (int i = 0; i < WIN_PIPED_MAX; i++) {
        if (win_piped_slots[i].pid == 0) return &win_piped_slots[i];
    }
    return NULL;
}

static void win_piped_free(struct WinPipedSlot* slot) {
    if (!slot) return;
    win_piped_cancel_pending(slot);
    win_close_handle(&slot->stdin_write);
    win_close_handle(&slot->stdin_event);
    win_close_handle(&slot->stdout_read);
    win_close_handle(&slot->process);
    win_close_handle(&slot->job);
    memset(slot, 0, sizeof(*slot));
}

int64_t rt_process_spawn_piped(const char* cmd, SplArray* args) {
    const char** child_args = NULL;
    char* cmdline = NULL;
    char* environment = NULL;
    HANDLE stdin_read = NULL;
    HANDLE stdin_write = NULL;
    HANDLE stdin_event = NULL;
    HANDLE stdout_read = NULL;
    HANDLE stdout_write = NULL;
    HANDLE job = NULL;
    LPPROC_THREAD_ATTRIBUTE_LIST attributes = NULL;
    int attributes_initialized = 0;
    int assigned_to_job = 0;
    PROCESS_INFORMATION process = {0};
    struct WinPipedSlot* slot = win_piped_alloc();
    if (!cmd || !*cmd || !slot) return -1;

    int64_t argc = args ? rt_array_len(args) : 0;
    if (argc < 0 || (uint64_t)argc > SIZE_MAX / sizeof(char*)) goto fail;
    if (argc > 0) {
        child_args = (const char**)malloc(sizeof(char*) * (size_t)argc);
        if (!child_args) goto fail;
        for (int64_t i = 0; i < argc; i++) {
            const uint8_t* data = rt_string_data(rt_array_get(args, i));
            child_args[i] = (const char*)(data ? data : (const uint8_t*)"");
        }
    }
    cmdline = win_cmd_build_line(cmd, child_args, argc);
    environment = win_filtered_environment();
    if (!cmdline || !environment) goto fail;

    SECURITY_ATTRIBUTES security = {sizeof(security), NULL, TRUE};
    char stdin_pipe_name[128];
    if (!win_random_pipe_name(stdin_pipe_name, sizeof(stdin_pipe_name))) {
        goto fail;
    }
#ifndef PIPE_REJECT_REMOTE_CLIENTS
#define PIPE_REJECT_REMOTE_CLIENTS 0x00000008
#endif
    stdin_read = CreateNamedPipeA(
        stdin_pipe_name,
        PIPE_ACCESS_INBOUND | FILE_FLAG_FIRST_PIPE_INSTANCE,
        PIPE_TYPE_BYTE | PIPE_READMODE_BYTE | PIPE_WAIT |
            PIPE_REJECT_REMOTE_CLIENTS,
        1, 65536, 65536, 0, &security);
    if (stdin_read == INVALID_HANDLE_VALUE) {
        stdin_read = NULL;
        goto fail;
    }
    stdin_write = CreateFileA(
        stdin_pipe_name, GENERIC_WRITE, 0, NULL, OPEN_EXISTING,
        FILE_ATTRIBUTE_NORMAL | FILE_FLAG_OVERLAPPED, NULL);
    if (stdin_write == INVALID_HANDLE_VALUE) {
        stdin_write = NULL;
        goto fail;
    }
    if ((!ConnectNamedPipe(stdin_read, NULL) &&
         GetLastError() != ERROR_PIPE_CONNECTED) ||
        !SetHandleInformation(stdin_write, HANDLE_FLAG_INHERIT, 0) ||
        !CreatePipe(&stdout_read, &stdout_write, &security, 0) ||
        !SetHandleInformation(stdout_read, HANDLE_FLAG_INHERIT, 0)) {
        goto fail;
    }
    stdin_event = CreateEventA(NULL, TRUE, FALSE, NULL);
    if (!stdin_event) goto fail;

    job = CreateJobObjectA(NULL, NULL);
    JOBOBJECT_EXTENDED_LIMIT_INFORMATION limits = {0};
    limits.BasicLimitInformation.LimitFlags = JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE;
    if (!job || !SetInformationJobObject(
            job, JobObjectExtendedLimitInformation, &limits, sizeof(limits))) {
        goto fail;
    }

    SIZE_T attributes_size = 0;
    (void)InitializeProcThreadAttributeList(NULL, 1, 0, &attributes_size);
    if (attributes_size == 0) goto fail;
    attributes = (LPPROC_THREAD_ATTRIBUTE_LIST)malloc(attributes_size);
    if (!attributes ||
        !InitializeProcThreadAttributeList(attributes, 1, 0, &attributes_size)) {
        goto fail;
    }
    attributes_initialized = 1;
    HANDLE inherited[] = {stdin_read, stdout_write};
    if (!UpdateProcThreadAttribute(
            attributes, 0, PROC_THREAD_ATTRIBUTE_HANDLE_LIST,
            inherited, sizeof(inherited), NULL, NULL)) {
        goto fail;
    }

    STARTUPINFOEXA startup = {0};
    startup.StartupInfo.cb = sizeof(startup);
    startup.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    startup.StartupInfo.hStdInput = stdin_read;
    startup.StartupInfo.hStdOutput = stdout_write;
    startup.StartupInfo.hStdError = stdout_write;
    DWORD creation_flags =
        CREATE_SUSPENDED | EXTENDED_STARTUPINFO_PRESENT | CREATE_NO_WINDOW;
    if (!CreateProcessA(
            NULL, cmdline, NULL, NULL, TRUE, creation_flags, environment, NULL,
            &startup.StartupInfo, &process)) {
        goto fail;
    }
    if (!AssignProcessToJobObject(job, process.hProcess)) goto fail;
    assigned_to_job = 1;
    if (ResumeThread(process.hThread) == (DWORD)-1) goto fail;

    DWORD pid = process.dwProcessId;
    win_close_handle(&process.hThread);
    win_close_handle(&stdin_read);
    win_close_handle(&stdout_write);
    if (attributes_initialized) DeleteProcThreadAttributeList(attributes);
    free(attributes);
    free(environment);
    free(cmdline);
    free(child_args);
    slot->pid = pid;
    slot->process = process.hProcess;
    slot->job = job;
    slot->stdin_write = stdin_write;
    slot->stdin_event = stdin_event;
    memset(&slot->stdin_overlapped, 0, sizeof(slot->stdin_overlapped));
    slot->stdin_overlapped.hEvent = stdin_event;
    slot->stdout_read = stdout_read;
    return (int64_t)pid;

fail:
    if (process.hProcess) {
        if (assigned_to_job) (void)TerminateJobObject(job, 1);
        else (void)TerminateProcess(process.hProcess, 1);
        (void)WaitForSingleObject(process.hProcess, 5000);
    }
    win_close_handle(&process.hThread);
    win_close_handle(&process.hProcess);
    win_close_handle(&stdin_read);
    win_close_handle(&stdin_write);
    win_close_handle(&stdin_event);
    win_close_handle(&stdout_read);
    win_close_handle(&stdout_write);
    win_close_handle(&job);
    if (attributes_initialized) DeleteProcThreadAttributeList(attributes);
    free(attributes);
    free(environment);
    free(cmdline);
    free(child_args);
    return -1;
}

bool rt_process_write_stdin(int64_t pid, const char* data) {
    if (pid <= 0 || pid > UINT32_MAX || !data) return false;
    size_t raw_length = strlen(data);
    if (raw_length > INT64_MAX) return false;
    int64_t length = (int64_t)raw_length;
    int64_t offset = 0;
    while (offset < length) {
        int64_t written = rt_process_write_stdin_some(
            pid, data, (int64_t)length, offset, 4096);
        if (written < 0) return false;
        if (written == 0) {
            Sleep(1);
            continue;
        }
        offset += written;
    }
    return true;
}

int64_t rt_process_write_stdin_some(
        int64_t pid, const char* data, int64_t data_len,
        int64_t offset, int64_t max_bytes) {
    if (pid <= 0 || pid > UINT32_MAX || !data || data_len < 0 ||
        offset < 0 || offset > data_len || max_bytes <= 0) {
        return -1;
    }
    if (offset == data_len) return 0;
    struct WinPipedSlot* slot = win_piped_find((DWORD)pid);
    if (!slot || !slot->stdin_write || !slot->stdin_event) return -1;
    if (slot->stdin_pending_len > 0) {
        if (slot->stdin_pending_data_len != data_len ||
            slot->stdin_pending_offset != offset ||
            memcmp(
                slot->stdin_pending_data, data + offset,
                slot->stdin_pending_len) != 0) {
            return -1;
        }
        DWORD completed = 0;
        if (!GetOverlappedResult(
                slot->stdin_write, &slot->stdin_overlapped,
                &completed, FALSE)) {
            if (GetLastError() == ERROR_IO_INCOMPLETE) return 0;
            win_piped_cancel_pending(slot);
            return -1;
        }
        slot->stdin_pending_len = 0;
        slot->stdin_pending_data_len = 0;
        slot->stdin_pending_offset = 0;
        ResetEvent(slot->stdin_event);
        memset(&slot->stdin_overlapped, 0, sizeof(slot->stdin_overlapped));
        slot->stdin_overlapped.hEvent = slot->stdin_event;
        return completed > 0 ? (int64_t)completed : -1;
    }
    uint64_t remaining = (uint64_t)(data_len - offset);
    uint64_t request = remaining;
    if (request > (uint64_t)max_bytes) request = (uint64_t)max_bytes;
    if (request > 4096U) request = 4096U;
    if (request == 0) return 0;
    memcpy(slot->stdin_pending_data, data + offset, (size_t)request);
    ResetEvent(slot->stdin_event);
    memset(&slot->stdin_overlapped, 0, sizeof(slot->stdin_overlapped));
    slot->stdin_overlapped.hEvent = slot->stdin_event;
    if (WriteFile(
            slot->stdin_write, slot->stdin_pending_data, (DWORD)request,
            NULL, &slot->stdin_overlapped)) {
        DWORD completed = 0;
        if (!GetOverlappedResult(
                slot->stdin_write, &slot->stdin_overlapped,
                &completed, FALSE)) {
            return -1;
        }
        return completed > 0 ? (int64_t)completed : -1;
    }
    if (GetLastError() != ERROR_IO_PENDING) {
        return -1;
    }
    slot->stdin_pending_len = (DWORD)request;
    slot->stdin_pending_data_len = data_len;
    slot->stdin_pending_offset = offset;
    return 0;
}

const char* rt_process_read_stdout(int64_t pid) {
    win_piped_read_buf[0] = '\0';
    if (pid <= 0 || pid > UINT32_MAX) return win_piped_read_buf;
    struct WinPipedSlot* slot = win_piped_find((DWORD)pid);
    if (!slot || !slot->stdout_read) return win_piped_read_buf;
    DWORD available = 0;
    if (!PeekNamedPipe(
            slot->stdout_read, NULL, 0, NULL, &available, NULL) ||
        available == 0) {
        return win_piped_read_buf;
    }
    DWORD request = available < WIN_PIPED_READ_BUF - 1
        ? available : WIN_PIPED_READ_BUF - 1;
    DWORD read_count = 0;
    if (!ReadFile(
            slot->stdout_read, win_piped_read_buf, request,
            &read_count, NULL)) {
        return win_piped_read_buf;
    }
    win_piped_read_buf[read_count] = '\0';
    return win_piped_read_buf;
}

bool rt_process_is_alive(int64_t pid) {
    if (pid <= 0 || pid > UINT32_MAX) return false;
    struct WinPipedSlot* slot = win_piped_find((DWORD)pid);
    if (!slot || !slot->process) return false;
    DWORD wait_result = WaitForSingleObject(slot->process, 0);
    if (wait_result == WAIT_TIMEOUT) return true;
    if (wait_result == WAIT_FAILED) return false;
    win_piped_free(slot);
    return false;
}

bool rt_process_close_piped(int64_t pid) {
    if (pid <= 0 || pid > UINT32_MAX) return false;
    struct WinPipedSlot* slot = win_piped_find((DWORD)pid);
    if (!slot) return false;
    win_piped_cancel_pending(slot);
    win_close_handle(&slot->stdin_write);
    DWORD wait_result = WaitForSingleObject(slot->process, 100);
    if (wait_result == WAIT_TIMEOUT) {
        if (!TerminateJobObject(slot->job, 1) &&
            !TerminateProcess(slot->process, 1)) {
            return false;
        }
        wait_result = WaitForSingleObject(slot->process, 5000);
    }
    if (wait_result != WAIT_OBJECT_0) return false;
    bool stopped = wait_result == WAIT_OBJECT_0;
    win_piped_free(slot);
    return stopped;
}

int64_t rt_browser_renderer_spawn_sandboxed(
        const char* cmd, SplArray* args) {
    (void)cmd;
    (void)args;
    return -1;
}

bool rt_browser_renderer_sandbox_enter(void) {
    return false;
}

const char* rt_browser_renderer_read_stdin_some(int64_t max_bytes) {
    win_browser_renderer_stdin_buf[0] = '\0';
    if (max_bytes <= 0) return win_browser_renderer_stdin_buf;
    DWORD request = max_bytes < WIN_PIPED_READ_BUF
        ? (DWORD)max_bytes : WIN_PIPED_READ_BUF - 1;
    DWORD read_count = 0;
    HANDLE input = GetStdHandle(STD_INPUT_HANDLE);
    if (!input || input == INVALID_HANDLE_VALUE ||
        !ReadFile(
            input, win_browser_renderer_stdin_buf, request,
            &read_count, NULL)) {
        return win_browser_renderer_stdin_buf;
    }
    win_browser_renderer_stdin_buf[read_count] = '\0';
    return win_browser_renderer_stdin_buf;
}

int64_t rt_browser_renderer_write_stdout_some(
        const char* data, int64_t data_len, int64_t offset,
        int64_t max_bytes) {
    if (!data || data_len < 0 || offset < 0 || offset > data_len ||
        max_bytes <= 0) return -1;
    if (offset == data_len) return 0;
    int64_t remaining = data_len - offset;
    if (max_bytes > 1048576) max_bytes = 1048576;
    DWORD request = (DWORD)(
        remaining < max_bytes ? remaining : max_bytes);
    DWORD written = 0;
    HANDLE output = GetStdHandle(STD_OUTPUT_HANDLE);
    if (!output || output == INVALID_HANDLE_VALUE ||
        !WriteFile(output, data + offset, request, &written, NULL)) {
        return -1;
    }
    return (int64_t)written;
}

int64_t rt_browser_renderer_write_protocol_some(
        const char* data, int64_t data_len, int64_t offset,
        int64_t max_bytes) {
    (void)data;
    (void)data_len;
    (void)offset;
    (void)max_bytes;
    return -1;
}

#else /* POSIX */

#include "runtime_fork.h"

#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <errno.h>
#include <pthread.h>
#include <poll.h>
#ifdef __APPLE__
#include <crt_externs.h>
#include <spawn.h>
#endif
#ifdef __linux__
#include <stddef.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/landlock.h>
#include <linux/seccomp.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#endif

/* ===== Process table ===== */

#define RT_PROC_MAX 16
#define RT_RENDERER_PROC_MAX 4
#define RT_PROC_READ_BUF 8192

struct RtProcSlot {
    pid_t pid;       /* 0 = empty, -1 = reserved during spawn */
    int   stdin_fd;  /* parent writes here  → child's stdin */
    int   stdout_fd; /* parent reads here   ← child's stdout */
    bool  sandboxed_renderer;
};

static struct RtProcSlot s_procs[RT_PROC_MAX];
static pthread_mutex_t s_proc_lock = PTHREAD_MUTEX_INITIALIZER;
static unsigned int s_renderer_slots_active;

/* Static read buffer — returned pointer is valid until the next call */
static char s_read_buf[RT_PROC_READ_BUF];
static char s_browser_renderer_stdin_buf[RT_PROC_READ_BUF];

/* ===== Internal helpers ===== */

static struct RtProcSlot* proc_find(pid_t pid) {
    for (int i = 0; i < RT_PROC_MAX; i++) {
        if (s_procs[i].pid == pid) return &s_procs[i];
    }
    return NULL;
}

static struct RtProcSlot* proc_alloc(bool sandboxed_renderer) {
    if (pthread_mutex_lock(&s_proc_lock) != 0) return NULL;
    if (sandboxed_renderer &&
        s_renderer_slots_active >= RT_RENDERER_PROC_MAX) {
        (void)pthread_mutex_unlock(&s_proc_lock);
        return NULL;
    }
    for (int i = 0; i < RT_PROC_MAX; i++) {
        if (s_procs[i].pid == 0) {
            s_procs[i].pid = -1;
            s_procs[i].stdin_fd = -1;
            s_procs[i].stdout_fd = -1;
            s_procs[i].sandboxed_renderer = sandboxed_renderer;
            if (sandboxed_renderer) s_renderer_slots_active++;
            (void)pthread_mutex_unlock(&s_proc_lock);
            return &s_procs[i];
        }
    }
    (void)pthread_mutex_unlock(&s_proc_lock);
    return NULL;
}

static void proc_free(struct RtProcSlot* slot) {
    if (!slot) return;
    if (pthread_mutex_lock(&s_proc_lock) != 0) return;
    if (slot->pid == 0) {
        (void)pthread_mutex_unlock(&s_proc_lock);
        return;
    }
    int stdin_fd = slot->stdin_fd;
    int stdout_fd = slot->stdout_fd;
    if (slot->sandboxed_renderer && s_renderer_slots_active > 0) {
        s_renderer_slots_active--;
    }
    slot->stdin_fd = -1;
    slot->stdout_fd = -1;
    slot->sandboxed_renderer = false;
    slot->pid = 0;
    (void)pthread_mutex_unlock(&s_proc_lock);
    if (stdin_fd >= 0) close(stdin_fd);
    if (stdout_fd >= 0) close(stdout_fd);
}

static bool proc_signal_tree(pid_t pid, int signal_number, bool leader_reaped) {
    if (kill(-pid, signal_number) == 0) return true;
    if (errno != ESRCH) return false;
    if (leader_reaped) return true;
    return kill(pid, signal_number) == 0 || errno == ESRCH;
}

static ssize_t proc_write_some_no_sigpipe(int fd, const char* data, size_t len) {
    sigset_t blocked;
    sigset_t old_mask;
    sigset_t pending;
    struct sigaction action;
    bool sigpipe_was_pending = false;
    bool sigpipe_is_ignored = false;
    bool broken_pipe = false;
    ssize_t written = -1;

    sigemptyset(&blocked);
    sigaddset(&blocked, SIGPIPE);
    if (pthread_sigmask(SIG_BLOCK, &blocked, &old_mask) != 0) return -1;
    if (sigpending(&pending) == 0) {
        sigpipe_was_pending = sigismember(&pending, SIGPIPE) == 1;
    }
    if (sigaction(SIGPIPE, NULL, &action) == 0) {
        sigpipe_is_ignored = action.sa_handler == SIG_IGN;
    }

    do {
        written = write(fd, data, len);
    } while (written < 0 && errno == EINTR);
    int write_error = written < 0 ? errno : 0;
    broken_pipe = written < 0 && write_error == EPIPE;

    if (broken_pipe && !sigpipe_was_pending && !sigpipe_is_ignored) {
        int signal_number = 0;
        (void)sigwait(&blocked, &signal_number);
    }
    (void)pthread_sigmask(SIG_SETMASK, &old_mask, NULL);
    if (written < 0 &&
        (write_error == EAGAIN || write_error == EWOULDBLOCK)) {
        return 0;
    }
    if (written < 0) errno = write_error;
    return written;
}

static bool proc_write_all_no_sigpipe(int fd, const char* data, size_t len) {
    size_t offset = 0;
    while (offset < len) {
        ssize_t written = proc_write_some_no_sigpipe(
            fd, data + offset, len - offset);
        if (written > 0) {
            offset += (size_t)written;
            continue;
        }
        if (written < 0) return false;
        struct pollfd writable = {fd, POLLOUT, 0};
        int ready;
        do {
            ready = poll(&writable, 1, -1);
        } while (ready < 0 && errno == EINTR);
        if (ready <= 0) return false;
    }
    return true;
}

static bool proc_pipe_cloexec(int fds[2]) {
    if (pipe(fds) != 0) return false;
    int first_flags = fcntl(fds[0], F_GETFD);
    int second_flags = fcntl(fds[1], F_GETFD);
    if (first_flags < 0 || second_flags < 0 ||
        fcntl(fds[0], F_SETFD, first_flags | FD_CLOEXEC) != 0 ||
        fcntl(fds[1], F_SETFD, second_flags | FD_CLOEXEC) != 0) {
        close(fds[0]);
        close(fds[1]);
        return false;
    }
    return true;
}

#ifdef __linux__
static bool proc_renderer_socketpair(int stdin_pipe[2], int stdout_pipe[2]) {
    int sockets[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, sockets) != 0) {
        return false;
    }
    int parent_read = fcntl(
        sockets[0], F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    int child_write = fcntl(
        sockets[1], F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    if (parent_read < 0 || child_write < 0) {
        if (parent_read >= 0) close(parent_read);
        if (child_write >= 0) close(child_write);
        close(sockets[0]);
        close(sockets[1]);
        return false;
    }
    stdin_pipe[0] = sockets[1];
    stdin_pipe[1] = sockets[0];
    stdout_pipe[0] = parent_read;
    stdout_pipe[1] = child_write;
    return true;
}
#endif

#ifdef __APPLE__
static bool proc_move_pipe_fds_above_stdio(int fds[2]) {
    for (int i = 0; i < 2; i++) {
        if (fds[i] > STDERR_FILENO) continue;
        int moved = fcntl(fds[i], F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
        if (moved < 0) return false;
        close(fds[i]);
        fds[i] = moved;
    }
    return true;
}

static pid_t proc_spawn_piped_apple(
        const char* cmd, char** argv,
        const int stdin_pipe[2], const int stdout_pipe[2]) {
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attributes;
    bool actions_initialized = false;
    bool attributes_initialized = false;
    pid_t pid = -1;
    sigset_t defaults;

    if (posix_spawn_file_actions_init(&actions) != 0) goto done;
    actions_initialized = true;
    if (posix_spawnattr_init(&attributes) != 0) goto done;
    attributes_initialized = true;

    if (posix_spawn_file_actions_adddup2(
            &actions, stdin_pipe[0], STDIN_FILENO) != 0 ||
        posix_spawn_file_actions_adddup2(
            &actions, stdout_pipe[1], STDOUT_FILENO) != 0) {
        goto done;
    }
    int stderr_flags = fcntl(STDERR_FILENO, F_GETFD);
    if (stderr_flags >= 0 && (stderr_flags & FD_CLOEXEC) == 0 &&
        posix_spawn_file_actions_addinherit_np(
            &actions, STDERR_FILENO) != 0) {
        goto done;
    }
    if (posix_spawn_file_actions_addclose(&actions, stdin_pipe[0]) != 0 ||
        posix_spawn_file_actions_addclose(&actions, stdin_pipe[1]) != 0 ||
        posix_spawn_file_actions_addclose(&actions, stdout_pipe[0]) != 0 ||
        posix_spawn_file_actions_addclose(&actions, stdout_pipe[1]) != 0) {
        goto done;
    }

    sigemptyset(&defaults);
    sigaddset(&defaults, SIGINT);
    sigaddset(&defaults, SIGTERM);
    sigaddset(&defaults, SIGPIPE);
    if (posix_spawnattr_setpgroup(&attributes, 0) != 0 ||
        posix_spawnattr_setsigdefault(&attributes, &defaults) != 0 ||
        posix_spawnattr_setflags(
            &attributes,
            (short)(POSIX_SPAWN_CLOEXEC_DEFAULT |
                    POSIX_SPAWN_SETPGROUP |
                    POSIX_SPAWN_SETSIGDEF)) != 0) {
        goto done;
    }

    if (posix_spawnp(
            &pid, cmd, &actions, &attributes, argv,
            *_NSGetEnviron()) != 0) {
        pid = -1;
    }

done:
    if (attributes_initialized) (void)posix_spawnattr_destroy(&attributes);
    if (actions_initialized) (void)posix_spawn_file_actions_destroy(&actions);
    return pid;
}
#else
static void proc_close_inherited_fds(void) {
#if defined(__linux__) && defined(SYS_close_range)
    if (syscall(SYS_close_range, 3U, ~0U, 0U) == 0) return;
#elif defined(__FreeBSD__)
    closefrom(3);
    return;
#endif
    long max_fd = sysconf(_SC_OPEN_MAX);
    if (max_fd < 0 || max_fd > 1048576) max_fd = 1048576;
    for (int fd = 3; fd < max_fd; fd++) close(fd);
}
#endif

/* ===== Public API ===== */

static int64_t rt_process_spawn_piped_argv(
        const char* cmd, char** argv, bool sandboxed_renderer) {
    if (!cmd || !*cmd) return -1;
#ifndef __linux__
    if (sandboxed_renderer) return -1;
#else
    if (sandboxed_renderer && cmd[0] != '/') return -1;
#endif

    struct RtProcSlot* slot = proc_alloc(sandboxed_renderer);
    if (!slot) return -1;

    /* stdin_pipe[0] = child reads, stdin_pipe[1] = parent writes */
    int stdin_pipe[2];
    /* stdout_pipe[0] = parent reads, stdout_pipe[1] = child writes */
    int stdout_pipe[2];

#ifdef __linux__
    if (sandboxed_renderer) {
        if (!proc_renderer_socketpair(stdin_pipe, stdout_pipe)) {
            proc_free(slot);
            return -1;
        }
    } else
#endif
    {
        if (!proc_pipe_cloexec(stdin_pipe)) {
            proc_free(slot);
            return -1;
        }
        if (!proc_pipe_cloexec(stdout_pipe)) {
            close(stdin_pipe[0]); close(stdin_pipe[1]);
            proc_free(slot);
            return -1;
        }
    }
#ifdef __APPLE__
    if (!proc_move_pipe_fds_above_stdio(stdin_pipe) ||
        !proc_move_pipe_fds_above_stdio(stdout_pipe)) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        proc_free(slot);
        return -1;
    }
#endif
    int stdin_flags = fcntl(stdin_pipe[1], F_GETFL, 0);
    if (stdin_flags < 0 ||
        fcntl(stdin_pipe[1], F_SETFL, stdin_flags | O_NONBLOCK) != 0) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        proc_free(slot);
        return -1;
    }

    fflush(stdout);
    fflush(stderr);

#ifdef __APPLE__
    pid_t pid = proc_spawn_piped_apple(
        cmd, argv, stdin_pipe, stdout_pipe);
#else
#ifdef __linux__
    pid_t expected_parent = getpid();
#endif
    pid_t pid = fork();
    if (pid < 0) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        proc_free(slot);
        return -1;
    }

    if (pid == 0) {
        /* === CHILD === */
        if (setpgid(0, 0) != 0) _exit(127);
#ifdef __linux__
        if (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 ||
            getppid() != expected_parent) {
            _exit(127);
        }
#endif
        int null_fd = -1;
        if (sandboxed_renderer) {
            null_fd = open("/dev/null", O_WRONLY);
            if (null_fd < 0) _exit(127);
        }

        /* Wire pipes to stdio */
        if (dup2(stdin_pipe[0], STDIN_FILENO) < 0 ||
            dup2(
                sandboxed_renderer ? null_fd : stdout_pipe[1],
                STDOUT_FILENO) < 0 ||
            (sandboxed_renderer && dup2(null_fd, STDERR_FILENO) < 0)) {
            _exit(127);
        }

        /* Close all parent-side fds */
        proc_close_inherited_fds();

        /* Reset signal handlers */
        signal(SIGINT,  SIG_DFL);
        signal(SIGTERM, SIG_DFL);
        signal(SIGPIPE, SIG_DFL);

        if (sandboxed_renderer) {
#ifdef __linux__
            char* empty_environment[] = {NULL};
            argv[0] = (char*)"simple-browser-renderer";
            if (chdir("/") != 0) _exit(127);
            execve(cmd, argv, empty_environment);
#endif
        } else {
            execvp(cmd, argv);
        }
        _exit(127); /* exec failed */
    }
#endif

    /* === PARENT === */
#ifndef __APPLE__
    if (setpgid(pid, pid) != 0 && errno != EACCES && errno != ESRCH) {
        kill(pid, SIGKILL);
        while (waitpid(pid, NULL, 0) < 0 && errno == EINTR) {}
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        proc_free(slot);
        return -1;
    }
#else
    if (pid < 0) {
        close(stdin_pipe[0]); close(stdin_pipe[1]);
        close(stdout_pipe[0]); close(stdout_pipe[1]);
        proc_free(slot);
        return -1;
    }
#endif
    /* Close child-side ends */
    close(stdin_pipe[0]);
    close(stdout_pipe[1]);

    /* Set stdout_fd non-blocking so reads don't hang */
    int flags = fcntl(stdout_pipe[0], F_GETFL, 0);
    if (flags >= 0) fcntl(stdout_pipe[0], F_SETFL, flags | O_NONBLOCK);

    slot->stdin_fd = stdin_pipe[1];
    slot->stdout_fd = stdout_pipe[0];
    slot->pid = pid;

    return (int64_t)pid;
}

/*
 * Fork + exec `cmd` with `args`, wiring up stdin/stdout pipes.
 * Returns the child PID on success, -1 on error.
 */
int64_t rt_process_spawn_piped(const char* cmd, SplArray* args) {
    int64_t argc = args ? rt_array_len(args) : 0;
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) return -1;
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < argc; i++) {
        const uint8_t* data = rt_string_data(rt_array_get(args, i));
        argv[i + 1] = (char*)(data ? data : (const uint8_t*)"");
    }
    argv[argc + 1] = NULL;
    int64_t pid = rt_process_spawn_piped_argv(cmd, argv, false);
    free(argv);
    return pid;
}

int64_t rt_browser_renderer_spawn_sandboxed(
        const char* cmd, SplArray* args) {
#ifndef __linux__
    (void)cmd;
    (void)args;
    return -1;
#else
    int64_t argc = args ? rt_array_len(args) : 0;
    if (argc < 0 || (uint64_t)argc > SIZE_MAX / sizeof(char*) - 2) return -1;
    char** argv = (char**)malloc(sizeof(char*) * (size_t)(argc + 2));
    if (!argv) return -1;
    argv[0] = (char*)"simple-browser-renderer";
    for (int64_t i = 0; i < argc; i++) {
        const uint8_t* data = rt_string_data(rt_array_get(args, i));
        argv[i + 1] = (char*)(data ? data : (const uint8_t*)"");
    }
    argv[argc + 1] = NULL;
    int64_t pid = rt_process_spawn_piped_argv(cmd, argv, true);
    free(argv);
    return pid;
#endif
}

static SplArray* posix_process_run_capture(const char* cmd, uint64_t cmd_len, SplArray* args,
                                           int64_t timeout_ms, int64_t max_output_bytes) {
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

    int64_t code = max_output_bytes < 0
        ? rt_fork_parent_wait(child_pid, timeout_ms > 0 ? timeout_ms : 0)
        : rt_fork_parent_wait_bounded(child_pid, timeout_ms > 0 ? timeout_ms : 0,
                                      (uint64_t)max_output_bytes);
    int timed_out = rt_fork_parent_timed_out() ? 1 : 0;
    if (rt_fork_parent_signaled()) code = -1;
    const char* out = rt_fork_parent_stdout();
    const char* err = rt_fork_parent_stderr();
    if (code == 127 && err && strstr(err, "rt_process_run_timeout execvp") != NULL) code = -1;
    return process_timeout_result(out, err, code, timed_out, timeout_ms);
}

/* (cmd_ptr, cmd_len, args, timeout_ms) -> RuntimeValue (array), per
 * runtime_sffi.rs:1423, matching the canonical Rust definition
 * (sffi/env_process.rs:1094 -> RuntimeValue).
 *
 * The BODY was already correct -- posix_process_run_capture builds the result
 * with rt_array_new / rt_array_push / rt_string_new, so it carries
 * RT_VALUE_TAG_HEAP and the rt_core registry owns it. Measured through the ABI
 * the compiler emits, in all three C link orders: raw=0x...2e1, tag=1,
 * array_len=3. cmd_len is honoured and forwarded. Only the C RETURN TYPE was
 * spelled `SplArray*` where the compiler says I64, which is what the extern ABI
 * gate flagged; this is a signature correction, not a behaviour change. */
int64_t rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms) {
    return (int64_t)(uintptr_t)posix_process_run_capture(cmd, cmd_len, args, timeout_ms, -1);
}

SplArray* rt_process_run_bounded(const char* cmd, uint64_t cmd_len, SplArray* args,
                                 int64_t timeout_ms, int64_t max_output_bytes) {
    if (max_output_bytes < 0 || (uint64_t)max_output_bytes > SIZE_MAX - 97U) {
        return process_timeout_result("", "", -1, 0, timeout_ms);
    }
    return posix_process_run_capture(cmd, cmd_len, args, timeout_ms, max_output_bytes);
}

int64_t rt_editor_spawn_simple_dap(void) {
    char* argv[] = {
        "src/compiler_rust/target/debug/simple",
        "run",
        "src/app/dap/simple_dap_main.spl",
        NULL
    };
    return rt_process_spawn_piped_argv(argv[0], argv, false);
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

    return proc_write_all_no_sigpipe(slot->stdin_fd, data, len);
}

int64_t rt_process_write_stdin_some(
        int64_t pid, const char* data, int64_t data_len,
        int64_t offset, int64_t max_bytes) {
    if (pid <= 0 || !data || data_len < 0 || offset < 0 ||
        offset > data_len || max_bytes <= 0) {
        return -1;
    }
    if (offset == data_len) return 0;
    struct RtProcSlot* slot = proc_find((pid_t)pid);
    if (!slot || slot->stdin_fd < 0) return -1;
    int64_t remaining = data_len - offset;
    uint64_t request64 = (uint64_t)(
        remaining < max_bytes ? remaining : max_bytes);
    if (request64 > SIZE_MAX) request64 = SIZE_MAX;
    size_t request = (size_t)request64;
    return (int64_t)proc_write_some_no_sigpipe(
        slot->stdin_fd, data + offset, request);
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
    pid_t result;
    do {
        result = waitpid(slot->pid, &status, WNOHANG);
    } while (result < 0 && errno == EINTR);
    if (result == 0) return true;   /* still running */
    if (result == slot->pid || (result < 0 && errno == ECHILD)) {
        if (!proc_signal_tree(slot->pid, SIGKILL, true)) return false;
        proc_free(slot);
        return false;
    }
    return false;
}

bool rt_process_close_piped(int64_t pid) {
    if (pid <= 0) return false;
    struct RtProcSlot* slot = proc_find((pid_t)pid);
    if (!slot) return false;

    if (slot->stdin_fd >= 0) {
        close(slot->stdin_fd);
        slot->stdin_fd = -1;
    }
    if (!proc_signal_tree(slot->pid, SIGTERM, false)) return false;

    int status = 0;
    bool leader_reaped = false;
    for (int waited_ms = 0; waited_ms < 100; waited_ms++) {
        pid_t result = waitpid(slot->pid, &status, WNOHANG);
        if (result == slot->pid || (result < 0 && errno == ECHILD)) {
            leader_reaped = true;
            break;
        }
        if (result < 0 && errno != EINTR) return false;
        usleep(1000);
    }

    if (!proc_signal_tree(slot->pid, SIGKILL, leader_reaped)) return false;
    if (!leader_reaped) {
        for (int waited_ms = 0; waited_ms < 5000; waited_ms++) {
            pid_t result = waitpid(slot->pid, &status, WNOHANG);
            if (result == slot->pid || (result < 0 && errno == ECHILD)) {
                leader_reaped = true;
                break;
            }
            if (result < 0 && errno != EINTR) return false;
            usleep(1000);
        }
    }
    if (!leader_reaped) return false;
    proc_free(slot);
    return true;
}

const char* rt_browser_renderer_read_stdin_some(int64_t max_bytes) {
    s_browser_renderer_stdin_buf[0] = '\0';
    if (max_bytes <= 0) return s_browser_renderer_stdin_buf;
    size_t request = max_bytes < RT_PROC_READ_BUF
        ? (size_t)max_bytes : RT_PROC_READ_BUF - 1;
    ssize_t read_count;
    do {
        read_count = read(
            STDIN_FILENO, s_browser_renderer_stdin_buf, request);
    } while (read_count < 0 && errno == EINTR);
    if (read_count <= 0) return s_browser_renderer_stdin_buf;
    s_browser_renderer_stdin_buf[read_count] = '\0';
    return s_browser_renderer_stdin_buf;
}

int64_t rt_browser_renderer_write_stdout_some(
        const char* data, int64_t data_len, int64_t offset,
        int64_t max_bytes) {
    if (!data || data_len < 0 || offset < 0 || offset > data_len ||
        max_bytes <= 0) return -1;
    if (offset == data_len) return 0;
    int64_t remaining = data_len - offset;
    if (max_bytes > 1048576) max_bytes = 1048576;
    size_t request = (size_t)(
        remaining < max_bytes ? remaining : max_bytes);
    ssize_t written;
    do {
        written = write(STDOUT_FILENO, data + offset, request);
    } while (written < 0 && errno == EINTR);
    return written < 0 ? -1 : (int64_t)written;
}

int64_t rt_browser_renderer_write_protocol_some(
        const char* data, int64_t data_len, int64_t offset,
        int64_t max_bytes) {
#ifndef __linux__
    (void)data;
    (void)data_len;
    (void)offset;
    (void)max_bytes;
    return -1;
#else
    if (!data || data_len < 0 || offset < 0 || offset > data_len ||
        max_bytes <= 0) return -1;
    if (offset == data_len) return 0;
    int64_t remaining = data_len - offset;
    if (max_bytes > 1048576) max_bytes = 1048576;
    size_t request = (size_t)(
        remaining < max_bytes ? remaining : max_bytes);
    ssize_t written;
    do {
        written = write(STDIN_FILENO, data + offset, request);
    } while (written < 0 && errno == EINTR);
    return written < 0 ? -1 : (int64_t)written;
#endif
}

#ifdef __linux__

#if defined(__x86_64__)
#define BROWSER_RENDERER_AUDIT_ARCH AUDIT_ARCH_X86_64
#elif defined(__aarch64__)
#define BROWSER_RENDERER_AUDIT_ARCH AUDIT_ARCH_AARCH64
#elif defined(__riscv) && __riscv_xlen == 64
#define BROWSER_RENDERER_AUDIT_ARCH AUDIT_ARCH_RISCV64
#elif defined(__i386__)
#define BROWSER_RENDERER_AUDIT_ARCH AUDIT_ARCH_I386
#elif defined(__arm__)
#define BROWSER_RENDERER_AUDIT_ARCH AUDIT_ARCH_ARM
#endif

#define BROWSER_RENDERER_DENY_SYSCALL(number) \
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (number), 0, 1), \
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ERRNO | (EPERM & SECCOMP_RET_DATA))

/* Allow-list entry: fall through to the next check unless the syscall
   number matches, in which case allow it. Anything that matches no entry
   reaches the filter's final default, SECCOMP_RET_KILL_PROCESS. */
#define BROWSER_RENDERER_ALLOW_SYSCALL(number) \
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, (number), 0, 1), \
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)

static bool browser_renderer_set_limit(
        int resource, rlim_t current, rlim_t maximum) {
    struct rlimit limit = {current, maximum};
    return setrlimit(resource, &limit) == 0;
}

static bool browser_renderer_apply_landlock(void) {
#if !defined(SYS_landlock_create_ruleset) || \
    !defined(SYS_landlock_restrict_self)
    return false;
#else
    int abi = (int)syscall(
        SYS_landlock_create_ruleset, NULL, 0,
        LANDLOCK_CREATE_RULESET_VERSION);
    if (abi < 1) return false;
    __u64 access =
        LANDLOCK_ACCESS_FS_EXECUTE |
        LANDLOCK_ACCESS_FS_WRITE_FILE |
        LANDLOCK_ACCESS_FS_READ_FILE |
        LANDLOCK_ACCESS_FS_READ_DIR |
        LANDLOCK_ACCESS_FS_REMOVE_DIR |
        LANDLOCK_ACCESS_FS_REMOVE_FILE |
        LANDLOCK_ACCESS_FS_MAKE_CHAR |
        LANDLOCK_ACCESS_FS_MAKE_DIR |
        LANDLOCK_ACCESS_FS_MAKE_REG |
        LANDLOCK_ACCESS_FS_MAKE_SOCK |
        LANDLOCK_ACCESS_FS_MAKE_FIFO |
        LANDLOCK_ACCESS_FS_MAKE_BLOCK |
        LANDLOCK_ACCESS_FS_MAKE_SYM;
#ifdef LANDLOCK_ACCESS_FS_REFER
    if (abi >= 2) access |= LANDLOCK_ACCESS_FS_REFER;
#endif
#ifdef LANDLOCK_ACCESS_FS_TRUNCATE
    if (abi >= 3) access |= LANDLOCK_ACCESS_FS_TRUNCATE;
#endif
#ifdef LANDLOCK_ACCESS_FS_IOCTL_DEV
    if (abi >= 5) access |= LANDLOCK_ACCESS_FS_IOCTL_DEV;
#endif
    struct landlock_ruleset_attr ruleset = {
        .handled_access_fs = access
    };
    int ruleset_fd = (int)syscall(
        SYS_landlock_create_ruleset, &ruleset, sizeof(ruleset), 0);
    if (ruleset_fd < 0) return false;
    bool restricted =
        syscall(SYS_landlock_restrict_self, ruleset_fd, 0) == 0;
    close(ruleset_fd);
    return restricted;
#endif
}

static bool s_browser_renderer_preinit_active;

static bool browser_renderer_apply_startup_seccomp(void) {
#if !defined(BROWSER_RENDERER_AUDIT_ARCH) || !defined(SYS_seccomp)
    return false;
#else
    struct sock_filter filter[] = {
        BPF_STMT(
            BPF_LD | BPF_W | BPF_ABS,
            (uint32_t)offsetof(struct seccomp_data, arch)),
        BPF_JUMP(
            BPF_JMP | BPF_JEQ | BPF_K,
            BROWSER_RENDERER_AUDIT_ARCH, 1, 0),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
        BPF_STMT(
            BPF_LD | BPF_W | BPF_ABS,
            (uint32_t)offsetof(struct seccomp_data, nr)),
#if defined(__x86_64__)
        BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x40000000U, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
#endif
#ifdef __NR_socket
        BROWSER_RENDERER_DENY_SYSCALL(__NR_socket),
#endif
#ifdef __NR_socketpair
        BROWSER_RENDERER_DENY_SYSCALL(__NR_socketpair),
#endif
#ifdef __NR_socketcall
        BROWSER_RENDERER_DENY_SYSCALL(__NR_socketcall),
#endif
#ifdef __NR_fork
        BROWSER_RENDERER_DENY_SYSCALL(__NR_fork),
#endif
#ifdef __NR_vfork
        BROWSER_RENDERER_DENY_SYSCALL(__NR_vfork),
#endif
#ifdef __NR_clone
        BROWSER_RENDERER_DENY_SYSCALL(__NR_clone),
#endif
#ifdef __NR_clone3
        BROWSER_RENDERER_DENY_SYSCALL(__NR_clone3),
#endif
#ifdef __NR_execve
        BROWSER_RENDERER_DENY_SYSCALL(__NR_execve),
#endif
#ifdef __NR_execveat
        BROWSER_RENDERER_DENY_SYSCALL(__NR_execveat),
#endif
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)
    };
    struct sock_fprog program = {
        .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
        .filter = filter
    };
    return syscall(
        SYS_seccomp, SECCOMP_SET_MODE_FILTER,
        SECCOMP_FILTER_FLAG_TSYNC, &program) == 0;
#endif
}

/* Namespace flags are spelled out rather than pulled from <sched.h>, which
   would need _GNU_SOURCE for unshare(); the syscall is issued through
   syscall(SYS_unshare, ...) exactly like the landlock/seccomp calls above. */
#ifndef CLONE_NEWIPC
#define CLONE_NEWIPC 0x08000000
#endif
#ifndef CLONE_NEWUSER
#define CLONE_NEWUSER 0x10000000
#endif
#ifndef CLONE_NEWNET
#define CLONE_NEWNET 0x40000000
#endif

static bool browser_renderer_write_proc(const char* path, const char* data) {
    int fd = open(path, O_WRONLY | O_CLOEXEC);
    if (fd < 0) return false;
    size_t len = strlen(data);
    ssize_t written = write(fd, data, len);
    int saved = errno;
    close(fd);
    errno = saved;
    return written == (ssize_t)len;
}

/* Unshare the user, network and IPC namespaces and drop to an unprivileged
   identity inside the new user namespace.

   This MUST run before browser_renderer_apply_landlock(). The landlock ruleset
   below declares handled_access_fs with NO allow rules, which denies
   LANDLOCK_ACCESS_FS_WRITE_FILE process-wide — so /proc/self/uid_map becomes
   unwritable the moment landlock is applied, and the uid/gid drop would be
   impossible afterwards. It must equally run before the seccomp filters, whose
   allow-list contains neither unshare nor openat.

   The network namespace is the load-bearing part: it removes the renderer's
   route to the network outright, instead of relying on every socket-creating
   syscall staying denied. seccomp already kills socket(), so the two are
   defence in depth, not duplicates — a future kernel syscall that reaches the
   network would defeat the filter but not an empty netns.

   PID namespace is deliberately NOT unshared: CLONE_NEWPID only takes effect
   for children created after the unshare, so it would change nothing for a
   worker that never forks (and the jail sets RLIMIT_NPROC=0 precisely so it
   cannot). Claiming it here would be theatre. */
static bool browser_renderer_enter_namespaces(void) {
#if !defined(SYS_unshare)
    return false;
#else
    uid_t uid = getuid();
    gid_t gid = getgid();

    /* The user namespace must come first and alone: it is what grants the
       privilege needed to unshare the remaining namespaces unprivileged. */
    if (syscall(SYS_unshare, CLONE_NEWUSER) != 0) return false;

    /* setgroups must be denied BEFORE gid_map is writable, otherwise the
       kernel rejects the gid mapping for an unprivileged writer. */
    if (!browser_renderer_write_proc("/proc/self/setgroups", "deny\n")) {
        return false;
    }

    char map[64];
    int n = snprintf(map, sizeof map, "%u %u 1\n", (unsigned)gid, (unsigned)gid);
    if (n <= 0 || (size_t)n >= sizeof map) return false;
    if (!browser_renderer_write_proc("/proc/self/gid_map", map)) return false;

    n = snprintf(map, sizeof map, "%u %u 1\n", (unsigned)uid, (unsigned)uid);
    if (n <= 0 || (size_t)n >= sizeof map) return false;
    if (!browser_renderer_write_proc("/proc/self/uid_map", map)) return false;

    /* Now unprivileged inside the new user namespace: take the rest. */
    if (syscall(SYS_unshare, CLONE_NEWNET | CLONE_NEWIPC) != 0) return false;

    return true;
#endif
}

static bool s_browser_renderer_namespaces_active = false;

/* Posture accessor. The namespace layer is REPORTED, never silently assumed:
   a caller or gate that wants to know whether this renderer actually lost its
   route to the network must read this rather than infer it from a successful
   sandbox_enter(). */
bool rt_browser_renderer_namespaces_active(void) {
    return s_browser_renderer_namespaces_active;
}

typedef void (*BrowserRendererPreinitFn)(int, char**, char**);

static void browser_renderer_preinit(int argc, char** argv, char** envp) {
    static const char marker[] = "simple-browser-renderer";
    if (argc <= 0 || !argv || !argv[0] || strcmp(argv[0], marker) != 0) {
        return;
    }
    if (!envp || envp[0] != NULL ||
        prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) {
        _exit(126);
    }

    /* Order is load-bearing: namespaces (needs openat + a writable /proc)
       before landlock (declares handled_access_fs with no allow rules, so all
       writes die) before seccomp (allow-list contains neither unshare nor
       openat).

       Namespace loss is recorded, not fatal. Ubuntu 24.04 ships
       kernel.apparmor_restrict_unprivileged_userns=1, which lets an unconfined
       binary create a user namespace but strips its capabilities, so the
       follow-up CLONE_NEWNET returns EPERM. Treating that as fatal would turn
       a working seccomp+landlock jail into NO jail on every default Ubuntu
       host — strictly worse security for a stricter-looking check. The honest
       posture is: enter the strongest jail available and publish which layers
       were obtained via rt_browser_renderer_namespaces_active(). */
    s_browser_renderer_namespaces_active = browser_renderer_enter_namespaces();

    if (!browser_renderer_apply_landlock() ||
        !browser_renderer_apply_startup_seccomp()) {
        _exit(126);
    }
    s_browser_renderer_preinit_active = true;
}

__attribute__((section(".preinit_array"), used))
static BrowserRendererPreinitFn const browser_renderer_preinit_entry =
    browser_renderer_preinit;

bool rt_browser_renderer_preinit_active_for_test(void) {
    return s_browser_renderer_preinit_active;
}

static bool browser_renderer_apply_seccomp(void) {
#if !defined(BROWSER_RENDERER_AUDIT_ARCH) || !defined(SYS_seccomp)
    return false;
#else
    struct sock_filter filter[] = {
        BPF_STMT(
            BPF_LD | BPF_W | BPF_ABS,
            (uint32_t)offsetof(struct seccomp_data, arch)),
        BPF_JUMP(
            BPF_JMP | BPF_JEQ | BPF_K,
            BROWSER_RENDERER_AUDIT_ARCH, 1, 0),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
        BPF_STMT(
            BPF_LD | BPF_W | BPF_ABS,
            (uint32_t)offsetof(struct seccomp_data, nr)),
#if defined(__x86_64__)
        BPF_JUMP(BPF_JMP | BPF_JGE | BPF_K, 0x40000000U, 0, 1),
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
#endif
        /* ALLOW-list: only the syscalls the jailed renderer worker needs.
           Audited against hosted_browser_renderer_worker.spl's post-enter
           runtime: blocking read/write loops on the two inherited pipe fds,
           anonymous memory management for the JS/layout heap, futex-based
           runtime locks, clocks/sleeps, signal return paths, event polling
           on inherited fds, randomness, and clean exit. Everything else --
           including any future kernel syscall -- falls through to the
           default SECCOMP_RET_KILL_PROCESS below. Fail closed. */
#ifdef __NR_read
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_read),
#endif
#ifdef __NR_write
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_write),
#endif
#ifdef __NR_readv
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_readv),
#endif
#ifdef __NR_writev
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_writev),
#endif
#ifdef __NR_close
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_close),
#endif
#ifdef __NR_fstat
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_fstat),
#endif
#ifdef __NR_fstat64
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_fstat64),
#endif
#ifdef __NR_mmap
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_mmap),
#endif
#ifdef __NR_mmap2
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_mmap2),
#endif
#ifdef __NR_munmap
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_munmap),
#endif
#ifdef __NR_mprotect
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_mprotect),
#endif
#ifdef __NR_mremap
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_mremap),
#endif
#ifdef __NR_brk
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_brk),
#endif
#ifdef __NR_madvise
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_madvise),
#endif
#ifdef __NR_futex
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_futex),
#endif
#ifdef __NR_futex_time64
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_futex_time64),
#endif
#ifdef __NR_clock_gettime
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_clock_gettime),
#endif
#ifdef __NR_clock_gettime64
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_clock_gettime64),
#endif
#ifdef __NR_clock_nanosleep
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_clock_nanosleep),
#endif
#ifdef __NR_clock_nanosleep_time64
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_clock_nanosleep_time64),
#endif
#ifdef __NR_nanosleep
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_nanosleep),
#endif
#ifdef __NR_gettimeofday
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_gettimeofday),
#endif
#ifdef __NR_exit
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_exit),
#endif
#ifdef __NR_exit_group
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_exit_group),
#endif
#ifdef __NR_rt_sigreturn
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_rt_sigreturn),
#endif
#ifdef __NR_sigreturn
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_sigreturn),
#endif
#ifdef __NR_sigaltstack
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_sigaltstack),
#endif
#ifdef __NR_rt_sigaction
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_rt_sigaction),
#endif
#ifdef __NR_rt_sigprocmask
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_rt_sigprocmask),
#endif
#ifdef __NR_restart_syscall
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_restart_syscall),
#endif
#ifdef __NR_epoll_create1
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_epoll_create1),
#endif
#ifdef __NR_epoll_ctl
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_epoll_ctl),
#endif
#ifdef __NR_epoll_wait
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_epoll_wait),
#endif
#ifdef __NR_epoll_pwait
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_epoll_pwait),
#endif
#ifdef __NR_epoll_pwait2
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_epoll_pwait2),
#endif
#ifdef __NR_poll
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_poll),
#endif
#ifdef __NR_ppoll
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_ppoll),
#endif
#ifdef __NR_ppoll_time64
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_ppoll_time64),
#endif
#ifdef __NR_getrandom
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_getrandom),
#endif
#ifdef __NR_sched_yield
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_sched_yield),
#endif
#ifdef __NR_getpid
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_getpid),
#endif
#ifdef __NR_gettid
        BROWSER_RENDERER_ALLOW_SYSCALL(__NR_gettid),
#endif
        BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS)
    };
    struct sock_fprog program = {
        .len = (unsigned short)(sizeof(filter) / sizeof(filter[0])),
        .filter = filter
    };
    return syscall(
        SYS_seccomp, SECCOMP_SET_MODE_FILTER,
        SECCOMP_FILTER_FLAG_TSYNC, &program) == 0;
#endif
}

bool rt_browser_renderer_sandbox_enter(void) {
    if (!s_browser_renderer_preinit_active ||
        !browser_renderer_set_limit(RLIMIT_CORE, 0, 0) ||
        !browser_renderer_set_limit(
            RLIMIT_AS, 512U * 1024U * 1024U, 512U * 1024U * 1024U) ||
        !browser_renderer_set_limit(RLIMIT_CPU, 30, 30) ||
        !browser_renderer_set_limit(RLIMIT_FSIZE, 0, 0) ||
        !browser_renderer_set_limit(RLIMIT_NPROC, 0, 0) ||
        !browser_renderer_set_limit(RLIMIT_NOFILE, 4, 4) ||
        prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 ||
        !browser_renderer_apply_landlock() ||
        !browser_renderer_apply_seccomp()) {
        return false;
    }
    return true;
}

#else

bool rt_browser_renderer_sandbox_enter(void) {
    return false;
}

#endif

#endif /* POSIX */

/* Backfill: runtime.h prototype with no C definition (caught by the Stage4
   runtime-capsule gate). Mirrors env_process.rs rt_process_wait semantics:
   returns child exit code, -1 on error, -2 on timeout (child keeps running). */
#ifdef _WIN32
int64_t rt_process_wait(int64_t pid, int64_t timeout_ms) {
    (void)pid; (void)timeout_ms;
    return -1;
}
#else
int64_t rt_process_wait(int64_t pid, int64_t timeout_ms) {
    if (pid <= 0) return -1;
    if (timeout_ms <= 0) {
        int status = 0;
        if (waitpid((pid_t)pid, &status, 0) < 0) return -1;
        if (WIFEXITED(status)) return (int64_t)WEXITSTATUS(status);
        return -1;
    }
    int64_t waited_ms = 0;
    for (;;) {
        int status = 0;
        pid_t r = waitpid((pid_t)pid, &status, WNOHANG);
        if (r < 0) return -1;
        if (r > 0) {
            if (WIFEXITED(status)) return (int64_t)WEXITSTATUS(status);
            return -1;
        }
        if (waited_ms >= timeout_ms) return -2;
        usleep(10 * 1000);
        waited_ms += 10;
    }
}
#endif
