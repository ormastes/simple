/* Native PTY provider used by the core-C bootstrap runtime. */
#ifndef _WIN32_WINNT
#define _WIN32_WINNT 0x0A00
#endif
#include "runtime.h"
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static int64_t pty_empty_text(void) { return rt_string_new(NULL, 0); }

#ifdef _WIN32
#include <windows.h>

#define PTY_SLOTS 64
typedef struct {
    bool used;
    HPCON console;
    HANDLE input;
    HANDLE output;
    HANDLE process;
} PtySlot;
static PtySlot pty_slots[PTY_SLOTS];
static SRWLOCK pty_lock = SRWLOCK_INIT;

static wchar_t* pty_wide(int64_t text) {
    int64_t len = rt_string_len(text);
    const uint8_t* data = rt_string_data(text);
    if (len <= 0 || !data || len > INT32_MAX) return NULL;
    int n = MultiByteToWideChar(CP_UTF8, 0, (const char*)data, (int)len, NULL, 0);
    if (n <= 0) return NULL;
    wchar_t* out = (wchar_t*)calloc((size_t)n + 1, sizeof(wchar_t));
    if (!out) return NULL;
    if (!MultiByteToWideChar(CP_UTF8, 0, (const char*)data, (int)len, out, n)) {
        free(out); return NULL;
    }
    return out;
}

int32_t rt_pty_open(int32_t rows, int32_t cols) {
    if (rows <= 0 || cols <= 0) return -1;
    HANDLE in_read = NULL, in_write = NULL, out_read = NULL, out_write = NULL;
    if (!CreatePipe(&in_read, &in_write, NULL, 0)) return -1;
    if (!CreatePipe(&out_read, &out_write, NULL, 0)) {
        CloseHandle(in_read); CloseHandle(in_write); return -1;
    }
    HPCON pc = NULL;
    COORD size = {(SHORT)cols, (SHORT)rows};
    /* Match the admitted Rust provider's cursor/input flags. */
    HRESULT hr = CreatePseudoConsole(size, in_read, out_write, 0x2 | 0x4, &pc);
    CloseHandle(in_read); CloseHandle(out_write);
    if (FAILED(hr)) { CloseHandle(in_write); CloseHandle(out_read); return -1; }
    AcquireSRWLockExclusive(&pty_lock);
    int32_t handle = -1;
    for (int i = 1; i < PTY_SLOTS; i++) if (!pty_slots[i].used) {
        pty_slots[i] = (PtySlot){true, pc, in_write, out_read, NULL}; handle = i; break;
    }
    ReleaseSRWLockExclusive(&pty_lock);
    if (handle < 0) { ClosePseudoConsole(pc); CloseHandle(in_write); CloseHandle(out_read); }
    return handle;
}

int64_t rt_pty_spawn(int32_t handle, int64_t shell) {
    if (handle <= 0 || handle >= PTY_SLOTS) return -1;
    wchar_t* cmd = pty_wide(shell);
    if (!cmd) return -1;
    AcquireSRWLockExclusive(&pty_lock);
    PtySlot* s = &pty_slots[handle];
    if (!s->used || s->process) { ReleaseSRWLockExclusive(&pty_lock); free(cmd); return -1; }
    SIZE_T bytes = 0;
    InitializeProcThreadAttributeList(NULL, 1, 0, &bytes);
    LPPROC_THREAD_ATTRIBUTE_LIST attrs = (LPPROC_THREAD_ATTRIBUTE_LIST)malloc(bytes);
    STARTUPINFOEXW si; PROCESS_INFORMATION pi;
    ZeroMemory(&si, sizeof(si)); ZeroMemory(&pi, sizeof(pi)); si.StartupInfo.cb = sizeof(si);
    /* Do not let the child retain the parent's console standard handles.
     * ConPTY supplies all three streams through its attribute. */
    si.StartupInfo.dwFlags = STARTF_USESTDHANDLES;
    si.StartupInfo.hStdInput = INVALID_HANDLE_VALUE;
    si.StartupInfo.hStdOutput = INVALID_HANDLE_VALUE;
    si.StartupInfo.hStdError = INVALID_HANDLE_VALUE;
    bool ok = attrs && InitializeProcThreadAttributeList(attrs, 1, 0, &bytes) &&
        UpdateProcThreadAttribute(attrs, 0, PROC_THREAD_ATTRIBUTE_PSEUDOCONSOLE,
                                  s->console, sizeof(s->console), NULL, NULL) &&
        CreateProcessW(NULL, cmd, NULL, NULL, FALSE,
                       EXTENDED_STARTUPINFO_PRESENT | CREATE_UNICODE_ENVIRONMENT,
                       NULL, NULL, &si.StartupInfo, &pi);
    if (attrs) { DeleteProcThreadAttributeList(attrs); free(attrs); }
    free(cmd);
    if (!ok) { ReleaseSRWLockExclusive(&pty_lock); return -1; }
    CloseHandle(pi.hThread); s->process = pi.hProcess;
    int64_t pid = (int64_t)pi.dwProcessId;
    ReleaseSRWLockExclusive(&pty_lock);
    return pid;
}

bool rt_pty_write(int64_t handle, int64_t data) {
    if (handle <= 0 || handle >= PTY_SLOTS) return false;
    int64_t len = rt_string_len(data); const uint8_t* bytes = rt_string_data(data);
    if (len < 0 || (!bytes && len)) return false;
    AcquireSRWLockShared(&pty_lock); PtySlot* s = &pty_slots[handle];
    if (!s->used) { ReleaseSRWLockShared(&pty_lock); return false; }
    size_t off = 0; bool ok = true;
    while (off < (size_t)len) { DWORD n = 0; if (!WriteFile(s->input, bytes + off, (DWORD)((size_t)len - off), &n, NULL) || !n) { ok = false; break; } off += n; }
    ReleaseSRWLockShared(&pty_lock); return ok;
}

int64_t rt_pty_read(int64_t handle, int64_t timeout_ms) {
    if (handle <= 0 || handle >= PTY_SLOTS || timeout_ms < 0) return pty_empty_text();
    uint8_t buf[4096]; DWORD available = 0, elapsed = 0;
    AcquireSRWLockShared(&pty_lock); PtySlot* s = &pty_slots[handle];
    if (!s->used) { ReleaseSRWLockShared(&pty_lock); return pty_empty_text(); }
    while (!PeekNamedPipe(s->output, NULL, 0, NULL, &available, NULL) || available == 0) {
        if (elapsed >= (DWORD)timeout_ms) { ReleaseSRWLockShared(&pty_lock); return pty_empty_text(); }
        DWORD step = (DWORD)timeout_ms - elapsed; if (step > 10) step = 10; Sleep(step); elapsed += step;
    }
    DWORD n = 0; if (available > sizeof(buf)) available = sizeof(buf);
    bool ok = ReadFile(s->output, buf, available, &n, NULL) != 0;
    ReleaseSRWLockShared(&pty_lock);
    return ok ? rt_string_new(buf, n) : pty_empty_text();
}

bool rt_pty_is_running(int64_t handle) {
    if (handle <= 0 || handle >= PTY_SLOTS) return false;
    AcquireSRWLockShared(&pty_lock); PtySlot* s = &pty_slots[handle]; DWORD code = 0;
    bool running = s->used && s->process && GetExitCodeProcess(s->process, &code) && code == STILL_ACTIVE;
    ReleaseSRWLockShared(&pty_lock); return running;
}

bool rt_pty_close(int64_t handle) {
    if (handle <= 0 || handle >= PTY_SLOTS) return false;
    AcquireSRWLockExclusive(&pty_lock); PtySlot s = pty_slots[handle];
    if (!s.used) { ReleaseSRWLockExclusive(&pty_lock); return false; }
    memset(&pty_slots[handle], 0, sizeof(PtySlot)); ReleaseSRWLockExclusive(&pty_lock);
    if (s.process) { DWORD code; if (GetExitCodeProcess(s.process, &code) && code == STILL_ACTIVE) TerminateProcess(s.process, 1); CloseHandle(s.process); }
    ClosePseudoConsole(s.console); CloseHandle(s.input); CloseHandle(s.output); return true;
}
#else
/* Hosted Unix builds currently use the Rust provider.  Keep the core-C ABI
 * closed and deterministic until its posix_openpt provider is admitted. */
int32_t rt_pty_open(int32_t rows, int32_t cols) { (void)rows; (void)cols; return -1; }
int64_t rt_pty_spawn(int32_t h, int64_t shell) { (void)h; (void)shell; return -1; }
bool rt_pty_write(int64_t h, int64_t data) { (void)h; (void)data; return false; }
int64_t rt_pty_read(int64_t h, int64_t ms) { (void)h; (void)ms; return pty_empty_text(); }
bool rt_pty_close(int64_t h) { (void)h; return false; }
bool rt_pty_is_running(int64_t h) { (void)h; return false; }
#endif
