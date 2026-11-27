/* Windows handle accounting for the piped-process primitive
 * (bug: windows_piped_process_cold_handle_growth_2026_10_12).
 * Spawns/pipes/closes many cycles (serial, then concurrent) and asserts the
 * process handle count returns to its post-warmup baseline.
 * Exit 0 = pass, 1 = leak/failure, 77 = not Windows (skipped). */
#include "runtime.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef _WIN32
int main(void) { puts("SKIP: windows only"); return 77; }
#else
#include <windows.h>
#include <psapi.h>

static const char** test_args;
static int64_t test_arg_count;
int64_t rt_array_len(SplArray* ignored) { (void)ignored; return test_arg_count; }
int64_t rt_array_get(SplArray* ignored, int64_t index) { (void)ignored; return index + 1; }
const uint8_t* rt_string_data(int64_t value) { return (const uint8_t*)test_args[value - 1]; }

/* Capture-path runtime symbols, unused by the piped path. */
int64_t rt_string_len(int64_t s) { (void)s; return 0; }
SplArray* rt_array_new(int64_t c) { (void)c; return NULL; }
int64_t rt_string_new(const uint8_t* b, uint64_t l) { (void)b; (void)l; return 0; }
int8_t rt_array_push(SplArray* a, int64_t v) { (void)a; (void)v; return 0; }
void rt_array_free(SplArray* a) { (void)a; }
int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_tuple_new(int64_t n) { (void)n; return 0; }
int8_t rt_tuple_set(int64_t t, int64_t i, int64_t v) { (void)t; (void)i; (void)v; return 0; }

static DWORD handles(void) {
    DWORD n = 0;
    GetProcessHandleCount(GetCurrentProcess(), &n);
    return n;
}

static SRWLOCK arg_lock = SRWLOCK_INIT;

/* One cycle: spawn cmd.exe, write stdin, drain stdout, close. */
static int cycle(void) {
    static const char* args[2] = {"/c", "echo hi"};
    static SplArray placeholder;
    AcquireSRWLockExclusive(&arg_lock);
    test_args = args;
    test_arg_count = 2;
    int64_t pid = rt_process_spawn_piped("cmd.exe", &placeholder);
    ReleaseSRWLockExclusive(&arg_lock);
    if (pid <= 0) return 0;
    (void)rt_process_write_stdin(pid, "x\r\n");
    for (int i = 0; i < 400 && rt_process_is_alive(pid); i++) Sleep(5);
    for (int i = 0; i < 4; i++) (void)rt_process_read_stdout(pid);
    return rt_process_close_piped(pid) ? 1 : 0;
}

static volatile LONG failures;
static DWORD WINAPI worker(LPVOID arg) {
    int n = (int)(intptr_t)arg;
    for (int i = 0; i < n; i++) if (!cycle()) InterlockedIncrement(&failures);
    return 0;
}

int main(void) {
    for (int i = 0; i < 3; i++) if (!cycle()) { puts("FAIL warmup"); return 1; }
    Sleep(100);
    DWORD baseline = handles();
    for (int i = 0; i < 100; i++) if (!cycle()) InterlockedIncrement(&failures);
    Sleep(100);
    DWORD after_serial = handles();
    HANDLE t[4];
    for (int i = 0; i < 4; i++) t[i] = CreateThread(NULL, 0, worker, (LPVOID)(intptr_t)15, 0, NULL);
    WaitForMultipleObjects(4, t, TRUE, 180000);
    for (int i = 0; i < 4; i++) CloseHandle(t[i]);
    Sleep(100);
    DWORD after_conc = handles();
    PROCESS_MEMORY_COUNTERS pmc = {0};
    GetProcessMemoryInfo(GetCurrentProcess(), &pmc, sizeof(pmc));
    printf("handles baseline=%lu serial=%lu concurrent=%lu failures=%ld peak_rss_kb=%lu\n",
           (unsigned long)baseline, (unsigned long)after_serial, (unsigned long)after_conc,
           (long)failures, (unsigned long)(pmc.PeakWorkingSetSize / 1024));
    if (failures) { puts("FAIL: cycle failures"); return 1; }
    if (after_serial > baseline || after_conc > baseline) { puts("FAIL: handle leak"); return 1; }
    puts("PASS");
    return 0;
}
#endif
