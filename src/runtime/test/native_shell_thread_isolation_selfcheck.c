/* Windows native ABI witness, linked only into the focused bootstrap fixture. */
#include "runtime.h"
#include <stdio.h>
#include <string.h>
#if defined(_WIN32)
#include <windows.h>

struct ShellThreadCase {
    int64_t code;
    HANDLE ready;
    HANDLE release;
};

static int64_t shell_test_text(const char* value) {
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}

static DWORD WINAPI shell_thread_check(void* opaque) {
    struct ShellThreadCase* test = (struct ShellThreadCase*)opaque;
    DWORD result = rt_shell_exit_code() == 0 ? 0 : 1;
    char command[48];
    snprintf(command, sizeof(command), "exit /b %lld", (long long)test->code);
    rt_shell_exec(shell_test_text(command));
    SetEvent(test->ready);
    if (WaitForSingleObject(test->release, 15000) != WAIT_OBJECT_0) return 2;
    if (rt_shell_exit_code() != test->code) result = 3;
    return result;
}

int64_t shell_thread_isolation_selfcheck(void) {
    HANDLE release = CreateEventW(NULL, TRUE, FALSE, NULL);
    HANDLE ready[2] = {CreateEventW(NULL, TRUE, FALSE, NULL), CreateEventW(NULL, TRUE, FALSE, NULL)};
    if (!release || !ready[0] || !ready[1]) return 10;
    struct ShellThreadCase cases[2] = {{4, ready[0], release}, {9, ready[1], release}};
    HANDLE threads[2] = {NULL, NULL};
    rt_shell_exec(shell_test_text("exit /b 11"));
    threads[0] = CreateThread(NULL, 0, shell_thread_check, &cases[0], 0, NULL);
    threads[1] = CreateThread(NULL, 0, shell_thread_check, &cases[1], 0, NULL);
    int64_t result = 0;
    if (!threads[0] || !threads[1]) result = 11;
    if (!result && WaitForMultipleObjects(2, ready, TRUE, 15000) != WAIT_OBJECT_0) result = 12;
    if (!result && rt_shell_exit_code() != 11) result = 13;
    SetEvent(release);
    if (threads[0] && threads[1] && WaitForMultipleObjects(2, threads, TRUE, 15000) != WAIT_OBJECT_0) result = 14;
    for (int i = 0; i < 2; ++i) {
        if (threads[i]) {
            DWORD code = 0;
            if (!GetExitCodeThread(threads[i], &code) || code != 0) result = 15;
            CloseHandle(threads[i]);
        }
        CloseHandle(ready[i]);
    }
    CloseHandle(release);
    rt_shell_exec(shell_test_text("exit /b 0"));
    return result;
}
#else
int64_t shell_thread_isolation_selfcheck(void) { return 77; }
#endif
