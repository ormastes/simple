/* Actual Windows thread-confinement fixture; NOT_RUN without a Windows host.
 * This exercises the production guard with two racing real threads. It does
 * not qualify Job, pipe, CPU, Docker or Simple language execution. */
#if defined(_WIN32)
#include <windows.h>
#include <stdio.h>
#include "../platform/runtime_windows_pty_owner_thread_private.h"

static HANDLE begin_event, ready_event, release_event;
static volatile LONG ready_count;
static int64_t outcomes[2];

static DWORD WINAPI contender(void *argument) {
    size_t index = (size_t)argument;
    if (WaitForSingleObject(begin_event, 5000) != WAIT_OBJECT_0) return 2;
    outcomes[index] = rt_windows_pty_owner_thread_guard_v1();
    if (InterlockedIncrement(&ready_count) == 2 && !SetEvent(ready_event)) return 3;
    if (outcomes[index] == 1 && WaitForSingleObject(release_event, 5000) != WAIT_OBJECT_0) return 4;
    return 0;
}

int main(void) {
    begin_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    ready_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    release_event = CreateEventW(NULL, TRUE, FALSE, NULL);
    if (!begin_event || !ready_event || !release_event) return 10;
    HANDLE threads[2];
    threads[0] = CreateThread(NULL, 0, contender, (void *)(size_t)0, 0, NULL);
    threads[1] = CreateThread(NULL, 0, contender, (void *)(size_t)1, 0, NULL);
    if (!threads[0] || !threads[1] || !SetEvent(begin_event)) return 11;
    if (WaitForSingleObject(ready_event, 5000) != WAIT_OBJECT_0) return 12;
    if (!((outcomes[0] == 1 && outcomes[1] == -1) ||
          (outcomes[1] == 1 && outcomes[0] == -1))) return 13;
    /* Main cannot use the live contender's owner even though it is in the
     * same process. A copied lease cannot change the pinned thread identity. */
    if (rt_windows_pty_owner_thread_guard_v1() != -1) return 14;
    if (!SetEvent(release_event) ||
        WaitForMultipleObjects(2, threads, TRUE, 5000) != WAIT_OBJECT_0) return 15;
    for (size_t index = 0; index < 2; ++index) {
        DWORD result = 999;
        if (!GetExitCodeThread(threads[index], &result) || result != 0) return 16;
    }
    /* The owner exited. Its retained real thread HANDLE prevents implicit
     * rebinding, including after the OS eventually recycles its numeric ID. */
    if (rt_windows_pty_owner_thread_guard_v1() != -2) return 17;
    if (!CloseHandle(threads[0]) || !CloseHandle(threads[1]) ||
        !CloseHandle(begin_event) || !CloseHandle(ready_event) ||
        !CloseHandle(release_event)) return 18;
    puts("PASS: one atomic owner, foreign-thread refusal, exited-owner refusal");
    return 0;
}
#else
int main(void) { return 77; }
#endif
