/* Owner-specific real scope contract. Default: selected core-C owner with
 * TLS/thread checks. For genuine Simple core_memory compile with
 * SIMPLE_SCOPE_STATE_SINGLE_THREAD: its documented single-thread scope state
 * is tested, without claiming TLS. Resolve no scope API from a stub/backfill.
 * Selected Simple startup must run its actual module initializers. */
#include <stdint.h>
#include "runtime.h"

#if !defined(SIMPLE_SCOPE_STATE_SINGLE_THREAD)
#if defined(_WIN32)
#include <windows.h>
#else
#include <pthread.h>
#endif
static int foreign_scope_ok;

static void query_foreign_scope(void) {
    foreign_scope_ok = rt_transient_array_scope_state_v1() == 0 &&
        rt_transient_array_scope_begin() == 0 &&
        rt_transient_array_scope_pause() == 0 &&
        rt_transient_array_scope_end() == 0 &&
        rt_transient_array_scope_state_v1() == 0;
}

#if defined(_WIN32)
static DWORD WINAPI foreign_thread(void* unused) {
    (void)unused;
    query_foreign_scope();
    return 0;
}
static int run_foreign_thread(void) {
    foreign_scope_ok = 0;
    HANDLE thread = CreateThread(NULL, 0, foreign_thread, NULL, 0, NULL);
    if (!thread) return 0;
    DWORD wait = WaitForSingleObject(thread, INFINITE);
    CloseHandle(thread);
    return wait == WAIT_OBJECT_0 && foreign_scope_ok;
}
#else
static void* foreign_thread(void* unused) {
    (void)unused;
    query_foreign_scope();
    return NULL;
}
static int run_foreign_thread(void) {
    foreign_scope_ok = 0;
    pthread_t thread;
    if (pthread_create(&thread, NULL, foreign_thread, NULL) != 0) return 0;
    return pthread_join(thread, NULL) == 0 && foreign_scope_ok;
}
#endif
#endif

int main(void) {
    if (rt_transient_array_scope_state_v1() != 0) return 1;
    if (rt_transient_array_scope_pause() != 0 || rt_transient_array_scope_end() != 0) return 2;
    if (rt_transient_array_scope_state_v1() != 0) return 3;
    if (rt_transient_array_scope_begin() != 1) return 4;
    if (rt_transient_array_scope_state_v1() != 1 || rt_transient_array_scope_state_v1() != 1) return 5;
    if (rt_transient_array_scope_begin() != 0) return 6;
    if (rt_transient_array_scope_state_v1() != 1) return 7;
#if !defined(SIMPLE_SCOPE_STATE_SINGLE_THREAD)
    if (!run_foreign_thread()) return 8;
#endif
    if (rt_transient_array_scope_state_v1() != 1) return 9;
    if (rt_transient_array_scope_pause() != 1) return 10;
    if (rt_transient_array_scope_state_v1() != 2) return 11;
    if (rt_transient_array_scope_begin() != 0) return 12;
    if (rt_transient_array_scope_state_v1() != 2 || rt_transient_array_scope_state_v1() != 2) return 13;
#if !defined(SIMPLE_SCOPE_STATE_SINGLE_THREAD)
    if (!run_foreign_thread()) return 14;
#endif
    if (rt_transient_array_scope_state_v1() != 2) return 15;
    if (rt_transient_array_scope_end() != 1) return 16;
    if (rt_transient_array_scope_state_v1() != 0 || rt_transient_array_scope_end() != 0 ||
        rt_transient_array_scope_state_v1() != 0) return 17;
    if (rt_transient_array_scope_begin() != 1 || rt_transient_array_scope_state_v1() != 1 ||
        rt_transient_array_scope_end() != 1 || rt_transient_array_scope_state_v1() != 0) return 18;
    return 0;
}
