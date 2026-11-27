/* One process-lifetime Windows IO owner binding, not a process registry.
 * The real thread HANDLE remains retained even after its thread exits, so a
 * reused DWORD thread ID can never rebind the owner. No lock spans a caller's
 * hash, launch, stream operation or wait. Initial cleanup failures poison the
 * binding and retain the failed HANDLE until process teardown. */
#ifndef SIMPLE_WINDOWS_PTY_OWNER_THREAD_PRIVATE_H
#define SIMPLE_WINDOWS_PTY_OWNER_THREAD_PRIVATE_H
#include <stdint.h>
#ifdef _WIN32
#include <windows.h>
static SRWLOCK simple_pty_owner_binding_lock_v1 = SRWLOCK_INIT;
static HANDLE simple_pty_owner_thread_v1;
static DWORD simple_pty_owner_thread_id_v1;
static int simple_pty_owner_phase_v1; /*0 unbound,1 bound,-2 exited,-3 failed*/

int64_t rt_windows_pty_owner_thread_guard_v1(void) {
    int64_t result = -3;
    AcquireSRWLockExclusive(&simple_pty_owner_binding_lock_v1);
    if (simple_pty_owner_phase_v1 == 0) {
        HANDLE candidate = NULL;
        BOOL copied = DuplicateHandle(GetCurrentProcess(), GetCurrentThread(),
            GetCurrentProcess(), &candidate,
            SYNCHRONIZE | THREAD_QUERY_LIMITED_INFORMATION, FALSE, 0);
        simple_pty_owner_thread_v1 = candidate; /*retain BEFORE status branch*/
        if (!copied || !candidate) {
            simple_pty_owner_phase_v1 = -3;
            if (candidate && CloseHandle(candidate)) simple_pty_owner_thread_v1 = NULL;
            goto done;
        }
        DWORD identity = GetThreadId(candidate);
        if (!identity || identity != GetCurrentThreadId()) {
            simple_pty_owner_phase_v1 = -3;
            if (CloseHandle(candidate)) simple_pty_owner_thread_v1 = NULL;
            goto done;
        }
        simple_pty_owner_thread_id_v1 = identity;
        simple_pty_owner_phase_v1 = 1;
    }
    if (simple_pty_owner_phase_v1 != 1) {
        result = simple_pty_owner_phase_v1;
        goto done;
    }
    DWORD state = WaitForSingleObject(simple_pty_owner_thread_v1, 0);
    if (state == WAIT_OBJECT_0) {
        simple_pty_owner_phase_v1 = -2;
        result = -2;
        goto done;
    }
    if (state != WAIT_TIMEOUT ||
            GetThreadId(simple_pty_owner_thread_v1) != simple_pty_owner_thread_id_v1) {
        simple_pty_owner_phase_v1 = -3;
        goto done;
    }
    result = GetCurrentThreadId() == simple_pty_owner_thread_id_v1 ? 1 : -1;
done:
    ReleaseSRWLockExclusive(&simple_pty_owner_binding_lock_v1);
    return result;
}
#else
int64_t rt_windows_pty_owner_thread_guard_v1(void) { return 0; }
#endif
#endif
