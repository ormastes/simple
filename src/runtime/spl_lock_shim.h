/* spl_lock_shim.h -- private, header-only Win32/POSIX mutex+condvar shim.
 *
 * Replaces the `#ifdef pthread ... #else Win32 ... #endif` twins that each
 * lock site used to spell out by hand. Every function is a 1:1 rename of the
 * primitive it wraps; nothing here adds a lock, picks signal vs broadcast for
 * the caller, or does one-time init:
 *
 *   Win32 (_WIN32 || _WIN64): CRITICAL_SECTION + CONDITION_VARIABLE,
 *     waits are SleepConditionVariableCS(..., INFINITE).
 *   otherwise:                pthread_mutex_t + pthread_cond_t.
 *
 * One-time init stays at each site (its own INIT_ONCE / static initializer);
 * spl_lk_init only performs the per-object init call that site already made.
 * spl_lk_destroy matches the existing sites: POSIX destroys cond then mutex,
 * Win32 deletes the critical section only (CONDITION_VARIABLE has no destroy).
 *
 * Include contract: include AFTER <windows.h> (Win32) or <pthread.h> (POSIX).
 * Names are deliberately not rt_*: nothing here is exported. */
#ifndef SPL_LOCK_SHIM_H
#define SPL_LOCK_SHIM_H

#if defined(_WIN32) || defined(_WIN64)
typedef CRITICAL_SECTION spl_lk_mutex;
typedef CONDITION_VARIABLE spl_lk_cond;
static inline void spl_lk_init(spl_lk_mutex* m, spl_lk_cond* c) {
    InitializeCriticalSection(m);
    InitializeConditionVariable(c);
}
static inline void spl_lk_destroy(spl_lk_mutex* m, spl_lk_cond* c) {
    (void)c;
    DeleteCriticalSection(m);
}
static inline void spl_lk_lock(spl_lk_mutex* m) { EnterCriticalSection(m); }
static inline void spl_lk_unlock(spl_lk_mutex* m) { LeaveCriticalSection(m); }
static inline void spl_lk_wait(spl_lk_cond* c, spl_lk_mutex* m) { SleepConditionVariableCS(c, m, INFINITE); }
static inline void spl_lk_signal(spl_lk_cond* c) { WakeConditionVariable(c); }
static inline void spl_lk_broadcast(spl_lk_cond* c) { WakeAllConditionVariable(c); }
#else
typedef pthread_mutex_t spl_lk_mutex;
typedef pthread_cond_t spl_lk_cond;
static inline void spl_lk_init(spl_lk_mutex* m, spl_lk_cond* c) {
    pthread_mutex_init(m, NULL);
    pthread_cond_init(c, NULL);
}
static inline void spl_lk_destroy(spl_lk_mutex* m, spl_lk_cond* c) {
    pthread_cond_destroy(c);
    pthread_mutex_destroy(m);
}
static inline void spl_lk_lock(spl_lk_mutex* m) { pthread_mutex_lock(m); }
static inline void spl_lk_unlock(spl_lk_mutex* m) { pthread_mutex_unlock(m); }
static inline void spl_lk_wait(spl_lk_cond* c, spl_lk_mutex* m) { pthread_cond_wait(c, m); }
static inline void spl_lk_signal(spl_lk_cond* c) { pthread_cond_signal(c); }
static inline void spl_lk_broadcast(spl_lk_cond* c) { pthread_cond_broadcast(c); }
#endif

#endif /* SPL_LOCK_SHIM_H */
