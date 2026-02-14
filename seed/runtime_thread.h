/*
 * Simple Runtime Threading Library - Header
 *
 * Cross-platform threading primitives for multi-threaded async runtime.
 * Supports pthread (Linux/macOS) and Windows threads.
 *
 * Design: SFFI-compatible, two-tier pattern.
 * All handles are opaque i64 values for Simple FFI.
 */

#ifndef SPL_RUNTIME_THREAD_H
#define SPL_RUNTIME_THREAD_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stdbool.h>

/* ===== Thread Handle (opaque) ===== */

typedef int64_t spl_thread_handle;
typedef int64_t spl_mutex_handle;
typedef int64_t spl_condvar_handle;

/* ===== Thread Management ===== */

/**
 * Create and start a new thread.
 *
 * Args:
 *   entry_point: Function pointer to thread entry (void* fn(void*))
 *   arg: Opaque argument passed to entry point
 *
 * Returns:
 *   Thread handle (> 0) on success, 0 on failure
 */
spl_thread_handle spl_thread_create(void* (*entry_point)(void*), void* arg);

/**
 * Wait for thread to complete.
 *
 * Args:
 *   handle: Thread handle from spl_thread_create
 *
 * Returns:
 *   true if joined successfully, false on error
 */
bool spl_thread_join(spl_thread_handle handle);

/**
 * Detach thread (no join required).
 *
 * Args:
 *   handle: Thread handle from spl_thread_create
 *
 * Returns:
 *   true if detached successfully, false on error
 */
bool spl_thread_detach(spl_thread_handle handle);

/**
 * Get current thread ID.
 *
 * Returns:
 *   Platform-specific thread ID
 */
int64_t spl_thread_current_id(void);

/**
 * Sleep current thread.
 *
 * Args:
 *   millis: Sleep duration in milliseconds
 */
void spl_thread_sleep(int64_t millis);

/**
 * Yield CPU to other threads.
 */
void spl_thread_yield(void);

/* ===== Mutex (Mutual Exclusion) ===== */

/**
 * Create new mutex.
 *
 * Returns:
 *   Mutex handle (> 0) on success, 0 on failure
 */
spl_mutex_handle spl_mutex_create(void);

/**
 * Lock mutex (blocking).
 *
 * Args:
 *   handle: Mutex handle from spl_mutex_create
 *
 * Returns:
 *   true if locked, false on error
 */
bool spl_mutex_lock(spl_mutex_handle handle);

/**
 * Try to lock mutex (non-blocking).
 *
 * Args:
 *   handle: Mutex handle from spl_mutex_create
 *
 * Returns:
 *   true if locked, false if already locked or error
 */
bool spl_mutex_try_lock(spl_mutex_handle handle);

/**
 * Unlock mutex.
 *
 * Args:
 *   handle: Mutex handle from spl_mutex_create
 *
 * Returns:
 *   true if unlocked, false on error
 */
bool spl_mutex_unlock(spl_mutex_handle handle);

/**
 * Destroy mutex.
 *
 * Args:
 *   handle: Mutex handle from spl_mutex_create
 */
void spl_mutex_destroy(spl_mutex_handle handle);

/* ===== Condition Variable ===== */

/**
 * Create new condition variable.
 *
 * Returns:
 *   Condvar handle (> 0) on success, 0 on failure
 */
spl_condvar_handle spl_condvar_create(void);

/**
 * Wait on condition variable (releases mutex, reacquires on wake).
 *
 * Args:
 *   cv_handle: Condvar handle from spl_condvar_create
 *   mutex_handle: Mutex handle (must be locked)
 *
 * Returns:
 *   true if woken, false on error
 */
bool spl_condvar_wait(spl_condvar_handle cv_handle, spl_mutex_handle mutex_handle);

/**
 * Wait with timeout (milliseconds).
 *
 * Args:
 *   cv_handle: Condvar handle from spl_condvar_create
 *   mutex_handle: Mutex handle (must be locked)
 *   timeout_ms: Timeout in milliseconds
 *
 * Returns:
 *   true if woken, false on timeout or error
 */
bool spl_condvar_wait_timeout(spl_condvar_handle cv_handle, spl_mutex_handle mutex_handle, int64_t timeout_ms);

/**
 * Signal one waiting thread.
 *
 * Args:
 *   handle: Condvar handle from spl_condvar_create
 *
 * Returns:
 *   true on success, false on error
 */
bool spl_condvar_signal(spl_condvar_handle handle);

/**
 * Signal all waiting threads.
 *
 * Args:
 *   handle: Condvar handle from spl_condvar_create
 *
 * Returns:
 *   true on success, false on error
 */
bool spl_condvar_broadcast(spl_condvar_handle handle);

/**
 * Destroy condition variable.
 *
 * Args:
 *   handle: Condvar handle from spl_condvar_create
 */
void spl_condvar_destroy(spl_condvar_handle handle);

/* ===== Platform Detection ===== */

/**
 * Get number of available CPU cores.
 *
 * Returns:
 *   Number of logical CPU cores
 */
int64_t spl_thread_cpu_count(void);

#ifdef __cplusplus
}
#endif

#endif /* SPL_RUNTIME_THREAD_H */
