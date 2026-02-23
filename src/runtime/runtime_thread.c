/*
 * Simple Runtime Threading Library - Implementation
 *
 * Cross-platform threading primitives.
 * Supports pthread (Linux/macOS) and Windows threads.
 */

#include "runtime_thread.h"
#include "runtime_memtrack.h"

#include <stdlib.h>
#include <string.h>

/* ================================================================
 * Platform Detection
 * ================================================================ */

#if defined(_WIN32) || defined(_WIN64)
    #define SPL_THREAD_WINDOWS
    #include <windows.h>
    #include <process.h>
#else
    #define SPL_THREAD_PTHREAD
    #include <pthread.h>
    #include <unistd.h>
    #include <time.h>
    #include <errno.h>
    #if defined(__APPLE__) || defined(__MACH__)
        #include <sys/sysctl.h>
    #endif
#endif

/* ================================================================
 * Internal Handle Storage
 * ================================================================ */

#define MAX_HANDLES 4096

typedef enum {
    HANDLE_FREE = 0,
    HANDLE_THREAD,
    HANDLE_MUTEX,
    HANDLE_CONDVAR
} HandleType;

typedef struct {
    HandleType type;
    void* ptr;
} HandleEntry;

static HandleEntry g_handles[MAX_HANDLES];
static int64_t g_next_handle = 1;

#ifdef SPL_THREAD_PTHREAD
static pthread_mutex_t g_handle_lock = PTHREAD_MUTEX_INITIALIZER;
#else
static CRITICAL_SECTION g_handle_lock;
static int g_handle_lock_initialized = 0;
#endif

static void init_handle_lock(void) {
#ifdef SPL_THREAD_WINDOWS
    if (!g_handle_lock_initialized) {
        InitializeCriticalSection(&g_handle_lock);
        g_handle_lock_initialized = 1;
    }
#endif
}

/* Public initialization function - called at startup */
void spl_thread_init(void) {
    init_handle_lock();
    /* Initialize handle array to zeros */
    for (int i = 0; i < MAX_HANDLES; i++) {
        g_handles[i].type = HANDLE_FREE;
        g_handles[i].ptr = NULL;
    }
}

static int64_t alloc_handle(HandleType type, void* ptr) {
    init_handle_lock();

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_handle_lock);
#else
    EnterCriticalSection(&g_handle_lock);
#endif

    int64_t handle = 0;
    for (int64_t i = 0; i < MAX_HANDLES; i++) {
        int64_t idx = (g_next_handle + i) % MAX_HANDLES;
        if (idx == 0) idx = 1;  /* Skip 0 (reserved for errors) */
        if (g_handles[idx].type == HANDLE_FREE) {
            g_handles[idx].type = type;
            g_handles[idx].ptr = ptr;
            handle = idx;
            g_next_handle = (idx + 1) % MAX_HANDLES;
            break;
        }
    }

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_unlock(&g_handle_lock);
#else
    LeaveCriticalSection(&g_handle_lock);
#endif

    return handle;
}

static void* get_handle(int64_t handle, HandleType expected_type) {
    if (handle <= 0 || handle >= MAX_HANDLES) {
        return NULL;
    }

    init_handle_lock();

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_handle_lock);
#else
    EnterCriticalSection(&g_handle_lock);
#endif

    void* ptr = NULL;
    if (g_handles[handle].type == expected_type) {
        ptr = g_handles[handle].ptr;
    }

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_unlock(&g_handle_lock);
#else
    LeaveCriticalSection(&g_handle_lock);
#endif

    return ptr;
}

static void free_handle(int64_t handle) {
    if (handle <= 0 || handle >= MAX_HANDLES) {
        return;
    }

    init_handle_lock();

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_handle_lock);
#else
    EnterCriticalSection(&g_handle_lock);
#endif

    g_handles[handle].type = HANDLE_FREE;
    g_handles[handle].ptr = NULL;

#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_unlock(&g_handle_lock);
#else
    LeaveCriticalSection(&g_handle_lock);
#endif
}

/* ================================================================
 * Thread Management
 * ================================================================ */

spl_thread_handle spl_thread_create(void* (*entry_point)(void*), void* arg) {
    if (!entry_point) {
        return 0;
    }

#ifdef SPL_THREAD_PTHREAD
    pthread_t* thread = (pthread_t*)SPL_MALLOC(sizeof(pthread_t), "thread");
    if (!thread) {
        return 0;
    }

    if (pthread_create(thread, NULL, entry_point, arg) != 0) {
        SPL_FREE(thread);
        return 0;
    }

    return alloc_handle(HANDLE_THREAD, thread);

#else  /* Windows */
    HANDLE thread = CreateThread(
        NULL,           /* default security */
        0,              /* default stack size */
        (LPTHREAD_START_ROUTINE)entry_point,
        arg,
        0,              /* run immediately */
        NULL            /* don't need thread ID */
    );

    if (thread == NULL) {
        return 0;
    }

    return alloc_handle(HANDLE_THREAD, thread);
#endif
}

bool spl_thread_join(spl_thread_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_t* thread = (pthread_t*)get_handle(handle, HANDLE_THREAD);
    if (!thread) {
        return false;
    }

    bool success = (pthread_join(*thread, NULL) == 0);
    SPL_FREE(thread);
    free_handle(handle);
    return success;

#else  /* Windows */
    HANDLE thread = (HANDLE)get_handle(handle, HANDLE_THREAD);
    if (!thread) {
        return false;
    }

    DWORD result = WaitForSingleObject(thread, INFINITE);
    CloseHandle(thread);
    free_handle(handle);
    return (result == WAIT_OBJECT_0);
#endif
}

bool spl_thread_detach(spl_thread_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_t* thread = (pthread_t*)get_handle(handle, HANDLE_THREAD);
    if (!thread) {
        return false;
    }

    bool success = (pthread_detach(*thread) == 0);
    SPL_FREE(thread);
    free_handle(handle);
    return success;

#else  /* Windows */
    HANDLE thread = (HANDLE)get_handle(handle, HANDLE_THREAD);
    if (!thread) {
        return false;
    }

    CloseHandle(thread);
    free_handle(handle);
    return true;
#endif
}

int64_t spl_thread_current_id(void) {
#ifdef SPL_THREAD_PTHREAD
    return (int64_t)pthread_self();
#else
    return (int64_t)GetCurrentThreadId();
#endif
}

void spl_thread_sleep(int64_t millis) {
    if (millis <= 0) {
        return;
    }

#ifdef SPL_THREAD_PTHREAD
    struct timespec ts;
    ts.tv_sec = millis / 1000;
    ts.tv_nsec = (millis % 1000) * 1000000;
    nanosleep(&ts, NULL);
#else
    Sleep((DWORD)millis);
#endif
}

void spl_thread_yield(void) {
#ifdef SPL_THREAD_PTHREAD
    sched_yield();
#else
    SwitchToThread();
#endif
}

/* ================================================================
 * Mutex
 * ================================================================ */

spl_mutex_handle spl_mutex_create(void) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t* mutex = (pthread_mutex_t*)SPL_MALLOC(sizeof(pthread_mutex_t), "mutex");
    if (!mutex) {
        return 0;
    }

    if (pthread_mutex_init(mutex, NULL) != 0) {
        SPL_FREE(mutex);
        return 0;
    }

    return alloc_handle(HANDLE_MUTEX, mutex);

#else  /* Windows */
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)SPL_MALLOC(sizeof(CRITICAL_SECTION), "cs_mutex");
    if (!cs) {
        return 0;
    }

    InitializeCriticalSection(cs);
    return alloc_handle(HANDLE_MUTEX, cs);
#endif
}

bool spl_mutex_lock(spl_mutex_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(handle, HANDLE_MUTEX);
    if (!mutex) {
        return false;
    }

    return (pthread_mutex_lock(mutex) == 0);

#else  /* Windows */
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(handle, HANDLE_MUTEX);
    if (!cs) {
        return false;
    }

    EnterCriticalSection(cs);
    return true;
#endif
}

bool spl_mutex_try_lock(spl_mutex_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(handle, HANDLE_MUTEX);
    if (!mutex) {
        return false;
    }

    return (pthread_mutex_trylock(mutex) == 0);

#else  /* Windows */
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(handle, HANDLE_MUTEX);
    if (!cs) {
        return false;
    }

    return TryEnterCriticalSection(cs);
#endif
}

bool spl_mutex_unlock(spl_mutex_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(handle, HANDLE_MUTEX);
    if (!mutex) {
        return false;
    }

    return (pthread_mutex_unlock(mutex) == 0);

#else  /* Windows */
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(handle, HANDLE_MUTEX);
    if (!cs) {
        return false;
    }

    LeaveCriticalSection(cs);
    return true;
#endif
}

void spl_mutex_destroy(spl_mutex_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(handle, HANDLE_MUTEX);
    if (mutex) {
        pthread_mutex_destroy(mutex);
        SPL_FREE(mutex);
        free_handle(handle);
    }

#else  /* Windows */
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(handle, HANDLE_MUTEX);
    if (cs) {
        DeleteCriticalSection(cs);
        SPL_FREE(cs);
        free_handle(handle);
    }
#endif
}

/* ================================================================
 * Condition Variable
 * ================================================================ */

spl_condvar_handle spl_condvar_create(void) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)SPL_MALLOC(sizeof(pthread_cond_t), "condvar");
    if (!cond) {
        return 0;
    }

    if (pthread_cond_init(cond, NULL) != 0) {
        SPL_FREE(cond);
        return 0;
    }

    return alloc_handle(HANDLE_CONDVAR, cond);

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)SPL_MALLOC(sizeof(CONDITION_VARIABLE), "cv_condvar");
    if (!cv) {
        return 0;
    }

    InitializeConditionVariable(cv);
    return alloc_handle(HANDLE_CONDVAR, cv);
#endif
}

bool spl_condvar_wait(spl_condvar_handle cv_handle, spl_mutex_handle mutex_handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)get_handle(cv_handle, HANDLE_CONDVAR);
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(mutex_handle, HANDLE_MUTEX);

    if (!cond || !mutex) {
        return false;
    }

    return (pthread_cond_wait(cond, mutex) == 0);

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)get_handle(cv_handle, HANDLE_CONDVAR);
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(mutex_handle, HANDLE_MUTEX);

    if (!cv || !cs) {
        return false;
    }

    return SleepConditionVariableCS(cv, cs, INFINITE);
#endif
}

bool spl_condvar_wait_timeout(spl_condvar_handle cv_handle, spl_mutex_handle mutex_handle, int64_t timeout_ms) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)get_handle(cv_handle, HANDLE_CONDVAR);
    pthread_mutex_t* mutex = (pthread_mutex_t*)get_handle(mutex_handle, HANDLE_MUTEX);

    if (!cond || !mutex) {
        return false;
    }

    struct timespec ts;
    clock_gettime(CLOCK_REALTIME, &ts);
    ts.tv_sec += timeout_ms / 1000;
    ts.tv_nsec += (timeout_ms % 1000) * 1000000;
    if (ts.tv_nsec >= 1000000000) {
        ts.tv_sec++;
        ts.tv_nsec -= 1000000000;
    }

    int result = pthread_cond_timedwait(cond, mutex, &ts);
    return (result == 0);

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)get_handle(cv_handle, HANDLE_CONDVAR);
    CRITICAL_SECTION* cs = (CRITICAL_SECTION*)get_handle(mutex_handle, HANDLE_MUTEX);

    if (!cv || !cs) {
        return false;
    }

    return SleepConditionVariableCS(cv, cs, (DWORD)timeout_ms);
#endif
}

bool spl_condvar_signal(spl_condvar_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)get_handle(handle, HANDLE_CONDVAR);
    if (!cond) {
        return false;
    }

    return (pthread_cond_signal(cond) == 0);

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)get_handle(handle, HANDLE_CONDVAR);
    if (!cv) {
        return false;
    }

    WakeConditionVariable(cv);
    return true;
#endif
}

bool spl_condvar_broadcast(spl_condvar_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)get_handle(handle, HANDLE_CONDVAR);
    if (!cond) {
        return false;
    }

    return (pthread_cond_broadcast(cond) == 0);

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)get_handle(handle, HANDLE_CONDVAR);
    if (!cv) {
        return false;
    }

    WakeAllConditionVariable(cv);
    return true;
#endif
}

void spl_condvar_destroy(spl_condvar_handle handle) {
#ifdef SPL_THREAD_PTHREAD
    pthread_cond_t* cond = (pthread_cond_t*)get_handle(handle, HANDLE_CONDVAR);
    if (cond) {
        pthread_cond_destroy(cond);
        SPL_FREE(cond);
        free_handle(handle);
    }

#else  /* Windows */
    CONDITION_VARIABLE* cv = (CONDITION_VARIABLE*)get_handle(handle, HANDLE_CONDVAR);
    if (cv) {
        /* Windows condition variables don't need explicit cleanup */
        SPL_FREE(cv);
        free_handle(handle);
    }
#endif
}

/* ================================================================
 * Platform Detection
 * ================================================================ */

int64_t spl_thread_cpu_count(void) {
#ifdef SPL_THREAD_PTHREAD
    #if defined(__APPLE__) || defined(__MACH__)
        int count;
        size_t size = sizeof(count);
        if (sysctlbyname("hw.logicalcpu", &count, &size, NULL, 0) == 0) {
            return (int64_t)count;
        }
        return 4;  /* fallback */
    #else
        long count = sysconf(_SC_NPROCESSORS_ONLN);
        return (count > 0) ? (int64_t)count : 4;
    #endif

#else  /* Windows */
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return (int64_t)sysinfo.dwNumberOfProcessors;
#endif
}

/* ================================================================
 * Thread Pool Worker Spawn Helper
 * ================================================================ */

/*
 * Forward declaration for Simple worker_loop_entry function.
 * This function is defined in thread_pool.spl and compiled to C.
 * In interpreter mode, this function may not be available.
 */
extern void worker_loop_entry(int64_t pool_id) __attribute__((weak));

/* Thread worker wrapper for pthread */
#ifdef SPL_THREAD_PTHREAD
static void* worker_thread_wrapper(void* arg) {
    int64_t pool_id = (int64_t)(intptr_t)arg;

    /* Call Simple worker function if linked */
    if (worker_loop_entry) {
        worker_loop_entry(pool_id);
    }

    return NULL;
}
#else  /* Windows */
static DWORD WINAPI worker_thread_wrapper(LPVOID arg) {
    int64_t pool_id = (int64_t)(intptr_t)arg;

    /* Call Simple worker function if linked */
    if (worker_loop_entry) {
        worker_loop_entry(pool_id);
    }

    return 0;
}
#endif

spl_thread_handle spl_thread_pool_spawn_worker(int64_t pool_id) {
    /* Check if worker function is available (compiled mode only) */
    if (!worker_loop_entry) {
        return 0;  /* Not available in interpreter mode */
    }

    /* Use standard thread creation with wrapper */
#ifdef SPL_THREAD_PTHREAD
    pthread_t* thread = (pthread_t*)SPL_MALLOC(sizeof(pthread_t), "thread");
    if (!thread) {
        return 0;
    }

    int result = pthread_create(thread, NULL, worker_thread_wrapper,
                                (void*)(intptr_t)pool_id);
    if (result != 0) {
        SPL_FREE(thread);
        return 0;
    }

    return alloc_handle(HANDLE_THREAD, thread);

#else  /* Windows */
    HANDLE thread = CreateThread(
        NULL,                       /* default security attributes */
        0,                          /* default stack size */
        worker_thread_wrapper,      /* thread function */
        (LPVOID)(intptr_t)pool_id, /* argument to thread function */
        0,                          /* default creation flags */
        NULL                        /* thread identifier not needed */
    );

    if (thread == NULL) {
        return 0;
    }

    return alloc_handle(HANDLE_THREAD, thread);
#endif
}
