/*
 * Simple Runtime Threading Library - Implementation
 *
 * Cross-platform threading primitives.
 * Supports pthread (Linux/macOS) and Windows threads.
 */

#include "runtime_thread.h"
#include "runtime_memtrack.h"

#include <stdlib.h>
#include <stdio.h>
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
    HANDLE_CONDVAR,
    HANDLE_POOL_TASK
} HandleType;

typedef struct {
    HandleType type;
    void* ptr;
} HandleEntry;

static HandleEntry g_handles[MAX_HANDLES];

/* Freelist stack for O(1) handle alloc/free */
static int64_t g_freelist[MAX_HANDLES];
static int64_t g_freelist_top = -1;  /* -1 means empty (not yet initialized) */
static int g_freelist_initialized = 0;

/* Read-write lock: allows concurrent get_handle reads */
#ifdef SPL_THREAD_PTHREAD
static pthread_rwlock_t g_handle_rwlock = PTHREAD_RWLOCK_INITIALIZER;
#define HANDLE_RDLOCK()   pthread_rwlock_rdlock(&g_handle_rwlock)
#define HANDLE_RDUNLOCK() pthread_rwlock_unlock(&g_handle_rwlock)
#define HANDLE_WRLOCK()   pthread_rwlock_wrlock(&g_handle_rwlock)
#define HANDLE_WRUNLOCK() pthread_rwlock_unlock(&g_handle_rwlock)
#else
static SRWLOCK g_handle_srwlock = SRWLOCK_INIT;
#define HANDLE_RDLOCK()   AcquireSRWLockShared(&g_handle_srwlock)
#define HANDLE_RDUNLOCK() ReleaseSRWLockShared(&g_handle_srwlock)
#define HANDLE_WRLOCK()   AcquireSRWLockExclusive(&g_handle_srwlock)
#define HANDLE_WRUNLOCK() ReleaseSRWLockExclusive(&g_handle_srwlock)
#endif

static void init_freelist(void) {
    if (!g_freelist_initialized) {
        /* Push all free slots onto the freelist (skip index 0 = invalid) */
        g_freelist_top = -1;
        for (int64_t i = MAX_HANDLES - 1; i >= 1; i--) {
            g_freelist[++g_freelist_top] = i;
        }
        g_freelist_initialized = 1;
    }
}

/* Public initialization function - called at startup */
void spl_thread_init(void) {
    /* Initialize handle array to zeros */
    for (int i = 0; i < MAX_HANDLES; i++) {
        g_handles[i].type = HANDLE_FREE;
        g_handles[i].ptr = NULL;
    }
    /* Initialize the freelist for O(1) handle allocation */
    init_freelist();
}

static int64_t alloc_handle(HandleType type, void* ptr) {
    init_freelist();

    HANDLE_WRLOCK();

    int64_t handle = 0;
    if (g_freelist_top >= 0) {
        handle = g_freelist[g_freelist_top--];
        g_handles[handle].type = type;
        g_handles[handle].ptr = ptr;
    }

    HANDLE_WRUNLOCK();

    return handle;
}

static void* get_handle(int64_t handle, HandleType expected_type) {
    if (handle <= 0 || handle >= MAX_HANDLES) {
        return NULL;
    }

    HANDLE_RDLOCK();

    void* ptr = NULL;
    if (g_handles[handle].type == expected_type) {
        ptr = g_handles[handle].ptr;
    }

    HANDLE_RDUNLOCK();

    return ptr;
}

static void free_handle(int64_t handle) {
    if (handle <= 0 || handle >= MAX_HANDLES) {
        return;
    }

    HANDLE_WRLOCK();

    g_handles[handle].type = HANDLE_FREE;
    g_handles[handle].ptr = NULL;
    g_freelist[++g_freelist_top] = handle;

    HANDLE_WRUNLOCK();
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

/* ================================================================
 * rt_thread_* — Isolated thread API (native codegen)
 *
 * Cranelift `Any` = (type_tag: i64, value: i64).
 * For closures, value is a heap pointer where [0] = fn_ptr.
 * The closure calling convention is fn_ptr(closure_ptr).
 * ================================================================ */

typedef int64_t (*rt_closure_fn_t)(int64_t);
typedef int64_t (*rt_closure2_fn_t)(int64_t, int64_t);

typedef struct {
    rt_closure_fn_t  entry;
    rt_closure2_fn_t entry2;
    int64_t          closure_ptr;
    int64_t          data1;
    int64_t          data2;
    int              arity;
    int64_t          result;
    int              done;
#ifdef SPL_THREAD_PTHREAD
    pthread_t        thread;
#else
    HANDLE           thread;
#endif
} RtThreadData;

static void* rt_isolated_wrapper(void* raw) {
    RtThreadData* td = (RtThreadData*)raw;
    if (td->arity == 2) {
        td->result = td->entry2(td->data1, td->data2);
    } else {
        td->result = td->entry(td->closure_ptr);
    }
    td->done = 1;
    return NULL;
}

#ifdef SPL_THREAD_WINDOWS
static DWORD WINAPI rt_isolated_wrapper_win(LPVOID raw) {
    RtThreadData* td = (RtThreadData*)raw;
    if (td->arity == 2) {
        td->result = td->entry2(td->data1, td->data2);
    } else {
        td->result = td->entry(td->closure_ptr);
    }
    td->done = 1;
    return 0;
}
#endif

int64_t rt_thread_spawn_isolated(int64_t arg0, int64_t arg1) {
    int64_t closure_ptr = (arg1 != 0) ? arg1 : arg0;
    rt_closure_fn_t fn_ptr = *(rt_closure_fn_t*)(intptr_t)closure_ptr;
    RtThreadData* td = (RtThreadData*)SPL_MALLOC(sizeof(RtThreadData), "rt_thread");
    if (!td) return 0;
    td->entry       = fn_ptr;
    td->entry2      = NULL;
    td->closure_ptr = closure_ptr;
    td->data1       = 0;
    td->data2       = 0;
    td->arity       = 1;
    td->result      = 0;
    td->done        = 0;

#ifdef SPL_THREAD_PTHREAD
    if (pthread_create(&td->thread, NULL, rt_isolated_wrapper, td) != 0) {
        SPL_FREE(td);
        return 0;
    }
#else
    td->thread = CreateThread(NULL, 0, rt_isolated_wrapper_win, td, 0, NULL);
    if (td->thread == NULL) {
        SPL_FREE(td);
        return 0;
    }
#endif
    return alloc_handle(HANDLE_THREAD, td);
}

int64_t rt_thread_spawn_isolated2(int64_t fn_ptr, int64_t data1, int64_t data2) {
    rt_closure2_fn_t entry = (rt_closure2_fn_t)(intptr_t)(fn_ptr >> 3);
    RtThreadData* td = (RtThreadData*)SPL_MALLOC(sizeof(RtThreadData), "rt_thread2");
    if (!td) return 0;
    td->entry       = NULL;
    td->entry2      = entry;
    td->closure_ptr = 0;
    td->data1       = data1;
    td->data2       = data2;
    td->arity       = 2;
    td->result      = 0;
    td->done        = 0;

#ifdef SPL_THREAD_PTHREAD
    if (pthread_create(&td->thread, NULL, rt_isolated_wrapper, td) != 0) {
        SPL_FREE(td);
        return 0;
    }
#else
    td->thread = CreateThread(NULL, 0, rt_isolated_wrapper_win, td, 0, NULL);
    if (td->thread == NULL) {
        SPL_FREE(td);
        return 0;
    }
#endif
    return alloc_handle(HANDLE_THREAD, td);
}

int64_t rt_thread_join(int64_t handle) {
    RtThreadData* td = (RtThreadData*)get_handle(handle, HANDLE_THREAD);
    if (!td) return 0;
#ifdef SPL_THREAD_PTHREAD
    pthread_join(td->thread, NULL);
#else
    WaitForSingleObject(td->thread, INFINITE);
    CloseHandle(td->thread);
#endif
    int64_t result = td->result;
    SPL_FREE(td);
    free_handle(handle);
    return result;
}

int64_t rt_thread_is_done(int64_t handle) {
    RtThreadData* td = (RtThreadData*)get_handle(handle, HANDLE_THREAD);
    if (!td) return 1;
    return td->done ? 1 : 0;
}

int64_t rt_thread_id(int64_t handle) {
    RtThreadData* td = (RtThreadData*)get_handle(handle, HANDLE_THREAD);
    if (!td) return 0;
#ifdef SPL_THREAD_PTHREAD
    return (int64_t)(intptr_t)td->thread;
#else
    return (int64_t)GetThreadId(td->thread);
#endif
}

void rt_thread_free(int64_t handle) {
    RtThreadData* td = (RtThreadData*)get_handle(handle, HANDLE_THREAD);
    if (!td) return;
#ifdef SPL_THREAD_PTHREAD
    pthread_detach(td->thread);
#else
    CloseHandle(td->thread);
#endif
    SPL_FREE(td);
    free_handle(handle);
}

void rt_thread_sleep(int64_t millis) {
    spl_thread_sleep(millis);
}

void rt_thread_yield(void) {
    spl_thread_yield();
}

/* ================================================================
 * rt_pool_* — Runtime-owned closure task pool (native codegen)
 * ================================================================ */

typedef struct RtPoolTask {
    rt_closure_fn_t entry;
    int64_t closure_ptr;
    int64_t result;
    int done;
    struct RtPoolTask* next;
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_t lock;
    pthread_cond_t done_cond;
#else
    CRITICAL_SECTION lock;
    CONDITION_VARIABLE done_cond;
#endif
} RtPoolTask;

static RtPoolTask* g_pool_head = NULL;
static RtPoolTask* g_pool_tail = NULL;
static int g_pool_started = 0;
static int g_pool_worker_count = 0;

#ifdef SPL_THREAD_PTHREAD
static pthread_mutex_t g_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_pool_not_empty = PTHREAD_COND_INITIALIZER;
#else
static CRITICAL_SECTION g_pool_lock;
static CONDITION_VARIABLE g_pool_not_empty;
static INIT_ONCE g_pool_once = INIT_ONCE_STATIC_INIT;
#endif

static int rt_pool_default_worker_count(void) {
    int64_t count = spl_thread_cpu_count();
    if (count < 1) return 1;
    if (count > 64) return 64;
    return (int)count;
}

static RtPoolTask* rt_pool_pop_task(void) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    while (!g_pool_head) {
        pthread_cond_wait(&g_pool_not_empty, &g_pool_lock);
    }
    RtPoolTask* task = g_pool_head;
    g_pool_head = task->next;
    if (!g_pool_head) g_pool_tail = NULL;
    task->next = NULL;
    pthread_mutex_unlock(&g_pool_lock);
    return task;
#else
    EnterCriticalSection(&g_pool_lock);
    while (!g_pool_head) {
        SleepConditionVariableCS(&g_pool_not_empty, &g_pool_lock, INFINITE);
    }
    RtPoolTask* task = g_pool_head;
    g_pool_head = task->next;
    if (!g_pool_head) g_pool_tail = NULL;
    task->next = NULL;
    LeaveCriticalSection(&g_pool_lock);
    return task;
#endif
}

static void rt_pool_complete_task(RtPoolTask* task, int64_t result) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&task->lock);
    task->result = result;
    task->done = 1;
    pthread_cond_broadcast(&task->done_cond);
    pthread_mutex_unlock(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    task->result = result;
    task->done = 1;
    WakeAllConditionVariable(&task->done_cond);
    LeaveCriticalSection(&task->lock);
#endif
}

static void* rt_pool_worker_main(void* raw) {
    (void)raw;
    for (;;) {
        RtPoolTask* task = rt_pool_pop_task();
        if (task && task->entry) {
            rt_pool_complete_task(task, task->entry(task->closure_ptr));
        }
    }
    return NULL;
}

#ifdef SPL_THREAD_WINDOWS
static DWORD WINAPI rt_pool_worker_main_win(LPVOID raw) {
    rt_pool_worker_main(raw);
    return 0;
}

static BOOL CALLBACK rt_pool_init_once(PINIT_ONCE once, PVOID param, PVOID* context) {
    (void)once; (void)param; (void)context;
    InitializeCriticalSection(&g_pool_lock);
    InitializeConditionVariable(&g_pool_not_empty);
    return TRUE;
}
#endif

static void rt_pool_start(void) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_started) {
        pthread_mutex_unlock(&g_pool_lock);
        return;
    }
    g_pool_started = 1;
    g_pool_worker_count = rt_pool_default_worker_count();
    pthread_mutex_unlock(&g_pool_lock);

    for (int i = 0; i < g_pool_worker_count; i++) {
        pthread_t thread;
        if (pthread_create(&thread, NULL, rt_pool_worker_main, NULL) == 0) {
            pthread_detach(thread);
        }
    }
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_started) {
        LeaveCriticalSection(&g_pool_lock);
        return;
    }
    g_pool_started = 1;
    g_pool_worker_count = rt_pool_default_worker_count();
    LeaveCriticalSection(&g_pool_lock);

    for (int i = 0; i < g_pool_worker_count; i++) {
        HANDLE thread = CreateThread(NULL, 0, rt_pool_worker_main_win, NULL, 0, NULL);
        if (thread) CloseHandle(thread);
    }
#endif
}

static void rt_pool_push_task(RtPoolTask* task) {
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_tail) {
        g_pool_tail->next = task;
    } else {
        g_pool_head = task;
    }
    g_pool_tail = task;
    pthread_cond_signal(&g_pool_not_empty);
    pthread_mutex_unlock(&g_pool_lock);
#else
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_tail) {
        g_pool_tail->next = task;
    } else {
        g_pool_head = task;
    }
    g_pool_tail = task;
    WakeConditionVariable(&g_pool_not_empty);
    LeaveCriticalSection(&g_pool_lock);
#endif
}

int64_t rt_pool_submit(int64_t arg0, int64_t arg1) {
    int64_t closure_ptr = (arg1 != 0) ? arg1 : arg0;
    if (!closure_ptr) return 0;
    rt_closure_fn_t fn_ptr = *(rt_closure_fn_t*)(intptr_t)closure_ptr;
    if (!fn_ptr) return 0;

    RtPoolTask* task = (RtPoolTask*)SPL_MALLOC(sizeof(RtPoolTask), "rt_pool_task");
    if (!task) return 0;
    task->entry = fn_ptr;
    task->closure_ptr = closure_ptr;
    task->result = 0;
    task->done = 0;
    task->next = NULL;
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_init(&task->lock, NULL);
    pthread_cond_init(&task->done_cond, NULL);
#else
    InitializeCriticalSection(&task->lock);
    InitializeConditionVariable(&task->done_cond);
#endif

    int64_t handle = alloc_handle(HANDLE_POOL_TASK, task);
    if (!handle) {
#ifdef SPL_THREAD_PTHREAD
        pthread_cond_destroy(&task->done_cond);
        pthread_mutex_destroy(&task->lock);
#else
        DeleteCriticalSection(&task->lock);
#endif
        SPL_FREE(task);
        return 0;
    }

    rt_pool_start();
    rt_pool_push_task(task);
    return handle;
}

int64_t rt_pool_is_done(int64_t handle) {
    RtPoolTask* task = (RtPoolTask*)get_handle(handle, HANDLE_POOL_TASK);
    if (!task) return 1;
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&task->lock);
    int done = task->done;
    pthread_mutex_unlock(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    int done = task->done;
    LeaveCriticalSection(&task->lock);
#endif
    return done ? 1 : 0;
}

int64_t rt_pool_join(int64_t handle) {
    RtPoolTask* task = (RtPoolTask*)get_handle(handle, HANDLE_POOL_TASK);
    if (!task) return 0;
#ifdef SPL_THREAD_PTHREAD
    pthread_mutex_lock(&task->lock);
    while (!task->done) {
        pthread_cond_wait(&task->done_cond, &task->lock);
    }
    int64_t result = task->result;
    pthread_mutex_unlock(&task->lock);
    pthread_cond_destroy(&task->done_cond);
    pthread_mutex_destroy(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    while (!task->done) {
        SleepConditionVariableCS(&task->done_cond, &task->lock, INFINITE);
    }
    int64_t result = task->result;
    LeaveCriticalSection(&task->lock);
    DeleteCriticalSection(&task->lock);
#endif
    SPL_FREE(task);
    free_handle(handle);
    return result;
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
