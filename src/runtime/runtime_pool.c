/*
 * Runtime-owned closure task pool for native Simple codegen.
 *
 * This file intentionally exports only rt_pool_* symbols. The Rust runtime
 * already exports rt_thread_* symbols, so runtime_thread.c cannot be linked
 * into simple-runtime without duplicate definitions.
 */

#include <stdint.h>
#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
    #define RT_POOL_WINDOWS
    #include <windows.h>
#else
    #define RT_POOL_PTHREAD
    #include <pthread.h>
    #include <unistd.h>
#endif

typedef int64_t (*rt_pool_closure_fn_t)(int64_t);

typedef struct RtPoolTask {
    rt_pool_closure_fn_t entry;
    int64_t closure_ptr;
    int64_t result;
    int done;
    struct RtPoolTask* next;
#ifdef RT_POOL_PTHREAD
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
static int g_pool_configured_worker_count = 0;

#ifdef RT_POOL_PTHREAD
static pthread_mutex_t g_pool_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_pool_not_empty = PTHREAD_COND_INITIALIZER;
#else
static CRITICAL_SECTION g_pool_lock;
static CONDITION_VARIABLE g_pool_not_empty;
static INIT_ONCE g_pool_once = INIT_ONCE_STATIC_INIT;

static BOOL CALLBACK rt_pool_init_once(PINIT_ONCE once, PVOID param, PVOID* context) {
    (void)once;
    (void)param;
    (void)context;
    InitializeCriticalSection(&g_pool_lock);
    InitializeConditionVariable(&g_pool_not_empty);
    return TRUE;
}
#endif

static int rt_pool_default_worker_count(void) {
#ifdef RT_POOL_PTHREAD
    long n = sysconf(_SC_NPROCESSORS_ONLN);
    if (n < 1) n = 4;
    if (n > 32) n = 32;
    return (int)n;
#else
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    int n = (int)info.dwNumberOfProcessors;
    if (n < 1) n = 4;
    if (n > 32) n = 32;
    return n;
#endif
}

static int rt_pool_clamp_worker_count(int64_t count) {
    if (count < 1) return 1;
    if (count > 64) return 64;
    return (int)count;
}

static int rt_pool_effective_worker_count(void) {
    return g_pool_configured_worker_count > 0
        ? g_pool_configured_worker_count
        : rt_pool_default_worker_count();
}

static RtPoolTask* rt_pool_pop_task(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    while (g_pool_head == NULL) {
        pthread_cond_wait(&g_pool_not_empty, &g_pool_lock);
    }
    RtPoolTask* task = g_pool_head;
    g_pool_head = task->next;
    if (g_pool_head == NULL) g_pool_tail = NULL;
    task->next = NULL;
    pthread_mutex_unlock(&g_pool_lock);
    return task;
#else
    EnterCriticalSection(&g_pool_lock);
    while (g_pool_head == NULL) {
        SleepConditionVariableCS(&g_pool_not_empty, &g_pool_lock, INFINITE);
    }
    RtPoolTask* task = g_pool_head;
    g_pool_head = task->next;
    if (g_pool_head == NULL) g_pool_tail = NULL;
    task->next = NULL;
    LeaveCriticalSection(&g_pool_lock);
    return task;
#endif
}

static void rt_pool_complete_task(RtPoolTask* task, int64_t result) {
#ifdef RT_POOL_PTHREAD
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
        rt_pool_complete_task(task, task->entry(task->closure_ptr));
    }
    return NULL;
}

#ifdef RT_POOL_WINDOWS
static DWORD WINAPI rt_pool_worker_main_win(LPVOID raw) {
    rt_pool_worker_main(raw);
    return 0;
}
#endif

static int rt_pool_spawn_worker(void) {
#ifdef RT_POOL_PTHREAD
    pthread_t thread;
    if (pthread_create(&thread, NULL, rt_pool_worker_main, NULL) == 0) {
        pthread_detach(thread);
        return 1;
    }
    return 0;
#else
    HANDLE thread = CreateThread(NULL, 0, rt_pool_worker_main_win, NULL, 0, NULL);
    if (thread != NULL) {
        CloseHandle(thread);
        return 1;
    }
    return 0;
#endif
}

static int rt_pool_start(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_started) {
        int count = g_pool_worker_count;
        pthread_mutex_unlock(&g_pool_lock);
        return count;
    }
    g_pool_started = 1;
    pthread_mutex_unlock(&g_pool_lock);

    int requested = rt_pool_effective_worker_count();
    int started = 0;
    for (int i = 0; i < requested; i++) {
        started += rt_pool_spawn_worker();
    }

    pthread_mutex_lock(&g_pool_lock);
    g_pool_worker_count = started;
    pthread_mutex_unlock(&g_pool_lock);
    return started;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_started) {
        int count = g_pool_worker_count;
        LeaveCriticalSection(&g_pool_lock);
        return count;
    }
    g_pool_started = 1;
    LeaveCriticalSection(&g_pool_lock);

    int requested = rt_pool_effective_worker_count();
    int started = 0;
    for (int i = 0; i < requested; i++) {
        started += rt_pool_spawn_worker();
    }

    EnterCriticalSection(&g_pool_lock);
    g_pool_worker_count = started;
    LeaveCriticalSection(&g_pool_lock);
    return started;
#endif
}

int64_t rt_pool_set_parallelism(int64_t workers) {
    int requested = rt_pool_clamp_worker_count(workers);
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (!g_pool_started) {
        g_pool_configured_worker_count = requested;
        g_pool_worker_count = requested;
        pthread_mutex_unlock(&g_pool_lock);
        return requested;
    }
    int current = g_pool_worker_count;
    if (requested <= current) {
        pthread_mutex_unlock(&g_pool_lock);
        return current;
    }
    pthread_mutex_unlock(&g_pool_lock);

    int added = 0;
    for (int i = current; i < requested; i++) {
        added += rt_pool_spawn_worker();
    }

    pthread_mutex_lock(&g_pool_lock);
    g_pool_worker_count += added;
    int actual = g_pool_worker_count;
    pthread_mutex_unlock(&g_pool_lock);
    return actual;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    if (!g_pool_started) {
        g_pool_configured_worker_count = requested;
        g_pool_worker_count = requested;
        LeaveCriticalSection(&g_pool_lock);
        return requested;
    }
    int current = g_pool_worker_count;
    if (requested <= current) {
        LeaveCriticalSection(&g_pool_lock);
        return current;
    }
    LeaveCriticalSection(&g_pool_lock);

    int added = 0;
    for (int i = current; i < requested; i++) {
        added += rt_pool_spawn_worker();
    }

    EnterCriticalSection(&g_pool_lock);
    g_pool_worker_count += added;
    int actual = g_pool_worker_count;
    LeaveCriticalSection(&g_pool_lock);
    return actual;
#endif
}

int64_t rt_pool_get_parallelism(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int count = g_pool_started ? g_pool_worker_count : rt_pool_effective_worker_count();
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int count = g_pool_started ? g_pool_worker_count : rt_pool_effective_worker_count();
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}

int64_t rt_pool_uses_global_fifo_queue(void) {
    return 1;
}

static void rt_pool_push_task(RtPoolTask* task) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_tail != NULL) {
        g_pool_tail->next = task;
    } else {
        g_pool_head = task;
    }
    g_pool_tail = task;
    pthread_cond_signal(&g_pool_not_empty);
    pthread_mutex_unlock(&g_pool_lock);
#else
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_tail != NULL) {
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
    if (closure_ptr == 0) return 0;

    rt_pool_closure_fn_t entry = *(rt_pool_closure_fn_t*)(intptr_t)closure_ptr;
    if (entry == NULL) return 0;

    RtPoolTask* task = (RtPoolTask*)calloc(1, sizeof(RtPoolTask));
    if (task == NULL) return 0;
    task->entry = entry;
    task->closure_ptr = closure_ptr;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_init(&task->lock, NULL);
    pthread_cond_init(&task->done_cond, NULL);
#else
    InitializeCriticalSection(&task->lock);
    InitializeConditionVariable(&task->done_cond);
#endif

    if (rt_pool_start() <= 0) {
        rt_pool_complete_task(task, task->entry(task->closure_ptr));
        return (int64_t)(intptr_t)task;
    }

    rt_pool_push_task(task);
    return (int64_t)(intptr_t)task;
}

int64_t rt_pool_is_done(int64_t handle) {
    RtPoolTask* task = (RtPoolTask*)(intptr_t)handle;
    if (task == NULL) return 1;
#ifdef RT_POOL_PTHREAD
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
    RtPoolTask* task = (RtPoolTask*)(intptr_t)handle;
    if (task == NULL) return 0;
#ifdef RT_POOL_PTHREAD
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
    free(task);
    return result;
}
