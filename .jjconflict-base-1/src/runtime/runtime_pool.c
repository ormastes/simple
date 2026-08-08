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
    #include <sched.h>
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

#define RT_POOL_MAX_WORKERS 64

typedef struct RtPoolQueue {
    RtPoolTask* head;
    RtPoolTask* tail;
} RtPoolQueue;

typedef struct RtPoolWorkerArg {
    int worker_id;
} RtPoolWorkerArg;

static RtPoolQueue g_pool_queues[RT_POOL_MAX_WORKERS];
static int g_pool_started = 0;
static int g_pool_worker_count = 0;
static int g_pool_configured_worker_count = 0;
static int g_pool_next_worker = 0;
static int g_pool_busy_workers = 0;
static int g_pool_pending_tasks = 0;
static int g_pool_blocked_workers = 0;
static int64_t g_pool_submitted_tasks = 0;
static int64_t g_pool_completed_tasks = 0;

#ifdef RT_POOL_WINDOWS
__declspec(thread) static int g_pool_worker_tls = 0;
__declspec(thread) static int g_pool_worker_blocked_tls = 0;
#else
static __thread int g_pool_worker_tls = 0;
static __thread int g_pool_worker_blocked_tls = 0;
#endif

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
    if (count > RT_POOL_MAX_WORKERS) return RT_POOL_MAX_WORKERS;
    return (int)count;
}

static int rt_pool_effective_worker_count(void) {
    return g_pool_configured_worker_count > 0
        ? g_pool_configured_worker_count
        : rt_pool_default_worker_count();
}

static int rt_pool_has_tasks_locked(void) {
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : rt_pool_effective_worker_count();
    if (count > RT_POOL_MAX_WORKERS) count = RT_POOL_MAX_WORKERS;
    for (int i = 0; i < count; i++) {
        if (g_pool_queues[i].head != NULL) return 1;
    }
    return 0;
}

static RtPoolTask* rt_pool_queue_pop_head(RtPoolQueue* queue) {
    RtPoolTask* task = queue->head;
    if (task == NULL) return NULL;
    queue->head = task->next;
    if (queue->head == NULL) queue->tail = NULL;
    task->next = NULL;
    return task;
}

static void rt_pool_queue_push_tail(RtPoolQueue* queue, RtPoolTask* task) {
    task->next = NULL;
    if (queue->tail != NULL) {
        queue->tail->next = task;
    } else {
        queue->head = task;
    }
    queue->tail = task;
}

static RtPoolTask* rt_pool_pop_task(int worker_id) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    while (!rt_pool_has_tasks_locked()) {
        pthread_cond_wait(&g_pool_not_empty, &g_pool_lock);
    }
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : 1;
    RtPoolTask* task = rt_pool_queue_pop_head(&g_pool_queues[worker_id % count]);
    for (int offset = 1; task == NULL && offset < count; offset++) {
        int victim = (worker_id + offset) % count;
        task = rt_pool_queue_pop_head(&g_pool_queues[victim]);
    }
    if (task != NULL) {
        if (g_pool_pending_tasks > 0) g_pool_pending_tasks--;
        g_pool_busy_workers++;
    }
    pthread_mutex_unlock(&g_pool_lock);
    return task;
#else
    EnterCriticalSection(&g_pool_lock);
    while (!rt_pool_has_tasks_locked()) {
        SleepConditionVariableCS(&g_pool_not_empty, &g_pool_lock, INFINITE);
    }
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : 1;
    RtPoolTask* task = rt_pool_queue_pop_head(&g_pool_queues[worker_id % count]);
    for (int offset = 1; task == NULL && offset < count; offset++) {
        int victim = (worker_id + offset) % count;
        task = rt_pool_queue_pop_head(&g_pool_queues[victim]);
    }
    if (task != NULL) {
        if (g_pool_pending_tasks > 0) g_pool_pending_tasks--;
        g_pool_busy_workers++;
    }
    LeaveCriticalSection(&g_pool_lock);
    return task;
#endif
}

static void rt_pool_complete_task(RtPoolTask* task, int64_t result) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_busy_workers > 0) g_pool_busy_workers--;
    g_pool_completed_tasks++;
    pthread_mutex_unlock(&g_pool_lock);
    pthread_mutex_lock(&task->lock);
    task->result = result;
    task->done = 1;
    pthread_cond_broadcast(&task->done_cond);
    pthread_mutex_unlock(&task->lock);
#else
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_busy_workers > 0) g_pool_busy_workers--;
    g_pool_completed_tasks++;
    LeaveCriticalSection(&g_pool_lock);
    EnterCriticalSection(&task->lock);
    task->result = result;
    task->done = 1;
    WakeAllConditionVariable(&task->done_cond);
    LeaveCriticalSection(&task->lock);
#endif
}

static void* rt_pool_worker_main(void* raw) {
    RtPoolWorkerArg* arg = (RtPoolWorkerArg*)raw;
    int worker_id = arg != NULL ? arg->worker_id : 0;
    free(arg);
    g_pool_worker_tls = 1;
    g_pool_worker_blocked_tls = 0;
    for (;;) {
        RtPoolTask* task = rt_pool_pop_task(worker_id);
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

static int rt_pool_spawn_worker(int worker_id) {
    RtPoolWorkerArg* arg = (RtPoolWorkerArg*)malloc(sizeof(RtPoolWorkerArg));
    if (arg == NULL) return 0;
    arg->worker_id = worker_id;
#ifdef RT_POOL_PTHREAD
    pthread_t thread;
    if (pthread_create(&thread, NULL, rt_pool_worker_main, arg) == 0) {
        pthread_detach(thread);
        return 1;
    }
    free(arg);
    return 0;
#else
    HANDLE thread = CreateThread(NULL, 0, rt_pool_worker_main_win, arg, 0, NULL);
    if (thread != NULL) {
        CloseHandle(thread);
        return 1;
    }
    free(arg);
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
        if (rt_pool_spawn_worker(started)) started++;
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
        if (rt_pool_spawn_worker(started)) started++;
    }

    EnterCriticalSection(&g_pool_lock);
    g_pool_worker_count = started;
    LeaveCriticalSection(&g_pool_lock);
    return started;
#endif
}

static void rt_pool_mark_worker_blocked(void) {
#ifdef RT_POOL_PTHREAD
    if (!g_pool_worker_tls || g_pool_worker_blocked_tls) return;
    pthread_mutex_lock(&g_pool_lock);
    g_pool_blocked_workers++;
    pthread_mutex_unlock(&g_pool_lock);
    g_pool_worker_blocked_tls = 1;
#else
    if (!g_pool_worker_tls || g_pool_worker_blocked_tls) return;
    EnterCriticalSection(&g_pool_lock);
    g_pool_blocked_workers++;
    LeaveCriticalSection(&g_pool_lock);
    g_pool_worker_blocked_tls = 1;
#endif
}

static void rt_pool_mark_worker_unblocked(void) {
#ifdef RT_POOL_PTHREAD
    if (!g_pool_worker_tls || !g_pool_worker_blocked_tls) return;
    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_blocked_workers > 0) g_pool_blocked_workers--;
    pthread_mutex_unlock(&g_pool_lock);
    g_pool_worker_blocked_tls = 0;
#else
    if (!g_pool_worker_tls || !g_pool_worker_blocked_tls) return;
    EnterCriticalSection(&g_pool_lock);
    if (g_pool_blocked_workers > 0) g_pool_blocked_workers--;
    LeaveCriticalSection(&g_pool_lock);
    g_pool_worker_blocked_tls = 0;
#endif
}

void rt_pool_worker_block_begin(void) {
    rt_pool_mark_worker_blocked();
}

void rt_pool_worker_block_end(void) {
    rt_pool_mark_worker_unblocked();
}

static int rt_pool_maybe_spawn_compensation_worker(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int should_spawn =
        g_pool_started &&
        g_pool_pending_tasks > 0 &&
        g_pool_blocked_workers > 0 &&
        g_pool_worker_count < RT_POOL_MAX_WORKERS;
    int worker_id = g_pool_worker_count;
    pthread_mutex_unlock(&g_pool_lock);

    if (!should_spawn) return 0;
    if (!rt_pool_spawn_worker(worker_id)) return 0;

    pthread_mutex_lock(&g_pool_lock);
    if (g_pool_worker_count == worker_id) {
        g_pool_worker_count++;
    }
    int spawned = g_pool_worker_count > worker_id ? 1 : 0;
    pthread_mutex_unlock(&g_pool_lock);
    return spawned;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int should_spawn =
        g_pool_started &&
        g_pool_pending_tasks > 0 &&
        g_pool_blocked_workers > 0 &&
        g_pool_worker_count < RT_POOL_MAX_WORKERS;
    int worker_id = g_pool_worker_count;
    LeaveCriticalSection(&g_pool_lock);

    if (!should_spawn) return 0;
    if (!rt_pool_spawn_worker(worker_id)) return 0;

    EnterCriticalSection(&g_pool_lock);
    if (g_pool_worker_count == worker_id) {
        g_pool_worker_count++;
    }
    int spawned = g_pool_worker_count > worker_id ? 1 : 0;
    LeaveCriticalSection(&g_pool_lock);
    return spawned;
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
        if (rt_pool_spawn_worker(current + added)) added++;
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
        if (rt_pool_spawn_worker(current + added)) added++;
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

static void rt_pool_push_task(RtPoolTask* task) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : 1;
    int target = g_pool_next_worker % count;
    g_pool_next_worker = (g_pool_next_worker + 1) % count;
    rt_pool_queue_push_tail(&g_pool_queues[target], task);
    g_pool_submitted_tasks++;
    g_pool_pending_tasks++;
    pthread_cond_signal(&g_pool_not_empty);
    pthread_mutex_unlock(&g_pool_lock);
    rt_pool_maybe_spawn_compensation_worker();
#else
    EnterCriticalSection(&g_pool_lock);
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : 1;
    int target = g_pool_next_worker % count;
    g_pool_next_worker = (g_pool_next_worker + 1) % count;
    rt_pool_queue_push_tail(&g_pool_queues[target], task);
    g_pool_submitted_tasks++;
    g_pool_pending_tasks++;
    WakeConditionVariable(&g_pool_not_empty);
    LeaveCriticalSection(&g_pool_lock);
    rt_pool_maybe_spawn_compensation_worker();
#endif
}

int64_t rt_pool_uses_global_fifo_queue(void) {
    return 0;
}

int64_t rt_pool_uses_work_stealing(void) {
    return 1;
}

int64_t rt_pool_safepoint(void) {
    if (!g_pool_worker_tls) return 0;
    rt_pool_mark_worker_blocked();
    int64_t spawned = rt_pool_maybe_spawn_compensation_worker();
#ifdef RT_POOL_PTHREAD
    sched_yield();
#else
    Sleep(0);
#endif
    rt_pool_mark_worker_unblocked();
    return spawned;
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
#ifdef RT_POOL_PTHREAD
        pthread_mutex_lock(&g_pool_lock);
        g_pool_submitted_tasks++;
        pthread_mutex_unlock(&g_pool_lock);
#else
        InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
        EnterCriticalSection(&g_pool_lock);
        g_pool_submitted_tasks++;
        LeaveCriticalSection(&g_pool_lock);
#endif
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

int64_t rt_pool_submitted_count(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int64_t count = g_pool_submitted_tasks;
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int64_t count = g_pool_submitted_tasks;
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}

int64_t rt_pool_completed_count(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int64_t count = g_pool_completed_tasks;
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int64_t count = g_pool_completed_tasks;
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}

int64_t rt_pool_pending_count(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int64_t count = g_pool_pending_tasks;
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int64_t count = g_pool_pending_tasks;
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}

int64_t rt_pool_busy_count(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int64_t count = g_pool_busy_workers;
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int64_t count = g_pool_busy_workers;
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}

int64_t rt_pool_blocked_count(void) {
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&g_pool_lock);
    int64_t count = g_pool_blocked_workers;
    pthread_mutex_unlock(&g_pool_lock);
    return count;
#else
    InitOnceExecuteOnce(&g_pool_once, rt_pool_init_once, NULL, NULL);
    EnterCriticalSection(&g_pool_lock);
    int64_t count = g_pool_blocked_workers;
    LeaveCriticalSection(&g_pool_lock);
    return count;
#endif
}
