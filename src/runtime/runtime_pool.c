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
typedef int64_t (*rt_pool_scalar_closure_fn_t)(int64_t, int64_t);

#define RT_POOL_DIRECT_FUNCTION_MARKER INT64_C(0x5344495245435446)

typedef struct RtPoolState RtPoolState;

typedef struct RtPoolTask {
    rt_pool_closure_fn_t entry;
    int64_t closure_ptr;
    int64_t result;
    int done;
    int joined;
    int released;
    int state_owned;
    rt_pool_scalar_closure_fn_t scalar_entry;
    int64_t scalar_closure[2];
    int64_t scalar_input;
    int64_t public_handle;
    RtPoolState* state;
    struct RtPoolTask* state_next;
    struct RtPoolTask* next;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_t lock;
    pthread_cond_t done_cond;
#else
    CRITICAL_SECTION lock;
    CONDITION_VARIABLE done_cond;
#endif
} RtPoolTask;

static int64_t rt_pool_scalar_task_dispatch(int64_t raw_task) {
    RtPoolTask* task = (RtPoolTask*)(intptr_t)raw_task;
    if (task == NULL || task->scalar_entry == NULL) return 0;
    return task->scalar_entry((int64_t)(intptr_t)&task->scalar_closure[0], task->scalar_input);
}

struct RtPoolState {
    int64_t capacity;
    int64_t outstanding;
    int64_t pending;
    int64_t running;
    int64_t completed;
    int closed;
    int destroying;
    int64_t public_handle;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_t lock;
    pthread_cond_t changed;
#else
    CRITICAL_SECTION lock;
    CONDITION_VARIABLE changed;
#endif
};

/* Generation-stamped handles prevent stale/forged integers from becoming
 * process pointers. Slots are bounded and reused only after generation is
 * advanced. The Simple v1 facade is a single-caller manual-lifecycle pilot;
 * language-level unique ownership is not yet enforced. */
#define RT_POOL_STATE_SLOT_COUNT 1024
#define RT_POOL_TASK_SLOT_COUNT 65536
#define RT_POOL_STATE_MAX_CAPACITY 65534
#define RT_POOL_HANDLE_INDEX_BITS 16
#define RT_POOL_HANDLE_INDEX_MASK 0xffff
#define RT_POOL_HANDLE_KIND_SHIFT 47
#define RT_POOL_HANDLE_GENERATION_MASK 0x7fffffffU
#define RT_POOL_HANDLE_KIND_STATE 1U
#define RT_POOL_HANDLE_KIND_TASK 2U

typedef struct RtPoolStateSlot { RtPoolState* ptr; uint32_t generation; uint32_t refs; int closing; } RtPoolStateSlot;
typedef struct RtPoolTaskSlot { RtPoolTask* ptr; uint32_t generation; uint32_t refs; int closing; } RtPoolTaskSlot;
static RtPoolStateSlot g_pool_state_slots[RT_POOL_STATE_SLOT_COUNT];
static RtPoolTaskSlot g_pool_task_slots[RT_POOL_TASK_SLOT_COUNT];

#ifdef RT_POOL_PTHREAD
static pthread_mutex_t g_pool_handle_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t g_pool_handle_changed = PTHREAD_COND_INITIALIZER;
#define RT_POOL_HANDLE_LOCK() pthread_mutex_lock(&g_pool_handle_lock)
#define RT_POOL_HANDLE_UNLOCK() pthread_mutex_unlock(&g_pool_handle_lock)
#else
static CRITICAL_SECTION g_pool_handle_lock;
static CONDITION_VARIABLE g_pool_handle_changed;
static INIT_ONCE g_pool_handle_once = INIT_ONCE_STATIC_INIT;
static BOOL CALLBACK rt_pool_handle_init_once(PINIT_ONCE once, PVOID param, PVOID* context) {
    (void)once; (void)param; (void)context;
    InitializeCriticalSection(&g_pool_handle_lock);
    InitializeConditionVariable(&g_pool_handle_changed);
    return TRUE;
}
#define RT_POOL_HANDLE_LOCK() do { InitOnceExecuteOnce(&g_pool_handle_once, rt_pool_handle_init_once, NULL, NULL); EnterCriticalSection(&g_pool_handle_lock); } while (0)
#define RT_POOL_HANDLE_UNLOCK() LeaveCriticalSection(&g_pool_handle_lock)
#endif

static int64_t rt_pool_handle_encode(uint32_t kind, uint32_t generation, uint32_t index) {
    return ((int64_t)kind << RT_POOL_HANDLE_KIND_SHIFT)
        | ((int64_t)(generation & RT_POOL_HANDLE_GENERATION_MASK) << RT_POOL_HANDLE_INDEX_BITS)
        | (int64_t)index;
}

static uint32_t rt_pool_handle_index(int64_t handle) {
    return (uint32_t)(handle & RT_POOL_HANDLE_INDEX_MASK);
}

static uint32_t rt_pool_handle_generation(int64_t handle) {
    return (uint32_t)((((uint64_t)handle) >> RT_POOL_HANDLE_INDEX_BITS) & RT_POOL_HANDLE_GENERATION_MASK);
}

static uint32_t rt_pool_handle_kind(int64_t handle) {
    return (uint32_t)(((uint64_t)handle) >> RT_POOL_HANDLE_KIND_SHIFT);
}

static int64_t rt_pool_state_handle_alloc(RtPoolState* state) {
    int64_t handle = 0;
    RT_POOL_HANDLE_LOCK();
    for (uint32_t i = 1; i < RT_POOL_STATE_SLOT_COUNT; i++) {
        if (g_pool_state_slots[i].ptr == NULL) {
            uint32_t generation = (g_pool_state_slots[i].generation + 1) & RT_POOL_HANDLE_GENERATION_MASK;
            if (generation == 0) generation = 1;
            g_pool_state_slots[i].generation = generation;
            g_pool_state_slots[i].ptr = state;
            g_pool_state_slots[i].closing = 0;
            g_pool_state_slots[i].refs = 0;
            handle = rt_pool_handle_encode(RT_POOL_HANDLE_KIND_STATE, generation, i);
            break;
        }
    }
    RT_POOL_HANDLE_UNLOCK();
    return handle;
}

static RtPoolState* rt_pool_state_handle_get(int64_t handle) {
    uint32_t index = rt_pool_handle_index(handle);
    uint32_t generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_STATE || index == 0 || index >= RT_POOL_STATE_SLOT_COUNT || generation == 0) return NULL;
    RT_POOL_HANDLE_LOCK();
    RtPoolState* state = NULL;
    if (g_pool_state_slots[index].generation == generation && !g_pool_state_slots[index].closing) {
        state = g_pool_state_slots[index].ptr;
        if (state != NULL) g_pool_state_slots[index].refs++;
    }
    RT_POOL_HANDLE_UNLOCK();
    return state;
}

static void rt_pool_state_handle_put(int64_t handle) {
    uint32_t index = rt_pool_handle_index(handle);
    uint32_t generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_STATE || index == 0 || index >= RT_POOL_STATE_SLOT_COUNT) return;
    RT_POOL_HANDLE_LOCK();
    if (g_pool_state_slots[index].generation == generation && g_pool_state_slots[index].refs > 0) {
        g_pool_state_slots[index].refs--;
#ifdef RT_POOL_PTHREAD
        pthread_cond_broadcast(&g_pool_handle_changed);
#else
        WakeAllConditionVariable(&g_pool_handle_changed);
#endif
    }
    RT_POOL_HANDLE_UNLOCK();
}

static int rt_pool_state_handle_close_wait(int64_t handle, RtPoolState* state) {
    uint32_t index = rt_pool_handle_index(handle), generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_STATE || index == 0 || index >= RT_POOL_STATE_SLOT_COUNT) return 0;
    RT_POOL_HANDLE_LOCK();
    RtPoolStateSlot* slot = &g_pool_state_slots[index];
    if (slot->generation != generation || slot->ptr != state || slot->closing) { RT_POOL_HANDLE_UNLOCK(); return 0; }
    slot->closing = 1;
    if (slot->refs > 0) slot->refs--; /* destroy's acquire */
#ifdef RT_POOL_PTHREAD
    while (slot->refs > 0) pthread_cond_wait(&g_pool_handle_changed, &g_pool_handle_lock);
#else
    while (slot->refs > 0) SleepConditionVariableCS(&g_pool_handle_changed, &g_pool_handle_lock, INFINITE);
#endif
    slot->ptr = NULL;
    RT_POOL_HANDLE_UNLOCK();
    return 1;
}

static int64_t rt_pool_task_handle_alloc(RtPoolTask* task) {
    int64_t handle = 0;
    RT_POOL_HANDLE_LOCK();
    for (uint32_t i = 1; i < RT_POOL_TASK_SLOT_COUNT; i++) {
        if (g_pool_task_slots[i].ptr == NULL) {
            uint32_t generation = (g_pool_task_slots[i].generation + 1) & RT_POOL_HANDLE_GENERATION_MASK;
            if (generation == 0) generation = 1;
            g_pool_task_slots[i].generation = generation;
            g_pool_task_slots[i].ptr = task;
            g_pool_task_slots[i].closing = 0;
            g_pool_task_slots[i].refs = 0;
            handle = rt_pool_handle_encode(RT_POOL_HANDLE_KIND_TASK, generation, i);
            break;
        }
    }
    RT_POOL_HANDLE_UNLOCK();
    return handle;
}

static RtPoolTask* rt_pool_task_handle_get(int64_t handle) {
    uint32_t index = rt_pool_handle_index(handle);
    uint32_t generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_TASK || index == 0 || index >= RT_POOL_TASK_SLOT_COUNT || generation == 0) return NULL;
    RT_POOL_HANDLE_LOCK();
    RtPoolTask* task = NULL;
    if (g_pool_task_slots[index].generation == generation && !g_pool_task_slots[index].closing) {
        task = g_pool_task_slots[index].ptr;
        if (task != NULL) g_pool_task_slots[index].refs++;
    }
    RT_POOL_HANDLE_UNLOCK();
    return task;
}

static void rt_pool_task_handle_put(int64_t handle) {
    uint32_t index = rt_pool_handle_index(handle);
    uint32_t generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_TASK || index == 0 || index >= RT_POOL_TASK_SLOT_COUNT) return;
    RT_POOL_HANDLE_LOCK();
    if (g_pool_task_slots[index].generation == generation && g_pool_task_slots[index].refs > 0) {
        g_pool_task_slots[index].refs--;
#ifdef RT_POOL_PTHREAD
        pthread_cond_broadcast(&g_pool_handle_changed);
#else
        WakeAllConditionVariable(&g_pool_handle_changed);
#endif
    }
    RT_POOL_HANDLE_UNLOCK();
}

static int rt_pool_task_handle_close_wait(int64_t handle, RtPoolTask* task) {
    uint32_t index = rt_pool_handle_index(handle), generation = rt_pool_handle_generation(handle);
    if (rt_pool_handle_kind(handle) != RT_POOL_HANDLE_KIND_TASK || index == 0 || index >= RT_POOL_TASK_SLOT_COUNT) return 0;
    RT_POOL_HANDLE_LOCK();
    RtPoolTaskSlot* slot = &g_pool_task_slots[index];
    if (slot->generation != generation || slot->ptr != task || slot->closing) { RT_POOL_HANDLE_UNLOCK(); return 0; }
    slot->closing = 1;
    if (slot->refs > 0) slot->refs--; /* release's acquire */
#ifdef RT_POOL_PTHREAD
    while (slot->refs > 0) pthread_cond_wait(&g_pool_handle_changed, &g_pool_handle_lock);
#else
    while (slot->refs > 0) SleepConditionVariableCS(&g_pool_handle_changed, &g_pool_handle_lock, INFINITE);
#endif
    slot->ptr = NULL;
    RT_POOL_HANDLE_UNLOCK();
    return 1;
}

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

static void rt_pool_state_task_started(RtPoolTask* task) {
    RtPoolState* state = task != NULL ? task->state : NULL;
    if (state == NULL) return;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    if (state->pending > 0) state->pending--;
    state->running++;
    pthread_cond_broadcast(&state->changed);
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    if (state->pending > 0) state->pending--;
    state->running++;
    WakeAllConditionVariable(&state->changed);
    LeaveCriticalSection(&state->lock);
#endif
}

static void rt_pool_state_task_completed(RtPoolTask* task) {
    RtPoolState* state = task != NULL ? task->state : NULL;
    if (state == NULL) return;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    if (state->running > 0) state->running--;
    state->completed++;
    pthread_cond_broadcast(&state->changed);
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    if (state->running > 0) state->running--;
    state->completed++;
    WakeAllConditionVariable(&state->changed);
    LeaveCriticalSection(&state->lock);
#endif
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
    if (task != NULL) rt_pool_state_task_started(task);
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
    if (task != NULL) rt_pool_state_task_started(task);
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
    rt_pool_state_task_completed(task);
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
    rt_pool_state_task_completed(task);
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

static RtPoolTask* rt_pool_task_create(int64_t arg0, int64_t arg1) {
    int64_t closure_ptr = (arg1 != 0) ? arg1 : arg0;
    if (closure_ptr == 0) return NULL;
    rt_pool_closure_fn_t entry = *(rt_pool_closure_fn_t*)(intptr_t)closure_ptr;
    if (entry == NULL) return NULL;
    RtPoolTask* task = (RtPoolTask*)calloc(1, sizeof(RtPoolTask));
    if (task == NULL) return NULL;
    task->entry = entry;
    task->closure_ptr = closure_ptr;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_init(&task->lock, NULL);
    pthread_cond_init(&task->done_cond, NULL);
#else
    InitializeCriticalSection(&task->lock);
    InitializeConditionVariable(&task->done_cond);
#endif
    return task;
}

static RtPoolTask* rt_pool_scalar_task_create(int64_t function_value, int64_t input_i64) {
    if (function_value == 0) return NULL;
    const int64_t* descriptor = (const int64_t*)(intptr_t)function_value;
    if (descriptor[0] == 0 || descriptor[1] != RT_POOL_DIRECT_FUNCTION_MARKER) return NULL;
    RtPoolTask* task = (RtPoolTask*)calloc(1, sizeof(RtPoolTask));
    if (task == NULL) return NULL;
    task->scalar_entry = (rt_pool_scalar_closure_fn_t)(intptr_t)descriptor[0];
    task->scalar_closure[0] = descriptor[0];
    task->scalar_closure[1] = descriptor[1];
    task->scalar_input = input_i64;
    task->entry = rt_pool_scalar_task_dispatch;
    task->closure_ptr = (int64_t)(intptr_t)task;
    task->state_owned = 1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_init(&task->lock, NULL);
    pthread_cond_init(&task->done_cond, NULL);
#else
    InitializeCriticalSection(&task->lock);
    InitializeConditionVariable(&task->done_cond);
#endif
    return task;
}

static int64_t rt_pool_schedule_task(RtPoolTask* task) {
    if (task == NULL) return 0;
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
        if (task->state != NULL) rt_pool_state_task_started(task);
        rt_pool_complete_task(task, task->entry(task->closure_ptr));
        return (int64_t)(intptr_t)task;
    }
    rt_pool_push_task(task);
    return (int64_t)(intptr_t)task;
}

int64_t rt_pool_submit(int64_t arg0, int64_t arg1) {
    return rt_pool_schedule_task(rt_pool_task_create(arg0, arg1));
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
    if (task->state != NULL) task->joined = 1;
    pthread_mutex_unlock(&task->lock);
    if (task->state != NULL) return result;
    pthread_cond_destroy(&task->done_cond);
    pthread_mutex_destroy(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    while (!task->done) {
        SleepConditionVariableCS(&task->done_cond, &task->lock, INFINITE);
    }
    int64_t result = task->result;
    if (task->state != NULL) task->joined = 1;
    LeaveCriticalSection(&task->lock);
    if (task->state != NULL) return result;
    DeleteCriticalSection(&task->lock);
#endif
    free(task);
    return result;
}

int64_t rt_pool_state_create_v1(int64_t capacity) {
    if (capacity < 1 || capacity > RT_POOL_STATE_MAX_CAPACITY) return 0;
    RtPoolState* state = (RtPoolState*)calloc(1, sizeof(RtPoolState));
    if (state == NULL) return 0;
    state->capacity = capacity;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_init(&state->lock, NULL);
    pthread_cond_init(&state->changed, NULL);
#else
    InitializeCriticalSection(&state->lock);
    InitializeConditionVariable(&state->changed);
#endif
    int64_t handle = rt_pool_state_handle_alloc(state);
    if (handle == 0) {
#ifdef RT_POOL_PTHREAD
        pthread_cond_destroy(&state->changed);
        pthread_mutex_destroy(&state->lock);
#else
        DeleteCriticalSection(&state->lock);
#endif
        free(state);
        return 0;
    }
    state->public_handle = handle;
    return handle;
}

int64_t rt_pool_state_try_submit_i64_v1(int64_t state_handle, int64_t arg0, int64_t arg1) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return -3;
    RtPoolTask* task = rt_pool_scalar_task_create(arg0, arg1);
    if (task == NULL) { rt_pool_state_handle_put(state_handle); return -3; }
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    if (state->closed || state->destroying) {
        pthread_mutex_unlock(&state->lock);
        pthread_cond_destroy(&task->done_cond);
        pthread_mutex_destroy(&task->lock);
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -2;
    }
    if (state->outstanding >= state->capacity) {
        pthread_mutex_unlock(&state->lock);
        pthread_cond_destroy(&task->done_cond);
        pthread_mutex_destroy(&task->lock);
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -1;
    }
    task->state = state;
    state->outstanding++;
    state->pending++;
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    if (state->closed || state->destroying) {
        LeaveCriticalSection(&state->lock);
        DeleteCriticalSection(&task->lock);
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -2;
    }
    if (state->outstanding >= state->capacity) {
        LeaveCriticalSection(&state->lock);
        DeleteCriticalSection(&task->lock);
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -1;
    }
    task->state = state;
    state->outstanding++;
    state->pending++;
    LeaveCriticalSection(&state->lock);
#endif
    int64_t task_handle = rt_pool_task_handle_alloc(task);
    if (task_handle == 0) {
#ifdef RT_POOL_PTHREAD
        pthread_mutex_lock(&state->lock);
        state->outstanding--;
        state->pending--;
        pthread_mutex_unlock(&state->lock);
        pthread_cond_destroy(&task->done_cond);
        pthread_mutex_destroy(&task->lock);
#else
        EnterCriticalSection(&state->lock);
        state->outstanding--;
        state->pending--;
        LeaveCriticalSection(&state->lock);
        DeleteCriticalSection(&task->lock);
#endif
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -3;
    }
    task->public_handle = task_handle;
    if (rt_pool_schedule_task(task) == 0) {
        rt_pool_task_handle_close_wait(task_handle, task);
#ifdef RT_POOL_PTHREAD
        pthread_mutex_lock(&state->lock);
        state->outstanding--;
        state->pending--;
        pthread_mutex_unlock(&state->lock);
        pthread_cond_destroy(&task->done_cond);
        pthread_mutex_destroy(&task->lock);
#else
        EnterCriticalSection(&state->lock);
        state->outstanding--;
        state->pending--;
        LeaveCriticalSection(&state->lock);
        DeleteCriticalSection(&task->lock);
#endif
        free(task);
        rt_pool_state_handle_put(state_handle);
        return -3;
    }
    rt_pool_state_handle_put(state_handle);
    return task_handle;
}

int64_t rt_pool_task_status_i64_v1(int64_t task_handle) {
    RtPoolTask* task = rt_pool_task_handle_get(task_handle);
    if (task == NULL || task->state == NULL) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&task->lock);
    int status = task->released ? 3 : (task->joined ? 2 : (task->done ? 1 : 0));
    pthread_mutex_unlock(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    int status = task->released ? 3 : (task->joined ? 2 : (task->done ? 1 : 0));
    LeaveCriticalSection(&task->lock);
#endif
    rt_pool_task_handle_put(task_handle);
    return status;
}

int64_t rt_pool_task_join_i64_v1(int64_t task_handle) {
    RtPoolTask* task = rt_pool_task_handle_get(task_handle);
    if (task == NULL || task->state == NULL) return 0;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&task->lock);
    while (!task->done) pthread_cond_wait(&task->done_cond, &task->lock);
    task->joined = 1;
    int64_t result = task->result;
    pthread_mutex_unlock(&task->lock);
#else
    EnterCriticalSection(&task->lock);
    while (!task->done) SleepConditionVariableCS(&task->done_cond, &task->lock, INFINITE);
    task->joined = 1;
    int64_t result = task->result;
    LeaveCriticalSection(&task->lock);
#endif
    rt_pool_task_handle_put(task_handle);
    return result;
}

int64_t rt_pool_task_release_i64_v1(int64_t task_handle) {
    RtPoolTask* task = rt_pool_task_handle_get(task_handle);
    if (task == NULL || task->state == NULL) return -1;
    RtPoolState* state = task->state;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&task->lock);
    if (!task->done || task->released) {
        int result = task->released ? -2 : -3;
        pthread_mutex_unlock(&task->lock);
        rt_pool_task_handle_put(task_handle);
        return result;
    }
    task->released = 1;
    pthread_mutex_unlock(&task->lock);
    pthread_mutex_lock(&state->lock);
    if (state->outstanding > 0) state->outstanding--;
    pthread_cond_broadcast(&state->changed);
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&task->lock);
    if (!task->done || task->released) {
        int result = task->released ? -2 : -3;
        LeaveCriticalSection(&task->lock);
        rt_pool_task_handle_put(task_handle);
        return result;
    }
    task->released = 1;
    LeaveCriticalSection(&task->lock);
    EnterCriticalSection(&state->lock);
    if (state->outstanding > 0) state->outstanding--;
    WakeAllConditionVariable(&state->changed);
    LeaveCriticalSection(&state->lock);
#endif
    if (!rt_pool_task_handle_close_wait(task_handle, task)) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_cond_destroy(&task->done_cond);
    pthread_mutex_destroy(&task->lock);
#else
    DeleteCriticalSection(&task->lock);
#endif
    free(task);
    return 1;
}

int64_t rt_pool_state_close_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return 0;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    state->closed = 1;
    pthread_cond_broadcast(&state->changed);
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    state->closed = 1;
    WakeAllConditionVariable(&state->changed);
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return 1;
}

int64_t rt_pool_state_join_idle_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return 0;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    while (state->pending > 0 || state->running > 0) {
        pthread_cond_wait(&state->changed, &state->lock);
    }
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    while (state->pending > 0 || state->running > 0) {
        SleepConditionVariableCS(&state->changed, &state->lock, INFINITE);
    }
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return 1;
}

int64_t rt_pool_state_outstanding_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    int64_t value = state->outstanding;
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    int64_t value = state->outstanding;
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return value;
}

int64_t rt_pool_state_pending_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    int64_t value = state->pending;
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    int64_t value = state->pending;
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return value;
}

int64_t rt_pool_state_running_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    int64_t value = state->running;
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    int64_t value = state->running;
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return value;
}

int64_t rt_pool_state_completed_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return -1;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    int64_t value = state->completed;
    pthread_mutex_unlock(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    int64_t value = state->completed;
    LeaveCriticalSection(&state->lock);
#endif
    rt_pool_state_handle_put(state_handle);
    return value;
}

int64_t rt_pool_state_destroy_v1(int64_t state_handle) {
    RtPoolState* state = rt_pool_state_handle_get(state_handle);
    if (state == NULL) return 0;
#ifdef RT_POOL_PTHREAD
    pthread_mutex_lock(&state->lock);
    if (!state->closed || state->outstanding != 0 || state->pending != 0 || state->running != 0) {
        pthread_mutex_unlock(&state->lock);
        rt_pool_state_handle_put(state_handle);
        return 0;
    }
    state->destroying = 1;
    pthread_mutex_unlock(&state->lock);
    if (!rt_pool_state_handle_close_wait(state_handle, state)) return 0;
    pthread_cond_destroy(&state->changed);
    pthread_mutex_destroy(&state->lock);
#else
    EnterCriticalSection(&state->lock);
    if (!state->closed || state->outstanding != 0 || state->pending != 0 || state->running != 0) {
        LeaveCriticalSection(&state->lock);
        rt_pool_state_handle_put(state_handle);
        return 0;
    }
    state->destroying = 1;
    LeaveCriticalSection(&state->lock);
    if (!rt_pool_state_handle_close_wait(state_handle, state)) return 0;
    DeleteCriticalSection(&state->lock);
#endif
    free(state);
    return 1;
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
