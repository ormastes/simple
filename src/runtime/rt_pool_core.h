/* rt_pool_core.h — lock-agnostic helpers shared by the two C task-pool lanes:
 *   runtime_pool.c   (Rust-seed simple-runtime lane)
 *   runtime_thread.c (core-C seed/simple lanes)
 *
 * Internal only: every definition is `static`, nothing is exported, and no
 * helper takes or releases a lock — the caller holds whatever its lane holds
 * (the queue helpers run under the lane's g_pool_lock).
 *
 * Include contract: include this AFTER the including file has defined
 *   - RtPoolTask with a `struct RtPoolTask* next` field (lanes keep their own
 *     task struct; runtime_pool.c also carries `state_next`),
 *   - RtPoolQueue with `RtPoolTask* head` and `RtPoolTask* tail`,
 *   - RT_POOL_MAX_WORKERS, g_pool_queues[], g_pool_worker_count,
 *     g_pool_configured_worker_count,
 *   - rt_pool_default_worker_count() (NOT shared: floor, cap and CPU source
 *     differ per lane).
 *
 * Deliberately NOT here: anything that locks internally (state_task_*,
 * pop_task, complete_task, mark_worker_*, compensation spawn), the handle
 * tables, and try_submit's counter ordering — those differ per lane. */
#ifndef RT_POOL_CORE_H
#define RT_POOL_CORE_H

#include <stddef.h>
#include <stdint.h>

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

/* Caller holds g_pool_lock. */
static int rt_pool_has_tasks_locked(void) {
    int count = g_pool_worker_count > 0 ? g_pool_worker_count : rt_pool_effective_worker_count();
    if (count > RT_POOL_MAX_WORKERS) count = RT_POOL_MAX_WORKERS;
    for (int i = 0; i < count; i++) {
        if (g_pool_queues[i].head != NULL) return 1;
    }
    return 0;
}

/* Intrusive FIFO; caller holds g_pool_lock. */
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

#endif /* RT_POOL_CORE_H */
