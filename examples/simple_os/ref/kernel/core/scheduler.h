/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/scheduler.h -- Priority-based round-robin scheduler
 *
 * Mirrors: spl/kernel/core/scheduler.spl
 *
 * 256 priority levels (0 = lowest, 255 = highest).  Threads at the same
 * priority are served in round-robin order.
 */

#ifndef SIMPLE_OS_SCHEDULER_H
#define SIMPLE_OS_SCHEDULER_H

#include "common/types.h"
#include "common/config.h"
#include "kernel/core/tcb.h"

/* ---- Constants --------------------------------------------------------- */

#define DEFAULT_TIME_SLICE  10   /* Ticks per quantum */
#define IDLE_THREAD_ID      0    /* Thread 0 is always idle */

/* ---- Per-priority ready queue ------------------------------------------ */

typedef struct {
    uint32_t head;       /* First TCB id, or TCB_NONE */
    uint32_t tail;       /* Last TCB id, or TCB_NONE */
    uint32_t count;
} ready_queue_t;

/* ---- Scheduler state --------------------------------------------------- */

typedef struct {
    ready_queue_t queues[NUM_PRIORITIES];
    uint32_t      current_thread;
    tcb_t         thread_pool[MAX_THREADS];
    uint32_t      thread_count;
    uint32_t      idle_thread_id;
    bool          need_reschedule;
    uint64_t      total_ticks;
} scheduler_t;

/* ---- API --------------------------------------------------------------- */

/* Initialize scheduler with idle thread at priority 0. */
void scheduler_init(scheduler_t *sched);

/* Register a thread in the pool. Returns its id. */
uint32_t scheduler_add_thread(scheduler_t *sched, const tcb_t *tcb);

/* Enqueue a thread into its priority-level ready queue. */
void scheduler_enqueue(scheduler_t *sched, uint32_t thread_id);

/* Dequeue a specific thread from its ready queue. */
void scheduler_dequeue(scheduler_t *sched, uint32_t thread_id);

/* Pick the highest-priority Ready thread. Returns true + *out_id. */
bool scheduler_pick_next(const scheduler_t *sched, uint32_t *out_id);

/* Core scheduling decision (context switch). */
void scheduler_schedule(scheduler_t *sched);

/* Timer tick handler. */
void scheduler_tick(scheduler_t *sched);

/* Voluntary yield. */
void scheduler_yield(scheduler_t *sched);

/* Block a thread with a given new state. */
void scheduler_block(scheduler_t *sched, uint32_t thread_id,
                     thread_state_t new_state);

/* Unblock a thread (set Ready, enqueue, check preemption). */
void scheduler_unblock(scheduler_t *sched, uint32_t thread_id);

/* Change a thread's priority (may trigger reschedule). */
void scheduler_set_priority(scheduler_t *sched, uint32_t thread_id,
                            uint32_t new_priority);

/* Get the current thread's TCB (read-only copy). */
tcb_t scheduler_current(const scheduler_t *sched);

/* Total ready count across all priorities. */
uint32_t scheduler_ready_count(const scheduler_t *sched);

#endif /* SIMPLE_OS_SCHEDULER_H */
