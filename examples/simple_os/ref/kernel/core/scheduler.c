/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/scheduler.c -- Priority-based round-robin scheduler
 *
 * Mirrors: spl/kernel/core/scheduler.spl
 */

#include "kernel/core/scheduler.h"

/* ------------------------------------------------------------------------ */

void scheduler_init(scheduler_t *sched)
{
    /* Initialize all ready queues */
    for (uint32_t p = 0; p < NUM_PRIORITIES; p++) {
        sched->queues[p].head  = TCB_NONE;
        sched->queues[p].tail  = TCB_NONE;
        sched->queues[p].count = 0;
    }

    /* Initialize all TCBs to default */
    for (uint32_t i = 0; i < MAX_THREADS; i++) {
        tcb_init(&sched->thread_pool[i], 0, 0);
    }

    /* Create the idle thread at priority 0 */
    tcb_init(&sched->thread_pool[IDLE_THREAD_ID], IDLE_THREAD_ID, 0);
    sched->thread_pool[IDLE_THREAD_ID].state      = THREAD_STATE_READY;
    sched->thread_pool[IDLE_THREAD_ID].time_slice  = DEFAULT_TIME_SLICE;
    sched->thread_pool[IDLE_THREAD_ID].name[0]     = 'i';
    sched->thread_pool[IDLE_THREAD_ID].name[1]     = 'd';
    sched->thread_pool[IDLE_THREAD_ID].name[2]     = 'l';
    sched->thread_pool[IDLE_THREAD_ID].name[3]     = 'e';
    sched->thread_pool[IDLE_THREAD_ID].name[4]     = '\0';

    sched->current_thread  = IDLE_THREAD_ID;
    sched->thread_count    = 1;
    sched->idle_thread_id  = IDLE_THREAD_ID;
    sched->need_reschedule = false;
    sched->total_ticks     = 0;
}

/* ------------------------------------------------------------------------ */

uint32_t scheduler_add_thread(scheduler_t *sched, const tcb_t *tcb)
{
    uint32_t id = tcb->id;
    if (id >= MAX_THREADS) {
        return TCB_NONE;
    }
    sched->thread_pool[id] = *tcb;
    if (id >= sched->thread_count) {
        sched->thread_count = id + 1;
    }
    return id;
}

/* ------------------------------------------------------------------------ */

void scheduler_enqueue(scheduler_t *sched, uint32_t thread_id)
{
    if (thread_id >= MAX_THREADS) {
        return;
    }

    sched->thread_pool[thread_id].state      = THREAD_STATE_READY;
    sched->thread_pool[thread_id].time_slice  = DEFAULT_TIME_SLICE;

    uint32_t prio = sched->thread_pool[thread_id].priority;
    uint32_t tail = sched->queues[prio].tail;

    /* Link at the tail of the queue */
    sched->thread_pool[thread_id].queue_prev = tail;
    sched->thread_pool[thread_id].queue_next = TCB_NONE;

    if (tail != TCB_NONE) {
        sched->thread_pool[tail].queue_next = thread_id;
    } else {
        /* Queue was empty */
        sched->queues[prio].head = thread_id;
    }

    sched->queues[prio].tail = thread_id;
    sched->queues[prio].count++;
}

/* ------------------------------------------------------------------------ */

void scheduler_dequeue(scheduler_t *sched, uint32_t thread_id)
{
    if (thread_id >= MAX_THREADS) {
        return;
    }

    uint32_t prio = sched->thread_pool[thread_id].priority;
    if (sched->queues[prio].count == 0) {
        return;
    }

    uint32_t prev = sched->thread_pool[thread_id].queue_prev;
    uint32_t next = sched->thread_pool[thread_id].queue_next;

    /* Patch previous node or update head */
    if (prev != TCB_NONE) {
        sched->thread_pool[prev].queue_next = next;
    } else {
        sched->queues[prio].head = next;
    }

    /* Patch next node or update tail */
    if (next != TCB_NONE) {
        sched->thread_pool[next].queue_prev = prev;
    } else {
        sched->queues[prio].tail = prev;
    }

    sched->thread_pool[thread_id].queue_next = TCB_NONE;
    sched->thread_pool[thread_id].queue_prev = TCB_NONE;
    sched->queues[prio].count--;
}

/* ------------------------------------------------------------------------ */

bool scheduler_pick_next(const scheduler_t *sched, uint32_t *out_id)
{
    /* Scan from highest to lowest priority */
    for (uint32_t p = NUM_PRIORITIES; p > 0; ) {
        p--;
        if (sched->queues[p].count > 0) {
            *out_id = sched->queues[p].head;
            return true;
        }
    }
    /* Fallback to idle thread */
    *out_id = sched->idle_thread_id;
    return true;
}

/* ------------------------------------------------------------------------ */

void scheduler_schedule(scheduler_t *sched)
{
    sched->need_reschedule = false;

    uint32_t next_id;
    if (!scheduler_pick_next(sched, &next_id)) {
        return;
    }

    uint32_t cur = sched->current_thread;

    /* Same thread stays -- nothing to do */
    if (next_id == cur) {
        sched->thread_pool[cur].state = THREAD_STATE_RUNNING;
        return;
    }

    /* Context switch out: move current back to Ready if still runnable */
    if (sched->thread_pool[cur].state == THREAD_STATE_RUNNING) {
        sched->thread_pool[cur].state = THREAD_STATE_READY;
        scheduler_enqueue(sched, cur);
    }

    /* Context switch in */
    scheduler_dequeue(sched, next_id);
    sched->thread_pool[next_id].state = THREAD_STATE_RUNNING;
    sched->current_thread = next_id;
}

/* ------------------------------------------------------------------------ */

void scheduler_tick(scheduler_t *sched)
{
    sched->total_ticks++;

    uint32_t cur = sched->current_thread;
    if (cur >= MAX_THREADS) {
        return;
    }

    if (sched->thread_pool[cur].time_slice > 0) {
        sched->thread_pool[cur].time_slice--;
    }

    if (sched->thread_pool[cur].time_slice == 0) {
        sched->need_reschedule = true;
    }
}

/* ------------------------------------------------------------------------ */

void scheduler_yield(scheduler_t *sched)
{
    uint32_t cur = sched->current_thread;
    if (cur >= MAX_THREADS) {
        return;
    }

    sched->thread_pool[cur].time_slice = 0;
    sched->need_reschedule = true;
}

/* ------------------------------------------------------------------------ */

void scheduler_block(scheduler_t *sched, uint32_t thread_id,
                     thread_state_t new_state)
{
    if (thread_id >= MAX_THREADS) {
        return;
    }

    if (thread_id == sched->current_thread) {
        sched->need_reschedule = true;
    } else {
        scheduler_dequeue(sched, thread_id);
    }

    sched->thread_pool[thread_id].state = new_state;
}

/* ------------------------------------------------------------------------ */

void scheduler_unblock(scheduler_t *sched, uint32_t thread_id)
{
    if (thread_id >= MAX_THREADS) {
        return;
    }

    sched->thread_pool[thread_id].state = THREAD_STATE_READY;
    scheduler_enqueue(sched, thread_id);

    /* Check if preemption is needed */
    uint32_t cur = sched->current_thread;
    if (sched->thread_pool[thread_id].priority >
        sched->thread_pool[cur].priority) {
        sched->need_reschedule = true;
    }
}

/* ------------------------------------------------------------------------ */

void scheduler_set_priority(scheduler_t *sched, uint32_t thread_id,
                            uint32_t new_priority)
{
    if (thread_id >= MAX_THREADS) {
        return;
    }

    uint32_t prio = new_priority;
    if (prio > MAX_PRIORITY) {
        prio = MAX_PRIORITY;
    }

    uint32_t old_prio = sched->thread_pool[thread_id].priority;
    if (prio == old_prio) {
        return;
    }

    bool is_ready =
        sched->thread_pool[thread_id].state == THREAD_STATE_READY;
    if (is_ready) {
        scheduler_dequeue(sched, thread_id);
    }

    sched->thread_pool[thread_id].priority = prio;

    if (is_ready) {
        scheduler_enqueue(sched, thread_id);
    }

    /* Higher-priority thread may preempt current */
    if (prio > sched->thread_pool[sched->current_thread].priority) {
        sched->need_reschedule = true;
    }
}

/* ------------------------------------------------------------------------ */

tcb_t scheduler_current(const scheduler_t *sched)
{
    return sched->thread_pool[sched->current_thread];
}

/* ------------------------------------------------------------------------ */

uint32_t scheduler_ready_count(const scheduler_t *sched)
{
    uint32_t total = 0;
    for (uint32_t p = 0; p < NUM_PRIORITIES; p++) {
        total += sched->queues[p].count;
    }
    return total;
}
