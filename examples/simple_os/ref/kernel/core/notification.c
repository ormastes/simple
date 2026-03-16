/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/notification.c -- Asynchronous notification implementation
 *
 * Mirrors: spl/kernel/core/notification.spl
 */

#include "kernel/core/notification.h"

/* ---- Queue helpers ----------------------------------------------------- */

static void nq_init(notif_queue_t *q)
{
    q->head  = 0;
    q->tail  = 0;
    q->count = 0;
}

static bool nq_is_empty(const notif_queue_t *q)
{
    return q->count == 0;
}

static bool nq_push(notif_queue_t *q, uint32_t id)
{
    if (q->count >= NOTIF_MAX_WAITERS) {
        return false;
    }
    q->entries[q->tail] = id;
    q->tail = (q->tail + 1) % NOTIF_MAX_WAITERS;
    q->count++;
    return true;
}

static bool nq_pop(notif_queue_t *q, uint32_t *out_id)
{
    if (q->count == 0) {
        return false;
    }
    *out_id = q->entries[q->head];
    q->head = (q->head + 1) % NOTIF_MAX_WAITERS;
    q->count--;
    return true;
}

static bool nq_contains(const notif_queue_t *q, uint32_t id)
{
    uint32_t idx = q->head;
    for (uint32_t i = 0; i < q->count; i++) {
        if (q->entries[idx] == id) {
            return true;
        }
        idx = (idx + 1) % NOTIF_MAX_WAITERS;
    }
    return false;
}

static void nq_remove(notif_queue_t *q, uint32_t id)
{
    uint32_t new_count = 0;
    uint32_t tmp[NOTIF_MAX_WAITERS];

    uint32_t idx = q->head;
    for (uint32_t i = 0; i < q->count; i++) {
        if (q->entries[idx] != id) {
            tmp[new_count++] = q->entries[idx];
        }
        idx = (idx + 1) % NOTIF_MAX_WAITERS;
    }

    for (uint32_t i = 0; i < new_count; i++) {
        q->entries[i] = tmp[i];
    }
    q->head  = 0;
    q->tail  = new_count;
    q->count = new_count;
}

/* ---- API --------------------------------------------------------------- */

void notification_init(notification_t *notif)
{
    notif->word      = 0;
    notif->is_idle   = true;
    nq_init(&notif->wait_queue);
    notif->bound_tcb = 0;
    notif->is_bound  = false;
}

/* ------------------------------------------------------------------------ */

bool notification_signal(notification_t *notif, uint32_t bits,
                         uint32_t *woken_id)
{
    /* Accumulate signal bits */
    notif->word |= bits;

    /* If a thread is waiting, wake it immediately */
    if (!nq_is_empty(&notif->wait_queue)) {
        if (nq_pop(&notif->wait_queue, woken_id)) {
            /* Waiter consumes the entire word */
            notif->word = 0;
            if (nq_is_empty(&notif->wait_queue)) {
                notif->is_idle = true;
            }
            return true;
        }
    }

    return false;
}

/* ------------------------------------------------------------------------ */

bool notification_wait(notification_t *notif, uint32_t thread_id,
                       uint32_t *consumed)
{
    /* Fast path: word is non-zero -- consume immediately */
    if (notif->word != 0) {
        *consumed = notif->word;
        notif->word = 0;
        return true;
    }

    /* Slow path: block the thread */
    nq_push(&notif->wait_queue, thread_id);
    notif->is_idle = false;
    return false;
}

/* ------------------------------------------------------------------------ */

bool notification_poll(notification_t *notif, uint32_t *consumed)
{
    if (notif->word == 0) {
        return false;
    }
    *consumed = notif->word;
    notif->word = 0;
    return true;
}

/* ------------------------------------------------------------------------ */

bool notification_bind(notification_t *notif, uint32_t tcb_id)
{
    if (notif->is_bound) {
        return false;
    }
    notif->bound_tcb = tcb_id;
    notif->is_bound  = true;
    return true;
}

/* ------------------------------------------------------------------------ */

bool notification_unbind(notification_t *notif)
{
    if (!notif->is_bound) {
        return false;
    }
    notif->bound_tcb = 0;
    notif->is_bound  = false;
    return true;
}

/* ------------------------------------------------------------------------ */

void notification_cancel(notification_t *notif, uint32_t thread_id)
{
    if (nq_contains(&notif->wait_queue, thread_id)) {
        nq_remove(&notif->wait_queue, thread_id);
    }
    if (nq_is_empty(&notif->wait_queue)) {
        notif->is_idle = true;
    }
}

/* ------------------------------------------------------------------------ */

bool notification_is_bound(const notification_t *notif)
{
    return notif->is_bound;
}

/* ------------------------------------------------------------------------ */

uint32_t notification_get_bound_tcb(const notification_t *notif)
{
    if (notif->is_bound) {
        return notif->bound_tcb;
    }
    return 0;
}

/* ------------------------------------------------------------------------ */

bool notification_has_signal(const notification_t *notif)
{
    return notif->word != 0;
}

/* ------------------------------------------------------------------------ */

uint32_t notification_peek(const notification_t *notif)
{
    return notif->word;
}

/* ------------------------------------------------------------------------ */

uint32_t notification_waiter_count(const notification_t *notif)
{
    return notif->wait_queue.count;
}
