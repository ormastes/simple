/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/endpoint.c -- L4 synchronous IPC endpoint implementation
 *
 * Mirrors: spl/kernel/core/endpoint.spl
 */

#include "kernel/core/endpoint.h"

/* ---- Queue helpers ----------------------------------------------------- */

static void ep_queue_init(ep_queue_t *q)
{
    q->head  = 0;
    q->tail  = 0;
    q->count = 0;
}

static bool ep_queue_is_empty(const ep_queue_t *q)
{
    return q->count == 0;
}

static bool ep_queue_push(ep_queue_t *q, uint32_t id)
{
    if (q->count >= EP_MAX_WAITERS) {
        return false;
    }
    q->entries[q->tail] = id;
    q->tail = (q->tail + 1) % EP_MAX_WAITERS;
    q->count++;
    return true;
}

static bool ep_queue_pop(ep_queue_t *q, uint32_t *out_id)
{
    if (q->count == 0) {
        return false;
    }
    *out_id = q->entries[q->head];
    q->head = (q->head + 1) % EP_MAX_WAITERS;
    q->count--;
    return true;
}

static void ep_queue_remove(ep_queue_t *q, uint32_t id)
{
    /* Rebuild the queue without the target id. */
    uint32_t new_count = 0;
    uint32_t tmp[EP_MAX_WAITERS];

    uint32_t idx = q->head;
    for (uint32_t i = 0; i < q->count; i++) {
        if (q->entries[idx] != id) {
            tmp[new_count++] = q->entries[idx];
        }
        idx = (idx + 1) % EP_MAX_WAITERS;
    }

    /* Copy back */
    for (uint32_t i = 0; i < new_count; i++) {
        q->entries[i] = tmp[i];
    }
    q->head  = 0;
    q->tail  = new_count;
    q->count = new_count;
}

static bool ep_queue_contains(const ep_queue_t *q, uint32_t id)
{
    uint32_t idx = q->head;
    for (uint32_t i = 0; i < q->count; i++) {
        if (q->entries[idx] == id) {
            return true;
        }
        idx = (idx + 1) % EP_MAX_WAITERS;
    }
    return false;
}

/* ---- Internal ---------------------------------------------------------- */

static void endpoint_update_state(endpoint_t *ep)
{
    bool has_senders   = !ep_queue_is_empty(&ep->sender_queue);
    bool has_receivers = !ep_queue_is_empty(&ep->receiver_queue);

    if (has_senders && !has_receivers) {
        ep->state = EP_STATE_SEND_BLOCKED;
    } else if (has_receivers && !has_senders) {
        ep->state = EP_STATE_RECV_BLOCKED;
    } else {
        ep->state = EP_STATE_IDLE;
    }
}

/* ---- API --------------------------------------------------------------- */

void endpoint_init(endpoint_t *ep)
{
    ep->state         = EP_STATE_IDLE;
    ep_queue_init(&ep->sender_queue);
    ep_queue_init(&ep->receiver_queue);
    ep->badge         = 0;
    ep->reply_to      = 0;
    ep->reply_pending = false;
}

/* ------------------------------------------------------------------------ */

bool endpoint_send(endpoint_t *ep, uint32_t sender_id, uint32_t msg_info,
                   uint32_t *receiver_id)
{
    (void)msg_info;  /* msg_info used by caller for buffer transfer */

    /* Check if a receiver is already waiting */
    if (!ep_queue_is_empty(&ep->receiver_queue)) {
        if (ep_queue_pop(&ep->receiver_queue, receiver_id)) {
            ep->reply_to      = sender_id;
            ep->reply_pending = true;
            endpoint_update_state(ep);
            return true;
        }
    }

    /* No receiver -- block the sender */
    ep_queue_push(&ep->sender_queue, sender_id);
    endpoint_update_state(ep);
    return false;
}

/* ------------------------------------------------------------------------ */

bool endpoint_recv(endpoint_t *ep, uint32_t receiver_id,
                   uint32_t *sender_id)
{
    /* Check if a sender is already waiting */
    if (!ep_queue_is_empty(&ep->sender_queue)) {
        if (ep_queue_pop(&ep->sender_queue, sender_id)) {
            ep->reply_to      = *sender_id;
            ep->reply_pending = true;
            endpoint_update_state(ep);
            return true;
        }
    }

    /* No sender -- block the receiver */
    ep_queue_push(&ep->receiver_queue, receiver_id);
    endpoint_update_state(ep);
    return false;
}

/* ------------------------------------------------------------------------ */

bool endpoint_reply(endpoint_t *ep, uint32_t replier_id, uint32_t msg_info,
                    uint32_t *caller_id)
{
    (void)replier_id;
    (void)msg_info;

    if (!ep->reply_pending) {
        return false;
    }

    *caller_id = ep->reply_to;

    /* Consume the reply capability */
    ep->reply_pending = false;
    ep->reply_to      = 0;
    return true;
}

/* ------------------------------------------------------------------------ */

void endpoint_cancel(endpoint_t *ep, uint32_t thread_id)
{
    if (ep_queue_contains(&ep->sender_queue, thread_id)) {
        ep_queue_remove(&ep->sender_queue, thread_id);
    }
    if (ep_queue_contains(&ep->receiver_queue, thread_id)) {
        ep_queue_remove(&ep->receiver_queue, thread_id);
    }
    endpoint_update_state(ep);
}

/* ------------------------------------------------------------------------ */

bool endpoint_is_idle(const endpoint_t *ep)
{
    return ep->state == EP_STATE_IDLE;
}

/* ------------------------------------------------------------------------ */

bool endpoint_has_waiters(const endpoint_t *ep)
{
    return !ep_queue_is_empty(&ep->sender_queue) ||
           !ep_queue_is_empty(&ep->receiver_queue);
}

/* ------------------------------------------------------------------------ */

uint32_t endpoint_sender_count(const endpoint_t *ep)
{
    return ep->sender_queue.count;
}

/* ------------------------------------------------------------------------ */

uint32_t endpoint_receiver_count(const endpoint_t *ep)
{
    return ep->receiver_queue.count;
}

/* ------------------------------------------------------------------------ */

void endpoint_set_badge(endpoint_t *ep, uint32_t badge)
{
    ep->badge = badge;
}

/* ------------------------------------------------------------------------ */

uint32_t endpoint_get_badge(const endpoint_t *ep)
{
    return ep->badge;
}
