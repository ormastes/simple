/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/endpoint.h -- L4 synchronous IPC endpoints
 *
 * Mirrors: spl/kernel/core/endpoint.spl
 *
 * An endpoint is a kernel object through which threads perform synchronous
 * message passing.  When a sender calls endpoint_send and no receiver is
 * waiting, the sender blocks.  Conversely for endpoint_recv.
 */

#ifndef SIMPLE_OS_ENDPOINT_H
#define SIMPLE_OS_ENDPOINT_H

#include "common/types.h"
#include "common/config.h"

/* ---- Endpoint states --------------------------------------------------- */

typedef enum {
    EP_STATE_IDLE         = 0,   /* No threads waiting on either side */
    EP_STATE_SEND_BLOCKED = 1,   /* Senders waiting for a receiver */
    EP_STATE_RECV_BLOCKED = 2,   /* Receivers waiting for a sender */
} endpoint_state_t;

/* ---- Constants --------------------------------------------------------- */

#define EP_MAX_WAITERS  64

/* ---- Wait queue (simple index-based linked list) ----------------------- */

typedef struct {
    uint32_t entries[EP_MAX_WAITERS];
    uint32_t head;
    uint32_t tail;
    uint32_t count;
} ep_queue_t;

/* ---- Endpoint ---------------------------------------------------------- */

typedef struct {
    endpoint_state_t state;
    ep_queue_t       sender_queue;
    ep_queue_t       receiver_queue;
    uint32_t         badge;
    uint32_t         reply_to;       /* TCB id awaiting reply (0 = none) */
    bool             reply_pending;
} endpoint_t;

/* ---- API --------------------------------------------------------------- */

/* Initialize an endpoint in the Idle state. */
void endpoint_init(endpoint_t *ep);

/* Synchronous send.  If a receiver is waiting, returns true and sets
 * *receiver_id.  Otherwise the sender is enqueued and returns false. */
bool endpoint_send(endpoint_t *ep, uint32_t sender_id, uint32_t msg_info,
                   uint32_t *receiver_id);

/* Synchronous receive.  If a sender is waiting, returns true and sets
 * *sender_id.  Otherwise the receiver is enqueued and returns false. */
bool endpoint_recv(endpoint_t *ep, uint32_t receiver_id,
                   uint32_t *sender_id);

/* One-shot reply.  Returns true and sets *caller_id on success. */
bool endpoint_reply(endpoint_t *ep, uint32_t replier_id, uint32_t msg_info,
                    uint32_t *caller_id);

/* Cancel a thread's wait on this endpoint. */
void endpoint_cancel(endpoint_t *ep, uint32_t thread_id);

/* Query */
bool endpoint_is_idle(const endpoint_t *ep);
bool endpoint_has_waiters(const endpoint_t *ep);
uint32_t endpoint_sender_count(const endpoint_t *ep);
uint32_t endpoint_receiver_count(const endpoint_t *ep);
void endpoint_set_badge(endpoint_t *ep, uint32_t badge);
uint32_t endpoint_get_badge(const endpoint_t *ep);

#endif /* SIMPLE_OS_ENDPOINT_H */
