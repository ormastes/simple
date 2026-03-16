/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/notification.h -- Asynchronous notification objects
 *
 * Mirrors: spl/kernel/core/notification.spl
 *
 * A notification is a lightweight signaling mechanism based on a bitmap word.
 * Signaling never blocks the signaler; only the waiter blocks if the word
 * is zero.
 */

#ifndef SIMPLE_OS_NOTIFICATION_H
#define SIMPLE_OS_NOTIFICATION_H

#include "common/types.h"
#include "common/config.h"

/* ---- Constants --------------------------------------------------------- */

#define NOTIF_MAX_WAITERS  64

/* ---- Wait queue (ring buffer) ------------------------------------------ */

typedef struct {
    uint32_t entries[NOTIF_MAX_WAITERS];
    uint32_t head;
    uint32_t tail;
    uint32_t count;
} notif_queue_t;

/* ---- Notification ------------------------------------------------------ */

typedef struct {
    uint32_t      word;          /* Bitmap of accumulated signal bits */
    bool          is_idle;       /* true if no threads waiting */
    notif_queue_t wait_queue;    /* Threads blocked waiting for signal */
    uint32_t      bound_tcb;    /* TCB id of bound thread (0 = none) */
    bool          is_bound;
} notification_t;

/* ---- API --------------------------------------------------------------- */

/* Initialize a notification with empty word and no waiters. */
void notification_init(notification_t *notif);

/* Signal by OR-ing bits into the word.  If a waiter is present, returns
 * true and sets *woken_id.  The waiter consumes the entire word. */
bool notification_signal(notification_t *notif, uint32_t bits,
                         uint32_t *woken_id);

/* Wait on a notification.  If word is non-zero, returns true and sets
 * *consumed.  Otherwise the caller is enqueued and returns false. */
bool notification_wait(notification_t *notif, uint32_t thread_id,
                       uint32_t *consumed);

/* Non-blocking poll.  Returns true and sets *consumed if word != 0. */
bool notification_poll(notification_t *notif, uint32_t *consumed);

/* Bind a thread to this notification.  Returns false if already bound. */
bool notification_bind(notification_t *notif, uint32_t tcb_id);

/* Unbind the currently bound thread.  Returns false if not bound. */
bool notification_unbind(notification_t *notif);

/* Cancel a thread's wait. */
void notification_cancel(notification_t *notif, uint32_t thread_id);

/* Query helpers */
bool     notification_is_bound(const notification_t *notif);
uint32_t notification_get_bound_tcb(const notification_t *notif);
bool     notification_has_signal(const notification_t *notif);
uint32_t notification_peek(const notification_t *notif);
uint32_t notification_waiter_count(const notification_t *notif);

#endif /* SIMPLE_OS_NOTIFICATION_H */
