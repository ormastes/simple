/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/sched_context.h -- MCS scheduling context
 *
 * Mirrors: spl/kernel/core/sched_context.spl
 *
 * Each SchedContext represents a "right to execute for B ticks every P ticks".
 * Threads must be bound to a SchedContext to be schedulable.
 */

#ifndef SIMPLE_OS_SCHED_CONTEXT_H
#define SIMPLE_OS_SCHED_CONTEXT_H

#include "common/types.h"

/* ---- Constants --------------------------------------------------------- */

#define MAX_SCHED_CONTEXTS    128
#define DEFAULT_SC_BUDGET     100
#define DEFAULT_SC_PERIOD     1000
#define SC_UNBOUND            0xFFFFFFFF

/* ---- Scheduling Context ------------------------------------------------ */

typedef struct {
    uint32_t id;
    uint64_t budget;           /* Time budget per period (in ticks) */
    uint64_t period;           /* Replenishment period (in ticks) */
    uint64_t remaining;        /* Remaining budget in current period */
    uint64_t next_replenish;   /* Absolute tick for next replenishment */
    bool     is_active;
    uint32_t bound_tcb;        /* ID of bound thread, or SC_UNBOUND */
} sched_context_t;

/* ---- Pool -------------------------------------------------------------- */

typedef struct {
    sched_context_t contexts[MAX_SCHED_CONTEXTS];
    uint32_t        count;
} sched_context_pool_t;

/* ---- API --------------------------------------------------------------- */

/* Create a scheduling context with given budget and period. */
void sched_context_init(sched_context_t *sc, uint32_t id,
                        uint64_t budget, uint64_t period);

/* Create with default budget/period. */
void sched_context_init_default(sched_context_t *sc, uint32_t id);

/* Update budget and period; clamp remaining to new budget. */
void sched_context_configure(sched_context_t *sc, uint64_t budget,
                             uint64_t period);

/* Consume ticks.  Returns true if budget still positive. */
bool sched_context_charge(sched_context_t *sc, uint64_t ticks);

/* Replenish if the replenishment point has been reached. */
void sched_context_refill(sched_context_t *sc, uint64_t current_tick);

/* Bind / unbind threads. */
void sched_context_bind(sched_context_t *sc, uint32_t tcb_id);
void sched_context_unbind(sched_context_t *sc);

/* Query */
bool sched_context_is_active(const sched_context_t *sc);
bool sched_context_is_runnable(const sched_context_t *sc);
bool sched_context_is_bound(const sched_context_t *sc);

/* Activate / deactivate */
void sched_context_deactivate(sched_context_t *sc);
void sched_context_activate(sched_context_t *sc, uint64_t current_tick);

/* Pool operations */
void sched_context_pool_init(sched_context_pool_t *pool);
bool sched_context_pool_alloc(sched_context_pool_t *pool,
                              uint64_t budget, uint64_t period,
                              uint32_t *out_idx);
bool sched_context_pool_get(const sched_context_pool_t *pool,
                            uint32_t index, sched_context_t *out);
uint32_t sched_context_pool_replenish_all(sched_context_pool_t *pool,
                                          uint64_t current_tick);

#endif /* SIMPLE_OS_SCHED_CONTEXT_H */
