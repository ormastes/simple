/*
 * SimpleOS -- L4 Microkernel Reference Implementation
 * kernel/core/sched_context.c -- MCS scheduling context implementation
 *
 * Mirrors: spl/kernel/core/sched_context.spl
 */

#include "kernel/core/sched_context.h"

/* ------------------------------------------------------------------------ */

void sched_context_init(sched_context_t *sc, uint32_t id,
                        uint64_t budget, uint64_t period)
{
    uint64_t actual_period = period;
    if (actual_period < budget) {
        actual_period = budget;
    }

    sc->id             = id;
    sc->budget         = budget;
    sc->period         = actual_period;
    sc->remaining      = budget;
    sc->next_replenish = actual_period;
    sc->is_active      = true;
    sc->bound_tcb      = SC_UNBOUND;
}

/* ------------------------------------------------------------------------ */

void sched_context_init_default(sched_context_t *sc, uint32_t id)
{
    sched_context_init(sc, id, DEFAULT_SC_BUDGET, DEFAULT_SC_PERIOD);
}

/* ------------------------------------------------------------------------ */

void sched_context_configure(sched_context_t *sc, uint64_t budget,
                             uint64_t period)
{
    uint64_t actual_period = period;
    if (actual_period < budget) {
        actual_period = budget;
    }
    sc->budget = budget;
    sc->period = actual_period;

    /* Clamp remaining to new budget */
    if (sc->remaining > budget) {
        sc->remaining = budget;
    }
}

/* ------------------------------------------------------------------------ */

bool sched_context_charge(sched_context_t *sc, uint64_t ticks)
{
    if (!sc->is_active) {
        return false;
    }

    if (ticks >= sc->remaining) {
        sc->remaining = 0;
        return false;
    }

    sc->remaining -= ticks;
    return true;
}

/* ------------------------------------------------------------------------ */

void sched_context_refill(sched_context_t *sc, uint64_t current_tick)
{
    if (!sc->is_active) {
        return;
    }

    if (current_tick >= sc->next_replenish) {
        sc->remaining      = sc->budget;
        sc->next_replenish = current_tick + sc->period;
    }
}

/* ------------------------------------------------------------------------ */

void sched_context_bind(sched_context_t *sc, uint32_t tcb_id)
{
    sc->bound_tcb = tcb_id;
}

/* ------------------------------------------------------------------------ */

void sched_context_unbind(sched_context_t *sc)
{
    sc->bound_tcb = SC_UNBOUND;
}

/* ------------------------------------------------------------------------ */

bool sched_context_is_active(const sched_context_t *sc)
{
    return sc->is_active;
}

/* ------------------------------------------------------------------------ */

bool sched_context_is_runnable(const sched_context_t *sc)
{
    return sc->is_active && sc->remaining > 0;
}

/* ------------------------------------------------------------------------ */

bool sched_context_is_bound(const sched_context_t *sc)
{
    return sc->bound_tcb != SC_UNBOUND;
}

/* ------------------------------------------------------------------------ */

void sched_context_deactivate(sched_context_t *sc)
{
    sc->is_active = false;
    sc->remaining = 0;
}

/* ------------------------------------------------------------------------ */

void sched_context_activate(sched_context_t *sc, uint64_t current_tick)
{
    sc->is_active      = true;
    sc->remaining      = sc->budget;
    sc->next_replenish = current_tick + sc->period;
}

/* ------------------------------------------------------------------------ */

void sched_context_pool_init(sched_context_pool_t *pool)
{
    pool->count = 0;
    for (uint32_t i = 0; i < MAX_SCHED_CONTEXTS; i++) {
        pool->contexts[i].id             = 0;
        pool->contexts[i].budget         = 0;
        pool->contexts[i].period         = 0;
        pool->contexts[i].remaining      = 0;
        pool->contexts[i].next_replenish = 0;
        pool->contexts[i].is_active      = false;
        pool->contexts[i].bound_tcb      = SC_UNBOUND;
    }
}

/* ------------------------------------------------------------------------ */

bool sched_context_pool_alloc(sched_context_pool_t *pool,
                              uint64_t budget, uint64_t period,
                              uint32_t *out_idx)
{
    if (pool->count >= MAX_SCHED_CONTEXTS) {
        return false;
    }

    uint32_t id = pool->count;
    sched_context_init(&pool->contexts[id], id, budget, period);
    pool->count++;
    *out_idx = id;
    return true;
}

/* ------------------------------------------------------------------------ */

bool sched_context_pool_get(const sched_context_pool_t *pool,
                            uint32_t index, sched_context_t *out)
{
    if (index >= pool->count) {
        return false;
    }
    if (!pool->contexts[index].is_active) {
        return false;
    }
    *out = pool->contexts[index];
    return true;
}

/* ------------------------------------------------------------------------ */

uint32_t sched_context_pool_replenish_all(sched_context_pool_t *pool,
                                          uint64_t current_tick)
{
    uint32_t count = 0;
    for (uint32_t i = 0; i < pool->count; i++) {
        if (pool->contexts[i].is_active &&
            current_tick >= pool->contexts[i].next_replenish) {
            sched_context_refill(&pool->contexts[i], current_tick);
            count++;
        }
    }
    return count;
}
