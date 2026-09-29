/* Independent frozen oracle: this is the pre-migration C storage policy. */
#include "cosmos_hal.h"
#include "cosmos_storage_policy_oracle.h"

#define COSMOS_STORAGE_ORACLE_GC_POLL_MASK 0xFFFFFU

static int oracle_acquire(
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts,
    enum cosmos_storage_oracle_action action) {
    counts->calls[action]++;
    return script->status[action];
}

void cosmos_storage_oracle_state_reset(
    struct cosmos_storage_oracle_state *state) {
    state->prepared = 0U;
    state->ready = 0U;
    state->gc_polls = 0U;
}

void cosmos_storage_oracle_counts_reset(
    struct cosmos_storage_oracle_counts *counts) {
    unsigned int action;

    for (action = 0U; action < COSMOS_STORAGE_ORACLE_ACTION_COUNT;
         action++) {
        counts->calls[action] = 0U;
    }
}

int cosmos_storage_oracle_init(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts) {
    int status;

    if (script->is_qemu) {
        return COSMOS_UNAVAILABLE;
    }
    state->prepared = 0U;
    state->ready = 0U;
    status = oracle_acquire(
        script, counts, COSMOS_STORAGE_ORACLE_BACKEND_INIT);
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_FTL_INIT);
    }
    if (status == COSMOS_OK) {
        state->prepared = 1U;
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_BACKEND_MOUNT);
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_FTL_RECOVER);
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_MEDIA_INIT);
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_IO_INIT);
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_ADMIN_INIT);
    }
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_DISPATCH_INIT);
    }
    if (status == COSMOS_OK) {
        state->gc_polls = 0U;
        state->ready = 1U;
    }
    return status;
}

int cosmos_storage_oracle_factory_initialize_erased(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts) {
    int status;

    if (script->is_qemu) {
        return COSMOS_UNAVAILABLE;
    }
    if (state->prepared == 0U || state->ready != 0U) {
        return COSMOS_INVALID;
    }
    status = oracle_acquire(
        script, counts, COSMOS_STORAGE_ORACLE_BACKEND_FORMAT);
    if (status == COSMOS_OK) {
        status = oracle_acquire(
            script, counts, COSMOS_STORAGE_ORACLE_FACTORY_INITIALIZE);
    }
    return status;
}

int cosmos_storage_oracle_poll(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts) {
    int status;

    if (script->is_qemu) {
        return COSMOS_UNAVAILABLE;
    }
    if (state->ready == 0U) {
        return COSMOS_UNAVAILABLE;
    }
    status = oracle_acquire(
        script, counts, COSMOS_STORAGE_ORACLE_DISPATCH_POLL);
    if (status != COSMOS_OK) {
        return status;
    }
    state->gc_polls++;
    if ((state->gc_polls & COSMOS_STORAGE_ORACLE_GC_POLL_MASK) != 0U) {
        return COSMOS_OK;
    }
    status = oracle_acquire(
        script, counts, COSMOS_STORAGE_ORACLE_GC_STEP);
    if (status == COSMOS_UNAVAILABLE || status == COSMOS_RETRY) {
        return COSMOS_OK;
    }
    if (status != COSMOS_OK) {
        state->ready = 0U;
    }
    return status;
}
