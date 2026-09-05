#ifndef SIMPLE_COSMOS_STORAGE_POLICY_ORACLE_H
#define SIMPLE_COSMOS_STORAGE_POLICY_ORACLE_H

/* Frozen, independent action vocabulary for the pre-migration C oracle. */
enum cosmos_storage_oracle_action {
    COSMOS_STORAGE_ORACLE_BACKEND_INIT = 0,
    COSMOS_STORAGE_ORACLE_FTL_INIT = 1,
    COSMOS_STORAGE_ORACLE_BACKEND_MOUNT = 2,
    COSMOS_STORAGE_ORACLE_FTL_RECOVER = 3,
    COSMOS_STORAGE_ORACLE_MEDIA_INIT = 4,
    COSMOS_STORAGE_ORACLE_IO_INIT = 5,
    COSMOS_STORAGE_ORACLE_ADMIN_INIT = 6,
    COSMOS_STORAGE_ORACLE_DISPATCH_INIT = 7,
    COSMOS_STORAGE_ORACLE_BACKEND_FORMAT = 8,
    COSMOS_STORAGE_ORACLE_FACTORY_INITIALIZE = 9,
    COSMOS_STORAGE_ORACLE_DISPATCH_POLL = 10,
    COSMOS_STORAGE_ORACLE_GC_STEP = 11,
    COSMOS_STORAGE_ORACLE_ACTION_COUNT = 12
};

struct cosmos_storage_oracle_script {
    int is_qemu;
    int status[COSMOS_STORAGE_ORACLE_ACTION_COUNT];
};

struct cosmos_storage_oracle_counts {
    unsigned int calls[COSMOS_STORAGE_ORACLE_ACTION_COUNT];
};

struct cosmos_storage_oracle_state {
    unsigned int prepared;
    unsigned int ready;
    unsigned int gc_polls;
};

void cosmos_storage_oracle_state_reset(
    struct cosmos_storage_oracle_state *state);
void cosmos_storage_oracle_counts_reset(
    struct cosmos_storage_oracle_counts *counts);
int cosmos_storage_oracle_init(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts);
int cosmos_storage_oracle_factory_initialize_erased(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts);
int cosmos_storage_oracle_poll(
    struct cosmos_storage_oracle_state *state,
    const struct cosmos_storage_oracle_script *script,
    struct cosmos_storage_oracle_counts *counts);

#endif
