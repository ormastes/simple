#ifndef SIMPLE_WORKSPACE_STORAGE_V1_H
#define SIMPLE_WORKSPACE_STORAGE_V1_H
#include <stdint.h>
/* All text parameters/results are tagged runtime strings, not split pointers.
 * Negative scalar outcomes reject or retain ownership; zero is never a lease.
 * No operation in this ABI deletes data, changes quotas, or releases a ledger. */
int64_t rt_workspace_storage_open_v1(int64_t kind, int64_t parent, int64_t leaf,
    int64_t pool, int64_t workspace, int64_t quota, int64_t hard_bytes, int64_t policy);
int64_t rt_workspace_storage_recover_v1(int64_t kind, int64_t parent, int64_t leaf,
    int64_t pool, int64_t workspace, int64_t quota, int64_t hard_bytes, int64_t policy);
int64_t rt_workspace_storage_observe_v1(int64_t token);
int64_t rt_workspace_storage_release_if_absent_v1(int64_t token);
int64_t rt_workspace_storage_forget_released_v1(int64_t token);
#endif
