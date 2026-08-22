#ifndef SIMPLE_RUNTIME_MCDC_V1_H
#define SIMPLE_RUNTIME_MCDC_V1_H

#include <stddef.h>
#include <stdint.h>

#if defined(__cplusplus)
extern "C" {
#endif

enum {
    SIMPLE_MCDC_V1_OK = 0,
    SIMPLE_MCDC_V1_NOT_INITIALIZED = 1,
    SIMPLE_MCDC_V1_INVALID = 2,
    SIMPLE_MCDC_V1_OVERFLOW = 3,
    SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL = 4,
    SIMPLE_MCDC_V1_SESSION_MISMATCH = 5,
    SIMPLE_MCDC_V1_NOT_SEALED = 6,
    SIMPLE_MCDC_V1_BUSY = 7,
    SIMPLE_MCDC_V1_BUDGET_EXHAUSTED = 8,
    SIMPLE_MCDC_V1_DRAINING = 9
};

typedef struct {
    uint64_t decision_id;
    uint32_t condition_count;
    uint32_t reserved0;
    uint64_t source_digest;
    uint64_t evaluated_mask;
    uint64_t true_mask;
    uint64_t owner_id;
    uint64_t owner_sequence;
    uint8_t outcome;
    uint8_t reserved[7];
} SimpleMcdcVectorV1;

typedef struct {
    uint64_t written;
    uint64_t overflow_first;
    uint64_t overflow_count;
    uint64_t session_id;
    uint8_t overflowed;
    uint8_t reserved[7];
} SimpleMcdcSnapshotV1;

typedef struct {
    uint64_t decision_id;
    uint64_t source_digest;
    uint32_t condition_index;
    uint32_t policy;
    uint64_t owner_a;
    uint64_t sequence_a;
    uint64_t owner_b;
    uint64_t sequence_b;
} SimpleMcdcWitnessV1;

typedef struct {
    uint64_t decisions;
    uint64_t gross_conditions;
    uint64_t covered_conditions;
    uint64_t witness_count;
    uint64_t pair_checks;
    uint64_t pair_budget;
} SimpleMcdcAnalysisV1;

#if defined(__cplusplus)
#define SIMPLE_MCDC_STATIC_ASSERT static_assert
#else
#define SIMPLE_MCDC_STATIC_ASSERT _Static_assert
#endif
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcVectorV1) == 64, "SimpleMcdcVectorV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcVectorV1, source_digest) == 16, "source digest ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcVectorV1, evaluated_mask) == 24, "evaluated mask ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcVectorV1, owner_id) == 40, "owner id ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcVectorV1, outcome) == 56, "outcome ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcSnapshotV1) == 40, "SimpleMcdcSnapshotV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcWitnessV1) == 56, "SimpleMcdcWitnessV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcWitnessV1, condition_index) == 16, "witness condition ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcWitnessV1, owner_a) == 24, "witness owner A ABI");
SIMPLE_MCDC_STATIC_ASSERT(offsetof(SimpleMcdcWitnessV1, sequence_b) == 48, "witness sequence B ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcAnalysisV1) == 48, "SimpleMcdcAnalysisV1 ABI");
#undef SIMPLE_MCDC_STATIC_ASSERT

int32_t rt_mcdc_collector_init_v1(void *storage, uint64_t storage_bytes,
                                  uint64_t session_id);
int32_t rt_mcdc_record_vector_v1(uint64_t session_id, uint64_t decision_id,
                                 uint32_t condition_count,
                                 uint64_t source_digest,
                                 uint64_t evaluated_mask, uint64_t true_mask,
                                 uint64_t owner_id, uint64_t owner_sequence,
                                 uint8_t outcome);
/* Compiled-producer lane. Configuration happens before the mission-critical
 * execution boundary; the record operation is fixed-storage and allocation
 * free. Exactly one compiled owner is admitted per collector process. */
int32_t rt_mcdc_configure_compiled_owner_v1(uint64_t session_id,
                                            uint64_t owner_id);
int32_t rt_mcdc_release_compiled_owner_v1(uint64_t session_id,
                                          uint64_t owner_id);
int32_t rt_mcdc_record_compiled_vector_v1(uint64_t decision_id,
                                          uint32_t condition_count,
                                          uint64_t source_digest,
                                          uint64_t evaluated_mask,
                                          uint64_t true_mask,
                                          uint8_t outcome);
int32_t rt_mcdc_compiled_last_status_v1(void);
typedef int32_t (*SimpleMcdcDynamicTargetV1)(
    uint64_t decision_id, uint32_t condition_count, uint64_t source_digest,
    uint64_t evaluated_mask, uint64_t true_mask, uint8_t outcome);
/* Dynamic aspect patchpoint. Idle dispatch is one atomic load and branch;
 * binding/unbinding is loader-owned and allocation free. */
int32_t rt_mcdc_dynamic_vector_patchpoint_v1(uint64_t decision_id,
                                             uint32_t condition_count,
                                             uint64_t source_digest,
                                             uint64_t evaluated_mask,
                                             uint64_t true_mask,
                                             uint8_t outcome);
int32_t rt_mcdc_dynamic_bind_v1(uint64_t target_handle);
int32_t rt_mcdc_dynamic_unbind_v1(uint64_t target_handle);
int32_t rt_mcdc_dynamic_settled_v1(void);
uint64_t rt_mcdc_compiled_target_v1(void);
uint64_t rt_mcdc_dynamic_register_target_v1(uint64_t target_address,
                                             uint64_t owner_cookie);
int32_t rt_mcdc_dynamic_unregister_target_v1(uint64_t target_handle,
                                              uint64_t owner_cookie);
int32_t rt_mcdc_collector_seal_v1(uint64_t session_id);
int32_t rt_mcdc_claim_interpreter_owner_v1(uint64_t session_id,
                                           uint64_t owner_id);
int32_t rt_mcdc_release_interpreter_owner_v1(uint64_t session_id,
                                             uint64_t owner_id);
int32_t rt_mcdc_snapshot_v1(SimpleMcdcVectorV1 *output, uint64_t output_capacity,
                            SimpleMcdcSnapshotV1 *snapshot);
int32_t rt_mcdc_collector_reset_checked_v1(void);
int32_t rt_mcdc_analyze_unique_v1(const SimpleMcdcVectorV1 *events,
                                  uint64_t event_count,
                                  SimpleMcdcWitnessV1 *witnesses,
                                  uint64_t witness_capacity,
                                  uint64_t pair_budget,
                                  SimpleMcdcAnalysisV1 *analysis);
int32_t rt_mcdc_sort_vectors_v1(SimpleMcdcVectorV1 *events,
                                uint64_t event_count);
void rt_mcdc_collector_reset_v1(void);

#if defined(__cplusplus)
}
#endif
#endif
