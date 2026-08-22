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
    SIMPLE_MCDC_V1_BUSY = 7
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

_Static_assert(sizeof(SimpleMcdcVectorV1) == 64, "SimpleMcdcVectorV1 ABI");
_Static_assert(offsetof(SimpleMcdcVectorV1, source_digest) == 16, "source digest ABI");
_Static_assert(offsetof(SimpleMcdcVectorV1, evaluated_mask) == 24, "evaluated mask ABI");
_Static_assert(offsetof(SimpleMcdcVectorV1, owner_id) == 40, "owner id ABI");
_Static_assert(offsetof(SimpleMcdcVectorV1, outcome) == 56, "outcome ABI");
_Static_assert(sizeof(SimpleMcdcSnapshotV1) == 40, "SimpleMcdcSnapshotV1 ABI");

int32_t rt_mcdc_collector_init_v1(void *storage, uint64_t storage_bytes,
                                  uint64_t session_id);
int32_t rt_mcdc_record_vector_v1(uint64_t session_id, uint64_t decision_id,
                                 uint32_t condition_count,
                                 uint64_t source_digest,
                                 uint64_t evaluated_mask, uint64_t true_mask,
                                 uint64_t owner_id, uint64_t owner_sequence,
                                 uint8_t outcome);
int32_t rt_mcdc_collector_seal_v1(uint64_t session_id);
int32_t rt_mcdc_claim_interpreter_owner_v1(uint64_t session_id,
                                           uint64_t owner_id);
int32_t rt_mcdc_release_interpreter_owner_v1(uint64_t session_id,
                                             uint64_t owner_id);
int32_t rt_mcdc_snapshot_v1(SimpleMcdcVectorV1 *output, uint64_t output_capacity,
                            SimpleMcdcSnapshotV1 *snapshot);
void rt_mcdc_collector_reset_v1(void);

#if defined(__cplusplus)
}
#endif
#endif
