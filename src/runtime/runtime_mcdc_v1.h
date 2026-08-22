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
    SIMPLE_MCDC_V1_DRAINING = 9,
    SIMPLE_MCDC_V1_GATE_FAILED = 10,
    SIMPLE_MCDC_V1_EMPTY_DENOMINATOR = 11,
    SIMPLE_MCDC_V1_EXCLUSION_INVALID = 12
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

enum {
    SIMPLE_MCDC_EXPR_CONDITION_V1 = 1,
    SIMPLE_MCDC_EXPR_NOT_V1 = 2,
    SIMPLE_MCDC_EXPR_AND_V1 = 3,
    SIMPLE_MCDC_EXPR_OR_V1 = 4
};

typedef struct {
    uint8_t opcode;
    uint8_t reserved[3];
    uint32_t condition_index;
} SimpleMcdcExprTokenV1;

typedef struct {
    uint64_t decision_id;
    uint64_t source_digest;
    uint32_t condition_count;
    uint32_t token_count;
    uint64_t token_offset;
} SimpleMcdcDecisionExprV1;

/* Validated MCDP wire metadata.  The wire identity is the compiler-emitted
 * lowercase SHA-256 text; it is copied, not NUL terminated. */
typedef struct {
    uint64_t program_count;
    uint64_t token_count;
    uint64_t semantic_count;
    uint64_t semantic_offset;
    uint8_t identity_sha256[64];
} SimpleMcdcManifestInfoV1;

enum {
    SIMPLE_MCDC_REPORT_NORMAL_V1 = 0,
    SIMPLE_MCDC_REPORT_ALPHA_V1 = 1,
    SIMPLE_MCDC_REPORT_BETA_V1 = 2,
    SIMPLE_MCDC_EXCLUSION_CAPABILITY_UNAVAILABLE_V1 = 1,
    SIMPLE_MCDC_EXCLUSION_REASON_BYTES_V1 = 96
};

/* Governed exclusion bound to the complete native decision identity.  Text is
 * length-delimited so critical-mode validation never scans outside the row. */
typedef struct {
    uint64_t decision_id;
    uint64_t source_digest;
    uint64_t condition_mask;
    uint64_t capability_id;
    uint64_t evidence_digest_hi;
    uint64_t evidence_digest_lo;
    uint64_t owner_id;
    uint64_t reviewed_epoch;
    uint64_t expires_epoch;
    uint32_t condition_count;
    uint32_t kind;
    uint32_t reason_length;
    uint32_t reserved0;
    uint8_t reason[SIMPLE_MCDC_EXCLUSION_REASON_BYTES_V1];
} SimpleMcdcExclusionV1;

typedef struct {
    uint64_t decisions;
    uint64_t gross_conditions;
    uint64_t excluded_conditions;
    uint64_t eligible_conditions;
    uint64_t covered_eligible_conditions;
    uint64_t uncovered_eligible_conditions;
    uint64_t validated_exclusions;
    uint64_t event_count;
    uint64_t witness_count;
    uint64_t proof_checks;
    uint32_t mode;
    uint32_t gate_passed;
    uint8_t provenance_sha256[64];
} SimpleMcdcReportV1;

/* Recompute the lowercase SHA-256 identity over canonical MCDP V1 bytes:
 * bytes [0,24) followed by bytes [88,byte_count). The embedded identity field
 * is deliberately excluded. This helper is allocation free. */
int32_t rt_mcdc_manifest_identity_v1(const uint8_t *bytes,
                                     uint64_t byte_count,
                                     uint8_t identity_sha256[64]);

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
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcExprTokenV1) == 8, "SimpleMcdcExprTokenV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcDecisionExprV1) == 32, "SimpleMcdcDecisionExprV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcManifestInfoV1) == 96, "SimpleMcdcManifestInfoV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcExclusionV1) == 184, "SimpleMcdcExclusionV1 ABI");
SIMPLE_MCDC_STATIC_ASSERT(sizeof(SimpleMcdcReportV1) == 152, "SimpleMcdcReportV1 ABI");
#undef SIMPLE_MCDC_STATIC_ASSERT

int32_t rt_mcdc_collector_init_v1(void *storage, uint64_t storage_bytes,
                                  uint64_t session_id);
/* Partition caller-owned storage into bounded independent producer shards.
 * owner_id selects a deterministic primary shard; a full primary probes each
 * remaining shard once in ring order before reporting sticky overflow.  The
 * record path performs no lock or allocation.  A one-shard init is exactly
 * the legacy collector_init_v1 behavior. */
int32_t rt_mcdc_collector_init_sharded_v1(void *storage,
                                         uint64_t storage_bytes,
                                         uint64_t session_id,
                                         uint32_t shard_count);
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
/* Loader-only address bridge for the one allowlisted dynamic-aspect import.
 * The public MC/DC facade continues to expose only the opaque target handle. */
uint64_t rt_mcdc_compiled_target_address_v1(void);
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
/* Expression-aware unique-cause plus validated masking analysis. Programs and
 * tokens are caller-owned, sorted by source_digest then decision_id, and use a
 * bounded postfix Boolean representation. Policy 0 witnesses are unique-cause;
 * policy 1 witnesses are masking proofs. */
int32_t rt_mcdc_analyze_masking_v1(
    const SimpleMcdcVectorV1 *events, uint64_t event_count,
    const SimpleMcdcDecisionExprV1 *programs, uint64_t program_count,
    const SimpleMcdcExprTokenV1 *tokens, uint64_t token_count,
    SimpleMcdcWitnessV1 *witnesses, uint64_t witness_capacity,
    uint64_t proof_budget, SimpleMcdcAnalysisV1 *analysis);
/* Validate a compiler-emitted MCDP V1 byte section and report exact bounded
 * caller-storage requirements.  No allocation occurs. */
int32_t rt_mcdc_manifest_requirements_v1(
    const uint8_t *bytes, uint64_t byte_count,
    SimpleMcdcManifestInfoV1 *info);
/* Decode little-endian wire rows into aligned caller-owned ABI arrays.  Use
 * requirements_v1 before entering a no-allocation execution phase. */
int32_t rt_mcdc_manifest_decode_v1(
    const uint8_t *bytes, uint64_t byte_count,
    SimpleMcdcDecisionExprV1 *programs, uint64_t program_capacity,
    SimpleMcdcExprTokenV1 *tokens, uint64_t token_capacity,
    SimpleMcdcManifestInfoV1 *info);
/* Allocation-free convenience bridge: validate/materialize MCDP, then invoke
 * the canonical masking analyzer using the supplied workspace. */
int32_t rt_mcdc_analyze_masking_mcdp_v1(
    const SimpleMcdcVectorV1 *events, uint64_t event_count,
    const uint8_t *bytes, uint64_t byte_count,
    SimpleMcdcDecisionExprV1 *program_workspace,
    uint64_t program_capacity,
    SimpleMcdcExprTokenV1 *token_workspace, uint64_t token_capacity,
    SimpleMcdcWitnessV1 *witnesses, uint64_t witness_capacity,
    uint64_t proof_budget, SimpleMcdcAnalysisV1 *analysis,
    SimpleMcdcManifestInfoV1 *info);
/* Authoritative bounded report/gate owner. Events are sorted in place, then
 * joined to the manifest, masking witnesses, and fresh governed exclusions.
 * All workspace is caller-owned; this function performs no allocation or I/O.
 * Normal mode returns GATE_FAILED unless eligible coverage is exactly 100%. */
int32_t rt_mcdc_report_mcdp_v1(
    SimpleMcdcVectorV1 *events, uint64_t event_count,
    const uint8_t *manifest_bytes, uint64_t manifest_byte_count,
    const SimpleMcdcExclusionV1 *exclusions, uint64_t exclusion_count,
    uint64_t current_epoch, uint32_t mode,
    SimpleMcdcDecisionExprV1 *program_workspace, uint64_t program_capacity,
    SimpleMcdcExprTokenV1 *token_workspace, uint64_t token_capacity,
    SimpleMcdcWitnessV1 *witness_workspace, uint64_t witness_capacity,
    uint64_t proof_budget, SimpleMcdcReportV1 *report);
int32_t rt_mcdc_sort_vectors_v1(SimpleMcdcVectorV1 *events,
                                uint64_t event_count);
void rt_mcdc_collector_reset_v1(void);

#if defined(__cplusplus)
}
#endif
#endif
