/* Explicit absent provider operations; never reinterpret a single-bundle
 * token as an unimplemented multi-artifact transaction. */
/* Self-contained for the standalone syntax gate: both headers are
 * include-guarded, so the real owner context (which included them already)
 * sees a no-op. */
#include "runtime.h"
#include "runtime_hosted_safe_artifact_v1.h"
int64_t rt_hosted_safe_artifact_bundle3_begin_v1(int64_t root,
    const uint8_t* source0, uint64_t source0_len, const uint8_t* source1, uint64_t source1_len,
    const uint8_t* source2, uint64_t source2_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload0, uint64_t payload0_len, const uint8_t* scr10, uint64_t scr10_len,
    const uint8_t* payload1, uint64_t payload1_len, const uint8_t* scr11, uint64_t scr11_len,
    const uint8_t* payload2, uint64_t payload2_len, const uint8_t* scr12, uint64_t scr12_len,
    int64_t max_bytes) {
    (void)root; (void)source0; (void)source0_len; (void)source1; (void)source1_len; (void)source2; (void)source2_len; (void)bundle; (void)bundle_len; (void)payload0; (void)payload0_len; (void)scr10; (void)scr10_len; (void)payload1; (void)payload1_len; (void)scr11; (void)scr11_len; (void)payload2; (void)payload2_len; (void)scr12; (void)scr12_len; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle3_read_stage_v1(int64_t token, int64_t slot, int64_t max_bytes) {
    (void)token; (void)slot; (void)max_bytes;
    return rt_value_nil();
}

int64_t rt_hosted_safe_artifact_bundle3_identity_v1(int64_t token, int64_t slot, int64_t field) {
    (void)token; (void)slot; (void)field;
    return -1;
}

int64_t rt_hosted_safe_artifact_bundle3_stage_scr1_v1(int64_t token, int64_t slot, int64_t payload, int64_t max_bytes) {
    (void)token; (void)slot; (void)payload; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle3_finish_v1(int64_t token, bool commit) {
    (void)token; (void)commit;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_begin_v1(int64_t root,
    const uint8_t* bundle, uint64_t bundle_len, const uint8_t* descriptor, uint64_t descriptor_len,
    int64_t count, int64_t max_bytes) {
    (void)root; (void)bundle; (void)bundle_len; (void)descriptor; (void)descriptor_len; (void)count; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_begin_two_descriptors_v1(int64_t root,
    const uint8_t* bundle, uint64_t bundle_len, const uint8_t* descriptor0, uint64_t descriptor0_len,
    const uint8_t* descriptor1, uint64_t descriptor1_len, int64_t count, int64_t max_bytes) {
    (void)root; (void)bundle; (void)bundle_len; (void)descriptor0; (void)descriptor0_len; (void)descriptor1; (void)descriptor1_len; (void)count; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_add_slot_v1(int64_t token, int64_t slot,
    const uint8_t* source, uint64_t source_len, const uint8_t* payload, uint64_t payload_len,
    const uint8_t* scr1, uint64_t scr1_len) {
    (void)token; (void)slot; (void)source; (void)source_len; (void)payload; (void)payload_len; (void)scr1; (void)scr1_len;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_seal_v1(int64_t token) {
    (void)token;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_read_stage_v1(int64_t token, int64_t slot, int64_t max_bytes) {
    (void)token; (void)slot; (void)max_bytes;
    return rt_value_nil();
}

int64_t rt_hosted_safe_artifact_bundle_n_identity_v1(int64_t token, int64_t slot, int64_t field) {
    (void)token; (void)slot; (void)field;
    return -1;
}

int64_t rt_hosted_safe_artifact_bundle_n_stage_scr1_v1(int64_t token, int64_t slot, int64_t payload, int64_t max_bytes) {
    (void)token; (void)slot; (void)payload; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_stage_descriptor_v1(int64_t token, int64_t payload, int64_t max_bytes) {
    (void)token; (void)payload; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_stage_named_descriptor_v1(int64_t token, int64_t slot,
    const uint8_t* leaf, uint64_t leaf_len, int64_t payload, int64_t max_bytes) {
    (void)token; (void)slot; (void)leaf; (void)leaf_len; (void)payload; (void)max_bytes;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}

int64_t rt_hosted_safe_artifact_bundle_n_finish_v1(int64_t token, bool commit) {
    (void)token; (void)commit;
    return RT_HSA_BUNDLE_UNSUPPORTED_V1;
}
