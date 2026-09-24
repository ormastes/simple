#ifndef SIMPLE_RUNTIME_HOSTED_SAFE_ARTIFACT_V1_H
#define SIMPLE_RUNTIME_HOSTED_SAFE_ARTIFACT_V1_H

#include <stdbool.h>
#include <stdint.h>

/* Retained-root handles are provider-owned tokens, never caller-owned fds.
 * Text arguments use the native (pointer, byte-length) ABI. Arrays are runtime
 * values. Read returns canonical native nil (rt_value_nil(), raw 3) on failure
 * and an owned array, including for an
 * empty file, on success. No operation follows a symlink or crosses a mount
 * below the retained root. Linux requires openat2 and O_TMPFILE support.
 * Other platforms fail closed until they provide those guarantees.
 *
 * Publish statuses: 0 durable; -1 rejected; -2 destination already exists;
 * -3 unsupported; -4 visible but durability/close failed; -5 cleanup failed.
 * A -4 result must never be retried as if publication had not happened.
 */
int64_t rt_hosted_safe_artifact_root_open_v1(const uint8_t* root, uint64_t length);
bool rt_hosted_safe_artifact_root_close_v1(int64_t handle);
int64_t rt_hosted_safe_artifact_read_v1(int64_t handle, const uint8_t* path,
                                      uint64_t length, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_publish_v1(int64_t handle, const uint8_t* path,
                                         uint64_t length, int64_t payload,
                                         int64_t max_bytes);

/* Bundle status ABI: begin returns a positive token; failure is negative.
 * Stage returns 1 or 0. Finish consumes the token: 1 = requested action
 * durable, -1 = commit rejected with durable rollback, -2 = visible but
 * durability/close failed, -3 = cleanup uncertain, -4 = unsupported,
 * 0 = invalid/consumed token. Reads return native nil on failure, and a
 * present empty byte array ONLY for verified EOF. Max_bytes bounds the
 * aggregate payload + receipt, up to 1 GiB; each read/stage is <=16 MiB.
 * Named publication requires an effective-uid-owned parent without group/
 * other write permissions and owner-private staging. Same-uid/privileged
 * native actors are trusted; this is not protection from those actors
 * mutating process descriptors, owner memory, or publication names.
 * Bundle3/N are explicit unsupported exports until their transaction
 * adapters are implemented. They never accept a token or publish bytes. */
#define RT_HSA_BUNDLE_UNSUPPORTED_V1 INT64_C(-4)
int64_t rt_hosted_safe_artifact_bundle_begin_v1(int64_t root,
    const uint8_t* source, uint64_t source_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload, uint64_t payload_len, const uint8_t* scr1, uint64_t scr1_len,
    int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_read_stage_v1(int64_t token, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_identity_v1(int64_t token, int64_t field);
int64_t rt_hosted_safe_artifact_bundle_stage_scr1_v1(int64_t token, int64_t payload, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_finish_v1(int64_t token, bool commit);
int64_t rt_hosted_safe_artifact_bundle3_begin_v1(int64_t root,
    const uint8_t* source0, uint64_t source0_len, const uint8_t* source1, uint64_t source1_len,
    const uint8_t* source2, uint64_t source2_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload0, uint64_t payload0_len, const uint8_t* scr10, uint64_t scr10_len,
    const uint8_t* payload1, uint64_t payload1_len, const uint8_t* scr11, uint64_t scr11_len,
    const uint8_t* payload2, uint64_t payload2_len, const uint8_t* scr12, uint64_t scr12_len,
    int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle3_read_stage_v1(int64_t token, int64_t slot, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle3_identity_v1(int64_t token, int64_t slot, int64_t field);
int64_t rt_hosted_safe_artifact_bundle3_stage_scr1_v1(int64_t token, int64_t slot, int64_t payload, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle3_finish_v1(int64_t token, bool commit);
int64_t rt_hosted_safe_artifact_bundle_n_begin_v1(int64_t root,
    const uint8_t* bundle, uint64_t bundle_len, const uint8_t* descriptor, uint64_t descriptor_len,
    int64_t count, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_begin_two_descriptors_v1(int64_t root,
    const uint8_t* bundle, uint64_t bundle_len, const uint8_t* descriptor0, uint64_t descriptor0_len,
    const uint8_t* descriptor1, uint64_t descriptor1_len, int64_t count, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_add_slot_v1(int64_t token, int64_t slot,
    const uint8_t* source, uint64_t source_len, const uint8_t* payload, uint64_t payload_len,
    const uint8_t* scr1, uint64_t scr1_len);
int64_t rt_hosted_safe_artifact_bundle_n_seal_v1(int64_t token);
int64_t rt_hosted_safe_artifact_bundle_n_read_stage_v1(int64_t token, int64_t slot, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_identity_v1(int64_t token, int64_t slot, int64_t field);
int64_t rt_hosted_safe_artifact_bundle_n_stage_scr1_v1(int64_t token, int64_t slot, int64_t payload, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_stage_descriptor_v1(int64_t token, int64_t payload, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_stage_named_descriptor_v1(int64_t token, int64_t slot,
    const uint8_t* leaf, uint64_t leaf_len, int64_t payload, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_n_finish_v1(int64_t token, bool commit);

#endif
