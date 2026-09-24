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

/* Bundle status ABI: begin returns a positive token; 0 on failure.
 * read_stage returns an owned array, including an empty array for verified
 * EOF, or native nil on failure; each read/stage is bounded to <=16 MiB and
 * the aggregate is bounded by max_bytes. identity reports st_dev/st_ino/
 * st_size/mtim sec/mtim nsec/bytes read for field 0..5, else -1.
 * stage_scr1 writes the receipt after EOF; finish(token, commit) consumes
 * the token and returns 1 when the requested action is durable, 0 otherwise.
 * Declarations match the definitions in runtime_native.c. */
#define RT_HSA_BUNDLE_UNSUPPORTED_V1 INT64_C(-4)
int64_t rt_hosted_safe_artifact_bundle_begin_v1(const uint8_t* root, uint64_t root_len,
    const uint8_t* source, uint64_t source_len, const uint8_t* bundle, uint64_t bundle_len,
    const uint8_t* payload, uint64_t payload_len, const uint8_t* scr1, uint64_t scr1_len,
    int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_read_stage_v1(int64_t token, int64_t bound);
int64_t rt_hosted_safe_artifact_bundle_identity_v1(int64_t token, int64_t field);
int64_t rt_hosted_safe_artifact_bundle_stage_scr1_v1(int64_t token, const uint8_t* bytes, uint64_t len, int64_t max_bytes);
int64_t rt_hosted_safe_artifact_bundle_finish_v1(int64_t token, int64_t commit);

#endif
