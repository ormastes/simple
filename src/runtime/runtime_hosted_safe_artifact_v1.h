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

#endif
