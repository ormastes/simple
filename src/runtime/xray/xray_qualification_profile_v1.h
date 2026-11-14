#ifndef SIMPLE_XRAY_QUALIFICATION_PROFILE_V1_H
#define SIMPLE_XRAY_QUALIFICATION_PROFILE_V1_H
#include <stdint.h>

/* Private, fixed-width interop record emitted only by the checked link owner.
 * Shape is not authority: approved evidence and exact input bindings belong to
 * the compiler-pinned catalogue/issuer. No caller provides a record pointer. */
#define SIMPLE_XRAY_PROFILE_MAGIC_V1 UINT64_C(0x0031565150525853) /* SXRPQV1\0 */
#define SIMPLE_XRAY_PROFILE_SCHEMA_V1 1
#define SIMPLE_XRAY_PROFILE_ABSENT_V1 0
#define SIMPLE_XRAY_PROFILE_INVALID_V1 (-1)
#define SIMPLE_XRAY_PROFILE_UNSUPPORTED_V1 (-2)
#define SIMPLE_XRAY_PROFILE_SNAPSHOT_V1 (-3)
#define SIMPLE_XRAY_PROFILE_OWNER_V1 (-4)
#define SIMPLE_XRAY_PROFILE_BYTES_V1 480
#define SIMPLE_XRAY_PROFILE_DIGEST_BASE_V1 128
#define SIMPLE_XRAY_PROFILE_DIGESTS_V1 11
#define SIMPLE_XRAY_PROFILE_REQUIRED_EVIDENCE_V1 255
#define SIMPLE_XRAY_PROFILE_TARGET_LINUX_X64_V1 1
#define SIMPLE_XRAY_PROFILE_RAW_STARTUP_V1 1
#define SIMPLE_XRAY_PROFILE_MAX_CONTEXTS_V1 64
#define SIMPLE_XRAY_PROFILE_MAX_PAYLOAD_V1 393216
#define SIMPLE_XRAY_PROFILE_METADATA_RESERVE_V1 33554432
#define SIMPLE_XRAY_PROFILE_MAX_RESIDENT_V1 67108864

/* Word offsets: magic, schema, bytes, target, profile, evidence mask,
 * context limit, per-context payload bytes (ring adds128), raw resident cap,
 * generation limit (one), actual metadata reservation, native word bytes.
 * Bytes96..127 are zero. Digests are raw32-byte SHA256 values, in this order:
 * approved receipt, producer, runtime component manifest, Clang, compiler-rt,
 * LLD, linked closure, generated Simple ABI, runtime ABI/thread evidence,
 * foreign/init closure, full allocation/resource evidence.
 * Scalar digest getters expose eight little-endian u32 words per digest. */
int64_t simple_xray_resident_profile_bind_v1(int64_t snapshot_handle);
int64_t simple_xray_resident_profile_word_v1(int64_t handle, int64_t field);
int64_t simple_xray_resident_profile_digest_word_v1(int64_t handle,
                                                  int64_t digest, int64_t word);
int64_t simple_xray_llvm_resident_publish_qualified_v1(int64_t profile,
        int64_t snapshot, int64_t descriptor, int64_t generation);
#endif
