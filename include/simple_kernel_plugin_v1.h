#ifndef SIMPLE_KERNEL_PLUGIN_V1_H
#define SIMPLE_KERNEL_PLUGIN_V1_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#define SIMPLE_KPF_ABI_V1 UINT32_C(1)
#define SIMPLE_KPF_PLUGIN_ENTRY_V1 "simple_kpf_plugin_v1"

typedef int32_t simple_kpf_status_v1;

typedef struct simple_kpf_abi_layout_vector_v1 {
    const char *name;
    uint64_t available_size;
    uint64_t struct_size;
    uint64_t payload_offset;
    uint64_t payload_length;
    uint64_t required_alignment;
    uint64_t reserved0;
    uint32_t expected_valid;
    uint32_t reserved1;
} simple_kpf_abi_layout_vector_v1;

static inline int simple_kpf_validate_abi_layout_vector_v1(
    const simple_kpf_abi_layout_vector_v1 *vector) {
    if (vector == NULL || vector->struct_size < UINT64_C(32) ||
        vector->struct_size > vector->available_size || vector->reserved0 != 0 ||
        vector->reserved1 != 0 || vector->required_alignment == 0 ||
        (vector->required_alignment & (vector->required_alignment - 1)) != 0 ||
        vector->payload_offset < vector->struct_size ||
        vector->payload_offset > vector->available_size ||
        (vector->payload_offset % vector->required_alignment) != 0) {
        return 0;
    }
    return vector->payload_length <= vector->available_size - vector->payload_offset;
}

enum {
    SIMPLE_KPF_STATUS_OK = 0,
    SIMPLE_KPF_STATUS_PENDING = 1,
    SIMPLE_KPF_STATUS_WOULD_BLOCK = 2,
    SIMPLE_KPF_STATUS_NEED_MORE = 3,
    SIMPLE_KPF_STATUS_CANCELLED = 4,
    SIMPLE_KPF_STATUS_DEADLINE_EXCEEDED = 5,
    SIMPLE_KPF_STATUS_CAPACITY_EXCEEDED = 6,
    SIMPLE_KPF_STATUS_REJECTED = 7,
    SIMPLE_KPF_STATUS_STALE_HANDLE = 8,
    SIMPLE_KPF_STATUS_INVALID_ARGUMENT = 9,
    SIMPLE_KPF_STATUS_FAILED = 10
};

typedef struct simple_kpf_id128_v1 {
    uint64_t hi;
    uint64_t lo;
} simple_kpf_id128_v1;

typedef struct simple_kpf_digest256_v1 {
    uint64_t words[4];
} simple_kpf_digest256_v1;

typedef struct simple_kpf_borrowed_bytes_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    const uint8_t *data;
    uint64_t size;
    uint64_t reserved0;
} simple_kpf_borrowed_bytes_v1;

typedef struct simple_kpf_output_buffer_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    uint8_t *data;
    uint64_t capacity;
    uint64_t used;
    uint64_t required;
    uint64_t reserved0;
} simple_kpf_output_buffer_v1;

typedef struct simple_kpf_interface_query_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    simple_kpf_id128_v1 interface_id;
    uint32_t interface_major;
    uint32_t minimum_minor;
    simple_kpf_digest256_v1 schema_digest;
    uint64_t required_operation_mask;
    uint64_t required_capability_mask;
    uint64_t reserved[2];
} simple_kpf_interface_query_v1;

struct simple_kpf_operation_table_v1;

typedef struct simple_kpf_interface_answer_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    uint32_t operation_count;
    uint32_t flags;
    const struct simple_kpf_operation_table_v1 *operation_table;
    uint64_t provided_operation_mask;
    uint64_t provided_capability_mask;
    simple_kpf_digest256_v1 schema_digest;
    uint64_t reserved[2];
} simple_kpf_interface_answer_v1;

typedef struct simple_kpf_call_header_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    uint64_t generation;
    uint64_t session;
    uint64_t request;
    uint32_t interface_slot;
    uint32_t operation_slot;
    uint64_t deadline_ns;
    uint64_t flags;
    uint64_t reserved[2];
} simple_kpf_call_header_v1;

typedef simple_kpf_status_v1 (*simple_kpf_open_session_fn_v1)(
    uint64_t provider_context,
    const simple_kpf_borrowed_bytes_v1 *configuration,
    uint64_t *session_out);
typedef simple_kpf_status_v1 (*simple_kpf_submit_batch_fn_v1)(
    uint64_t provider_context,
    const simple_kpf_call_header_v1 *call,
    const simple_kpf_borrowed_bytes_v1 *input,
    simple_kpf_output_buffer_v1 *output);
typedef simple_kpf_status_v1 (*simple_kpf_poll_fn_v1)(
    uint64_t provider_context,
    uint64_t session,
    simple_kpf_output_buffer_v1 *completions);
typedef simple_kpf_status_v1 (*simple_kpf_cancel_fn_v1)(
    uint64_t provider_context,
    const simple_kpf_call_header_v1 *call);
typedef simple_kpf_status_v1 (*simple_kpf_quiesce_fn_v1)(
    uint64_t provider_context,
    uint64_t session,
    uint64_t deadline_ns,
    uint64_t flags);
typedef simple_kpf_status_v1 (*simple_kpf_close_session_fn_v1)(
    uint64_t provider_context,
    uint64_t session);

typedef struct simple_kpf_operation_table_v1 {
    uint32_t abi_version;
    uint32_t struct_size;
    uint32_t operation_count;
    uint32_t flags;
    simple_kpf_open_session_fn_v1 open_session;
    simple_kpf_submit_batch_fn_v1 submit_batch;
    simple_kpf_poll_fn_v1 poll;
    simple_kpf_cancel_fn_v1 cancel;
    simple_kpf_quiesce_fn_v1 quiesce;
    simple_kpf_close_session_fn_v1 close_session;
    uint64_t reserved[2];
} simple_kpf_operation_table_v1;

typedef simple_kpf_status_v1 (*simple_kpf_plugin_entry_fn_v1)(
    const simple_kpf_interface_query_v1 *query,
    simple_kpf_interface_answer_v1 *answer);

#define SIMPLE_KPF_ABI_LAYOUT_PREFIX_SIZE_V1 UINT64_C(32)
#ifdef SIMPLE_KPF_INCLUDE_ABI_TEST_VECTORS
#define SIMPLE_KPF_ABI_LAYOUT_VECTOR_COUNT_V1 UINT32_C(9)
static const simple_kpf_abi_layout_vector_v1 SIMPLE_KPF_ABI_LAYOUT_VECTORS_V1[] = {
    {"valid_exact", UINT64_C(48), UINT64_C(32), UINT64_C(32), UINT64_C(16), UINT64_C(8), UINT64_C(0), UINT32_C(1), UINT32_C(0)},
    {"valid_append_only_tail", UINT64_C(56), UINT64_C(40), UINT64_C(40), UINT64_C(16), UINT64_C(8), UINT64_C(0), UINT32_C(1), UINT32_C(0)},
    {"truncated_prefix", UINT64_C(48), UINT64_C(31), UINT64_C(32), UINT64_C(16), UINT64_C(8), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
    {"declared_oversize", UINT64_C(48), UINT64_C(56), UINT64_C(56), UINT64_C(0), UINT64_C(8), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
    {"reserved_nonzero", UINT64_C(48), UINT64_C(32), UINT64_C(32), UINT64_C(16), UINT64_C(8), UINT64_C(1), UINT32_C(0), UINT32_C(0)},
    {"offset_before_header", UINT64_C(48), UINT64_C(32), UINT64_C(24), UINT64_C(16), UINT64_C(8), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
    {"offset_length_overflow", UINT64_C(48), UINT64_C(32), UINT64_C(40), UINT64_C(16), UINT64_C(8), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
    {"misaligned_offset", UINT64_C(48), UINT64_C(32), UINT64_C(36), UINT64_C(8), UINT64_C(8), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
    {"invalid_alignment", UINT64_C(48), UINT64_C(32), UINT64_C(32), UINT64_C(16), UINT64_C(3), UINT64_C(0), UINT32_C(0), UINT32_C(0)},
};
#endif

#ifdef __cplusplus
}
#endif

#endif
