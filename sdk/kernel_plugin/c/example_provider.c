#include "kpf_v1.h"

#include <string.h>

enum { EXAMPLE_OPERATION_MASK = 1 };
static const uint64_t EXAMPLE_CONTEXT = UINT64_C(0x4558414d504c45);
static const uint64_t EXAMPLE_SESSION = UINT64_C(0x53455353494f4e);
static int example_quiesced;
static int example_closed;

static simple_kpf_status_v1 example_open(
    uint64_t provider_context,
    const simple_kpf_borrowed_bytes_v1 *configuration,
    uint64_t *session_out) {
    if (provider_context != EXAMPLE_CONTEXT || configuration == NULL ||
        session_out == NULL || configuration->abi_version != SIMPLE_KPF_ABI_V1) {
        return SIMPLE_KPF_STATUS_INVALID_ARGUMENT;
    }
    example_quiesced = 0;
    example_closed = 0;
    *session_out = EXAMPLE_SESSION;
    return SIMPLE_KPF_STATUS_OK;
}

static simple_kpf_status_v1 example_submit(
    uint64_t provider_context,
    const simple_kpf_call_header_v1 *call,
    const simple_kpf_borrowed_bytes_v1 *input,
    simple_kpf_output_buffer_v1 *output) {
    if (provider_context != EXAMPLE_CONTEXT || call == NULL || input == NULL ||
        output == NULL || call->session != EXAMPLE_SESSION || example_closed ||
        example_quiesced) {
        return SIMPLE_KPF_STATUS_REJECTED;
    }
    output->required = input->size;
    if (output->capacity < input->size) {
        output->used = 0;
        return SIMPLE_KPF_STATUS_NEED_MORE;
    }
    if (input->size != 0) {
        memcpy(output->data, input->data, (size_t)input->size);
    }
    output->used = input->size;
    return SIMPLE_KPF_STATUS_OK;
}

static simple_kpf_status_v1 example_poll(
    uint64_t provider_context,
    uint64_t session,
    simple_kpf_output_buffer_v1 *completions) {
    if (provider_context != EXAMPLE_CONTEXT || session != EXAMPLE_SESSION ||
        completions == NULL || example_closed) {
        return SIMPLE_KPF_STATUS_STALE_HANDLE;
    }
    completions->used = 0;
    completions->required = 0;
    return SIMPLE_KPF_STATUS_OK;
}

static simple_kpf_status_v1 example_cancel(
    uint64_t provider_context,
    const simple_kpf_call_header_v1 *call) {
    return provider_context == EXAMPLE_CONTEXT && call != NULL &&
                   call->session == EXAMPLE_SESSION && !example_closed
               ? SIMPLE_KPF_STATUS_OK
               : SIMPLE_KPF_STATUS_STALE_HANDLE;
}

static simple_kpf_status_v1 example_quiesce(
    uint64_t provider_context,
    uint64_t session,
    uint64_t deadline_ns,
    uint64_t flags) {
    (void)deadline_ns;
    (void)flags;
    if (provider_context != EXAMPLE_CONTEXT || session != EXAMPLE_SESSION ||
        example_closed) {
        return SIMPLE_KPF_STATUS_STALE_HANDLE;
    }
    example_quiesced = 1;
    return SIMPLE_KPF_STATUS_OK;
}

static simple_kpf_status_v1 example_close(
    uint64_t provider_context,
    uint64_t session) {
    if (provider_context != EXAMPLE_CONTEXT || session != EXAMPLE_SESSION ||
        example_closed || !example_quiesced) {
        return SIMPLE_KPF_STATUS_REJECTED;
    }
    example_closed = 1;
    return SIMPLE_KPF_STATUS_OK;
}

static const simple_kpf_operation_table_v1 EXAMPLE_OPERATIONS = {
    SIMPLE_KPF_ABI_V1,
    sizeof(simple_kpf_operation_table_v1),
    6,
    0,
    example_open,
    example_submit,
    example_poll,
    example_cancel,
    example_quiesce,
    example_close,
    {0, 0}};

simple_kpf_status_v1 simple_kpf_plugin_v1(
    const simple_kpf_interface_query_v1 *query,
    simple_kpf_interface_answer_v1 *answer) {
    if (query == NULL || answer == NULL ||
        query->abi_version != SIMPLE_KPF_ABI_V1 ||
        query->interface_major != 1 ||
        (query->required_operation_mask & ~((uint64_t)EXAMPLE_OPERATION_MASK)) != 0) {
        return SIMPLE_KPF_STATUS_REJECTED;
    }
    memset(answer, 0, sizeof(*answer));
    answer->abi_version = SIMPLE_KPF_ABI_V1;
    answer->struct_size = (uint32_t)sizeof(*answer);
    answer->operation_count = EXAMPLE_OPERATIONS.operation_count;
    answer->operation_table = &EXAMPLE_OPERATIONS;
    answer->provided_operation_mask = EXAMPLE_OPERATION_MASK;
    answer->provided_capability_mask = 0;
    answer->schema_digest = query->schema_digest;
    return SIMPLE_KPF_STATUS_OK;
}

uint64_t simple_kpf_example_context_v1(void) { return EXAMPLE_CONTEXT; }
