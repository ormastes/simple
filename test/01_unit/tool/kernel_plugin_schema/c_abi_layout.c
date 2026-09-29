#define SIMPLE_KPF_INCLUDE_ABI_TEST_VECTORS 1
#include "simple_kernel_plugin_v1.h"

#include <stddef.h>

#define ASSERT_SIZE(type, expected) _Static_assert(sizeof(type) == (expected), #type " size")
#define ASSERT_ALIGN(type, expected) _Static_assert(_Alignof(type) == (expected), #type " alignment")
#define ASSERT_OFFSET(type, field, expected) _Static_assert(offsetof(type, field) == (expected), #type "." #field " offset")

ASSERT_SIZE(simple_kpf_id128_v1, 16);
ASSERT_ALIGN(simple_kpf_id128_v1, 8);
ASSERT_SIZE(simple_kpf_digest256_v1, 32);
ASSERT_ALIGN(simple_kpf_digest256_v1, 8);

ASSERT_SIZE(simple_kpf_borrowed_bytes_v1, 32);
ASSERT_OFFSET(simple_kpf_borrowed_bytes_v1, abi_version, 0);
ASSERT_OFFSET(simple_kpf_borrowed_bytes_v1, struct_size, 4);
ASSERT_OFFSET(simple_kpf_borrowed_bytes_v1, data, 8);
ASSERT_OFFSET(simple_kpf_borrowed_bytes_v1, reserved0, 24);

ASSERT_SIZE(simple_kpf_output_buffer_v1, 48);
ASSERT_OFFSET(simple_kpf_output_buffer_v1, data, 8);
ASSERT_OFFSET(simple_kpf_output_buffer_v1, required, 32);
ASSERT_OFFSET(simple_kpf_output_buffer_v1, reserved0, 40);

ASSERT_SIZE(simple_kpf_interface_query_v1, 96);
ASSERT_OFFSET(simple_kpf_interface_query_v1, interface_id, 8);
ASSERT_OFFSET(simple_kpf_interface_query_v1, schema_digest, 32);
ASSERT_OFFSET(simple_kpf_interface_query_v1, required_operation_mask, 64);
ASSERT_OFFSET(simple_kpf_interface_query_v1, reserved, 80);

ASSERT_SIZE(simple_kpf_interface_answer_v1, 88);
ASSERT_OFFSET(simple_kpf_interface_answer_v1, operation_table, 16);
ASSERT_OFFSET(simple_kpf_interface_answer_v1, schema_digest, 40);
ASSERT_OFFSET(simple_kpf_interface_answer_v1, reserved, 72);

ASSERT_SIZE(simple_kpf_call_header_v1, 72);
ASSERT_OFFSET(simple_kpf_call_header_v1, generation, 8);
ASSERT_OFFSET(simple_kpf_call_header_v1, interface_slot, 32);
ASSERT_OFFSET(simple_kpf_call_header_v1, deadline_ns, 40);
ASSERT_OFFSET(simple_kpf_call_header_v1, reserved, 56);

ASSERT_SIZE(simple_kpf_operation_table_v1, 80);
ASSERT_OFFSET(simple_kpf_operation_table_v1, open_session, 16);
ASSERT_OFFSET(simple_kpf_operation_table_v1, close_session, 56);
ASSERT_OFFSET(simple_kpf_operation_table_v1, reserved, 64);

static simple_kpf_status_v1 query_stub(
    const simple_kpf_interface_query_v1 *query,
    simple_kpf_interface_answer_v1 *answer) {
    return query != NULL && answer != NULL ? SIMPLE_KPF_STATUS_OK : SIMPLE_KPF_STATUS_INVALID_ARGUMENT;
}

int main(void) {
    simple_kpf_plugin_entry_fn_v1 entry = query_stub;
    uint32_t index;
    if (entry == NULL || SIMPLE_KPF_ABI_LAYOUT_VECTOR_COUNT_V1 != 9) {
        return 1;
    }
    for (index = 0; index < SIMPLE_KPF_ABI_LAYOUT_VECTOR_COUNT_V1; ++index) {
        const simple_kpf_abi_layout_vector_v1 *vector =
            &SIMPLE_KPF_ABI_LAYOUT_VECTORS_V1[index];
        if (simple_kpf_validate_abi_layout_vector_v1(vector) !=
            (int)vector->expected_valid) {
            return 2;
        }
    }
    return 0;
}
