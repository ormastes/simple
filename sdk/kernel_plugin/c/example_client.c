#include "kpf_v1.h"

#include <assert.h>
#include <string.h>

simple_kpf_status_v1 simple_kpf_plugin_v1(
    const simple_kpf_interface_query_v1 *, simple_kpf_interface_answer_v1 *);
uint64_t simple_kpf_example_context_v1(void);

int main(void) {
    simple_kpf_interface_query_v1 query;
    simple_kpf_interface_answer_v1 answer;
    uint64_t session = 0;
    uint8_t output_bytes[16];
    const char input_bytes[] = "hello-kpf";
    simple_kpf_borrowed_bytes_v1 empty = simple_kpf_borrow_v1(NULL, 0);
    simple_kpf_borrowed_bytes_v1 input =
        simple_kpf_borrow_v1(input_bytes, sizeof(input_bytes));
    simple_kpf_output_buffer_v1 output =
        simple_kpf_output_v1(output_bytes, sizeof(output_bytes));
    memset(&query, 0, sizeof(query));
    query.abi_version = SIMPLE_KPF_ABI_V1;
    query.struct_size = (uint32_t)sizeof(query);
    query.interface_major = 1;
    query.required_operation_mask = 1;
    assert(simple_kpf_plugin_v1(&query, &answer) == SIMPLE_KPF_STATUS_OK);
    assert(answer.operation_table->open_session(
               simple_kpf_example_context_v1(), &empty, &session) ==
           SIMPLE_KPF_STATUS_OK);
    simple_kpf_call_header_v1 call = simple_kpf_call_v1(1, session, 1, 0, 0, 0);
    assert(answer.operation_table->submit_batch(
               simple_kpf_example_context_v1(), &call, &input, &output) ==
           SIMPLE_KPF_STATUS_OK);
    assert(output.used == sizeof(input_bytes));
    assert(memcmp(output_bytes, input_bytes, sizeof(input_bytes)) == 0);
    assert(answer.operation_table->close_session(
               simple_kpf_example_context_v1(), session) ==
           SIMPLE_KPF_STATUS_REJECTED);
    assert(answer.operation_table->quiesce(
               simple_kpf_example_context_v1(), session, 0, 0) ==
           SIMPLE_KPF_STATUS_OK);
    assert(answer.operation_table->close_session(
               simple_kpf_example_context_v1(), session) ==
           SIMPLE_KPF_STATUS_OK);
    return 0;
}
