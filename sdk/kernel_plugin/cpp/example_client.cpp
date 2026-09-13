#include "kpf_v1.hpp"

#include <cassert>
#include <cstring>
#include <type_traits>

extern "C" simple_kpf_status_v1 simple_kpf_plugin_v1(
    const simple_kpf_interface_query_v1 *, simple_kpf_interface_answer_v1 *);
extern "C" std::uint64_t simple_kpf_example_context_v1(void);

int main() {
    static_assert(!std::is_copy_constructible_v<simple::kpf::Session>);
    static_assert(std::is_nothrow_move_constructible_v<simple::kpf::Session>);
    static_assert(std::is_nothrow_destructible_v<simple::kpf::Session>);

    simple_kpf_interface_query_v1 query{};
    simple_kpf_interface_answer_v1 answer{};
    query.abi_version = SIMPLE_KPF_ABI_V1;
    query.struct_size = sizeof(query);
    query.interface_major = 1;
    query.required_operation_mask = 1;
    assert(simple_kpf_plugin_v1(&query, &answer) == SIMPLE_KPF_STATUS_OK);

    auto configuration = simple_kpf_borrow_v1(nullptr, 0);
    simple::kpf::Session session;
    assert(simple::kpf::Session::open(*answer.operation_table,
                                     simple_kpf_example_context_v1(),
                                     configuration, session) ==
           SIMPLE_KPF_STATUS_OK);

    simple::kpf::Session moved = static_cast<simple::kpf::Session &&>(session);
    assert(!session.active());
    assert(moved.active());

    const char input_bytes[] = "cpp-raii";
    std::uint8_t output_bytes[16]{};
    auto input = simple_kpf_borrow_v1(input_bytes, sizeof(input_bytes));
    auto output = simple_kpf_output_v1(output_bytes, sizeof(output_bytes));
    assert(moved.submit(1, 7, 0, 0, 0, input, output) == SIMPLE_KPF_STATUS_OK);
    assert(output.used == sizeof(input_bytes));
    assert(std::memcmp(output_bytes, input_bytes, sizeof(input_bytes)) == 0);
    assert(moved.close() == SIMPLE_KPF_STATUS_REJECTED);
    assert(moved.quiesce(0) == SIMPLE_KPF_STATUS_OK);
    assert(moved.close() == SIMPLE_KPF_STATUS_OK);
    assert(!moved.active());
    return 0;
}
