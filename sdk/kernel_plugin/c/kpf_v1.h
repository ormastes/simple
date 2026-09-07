#ifndef SIMPLE_SDK_KERNEL_PLUGIN_C_KPF_V1_H
#define SIMPLE_SDK_KERNEL_PLUGIN_C_KPF_V1_H

#include "../../../include/simple_kernel_plugin_v1.h"

#include <string.h>

static inline simple_kpf_borrowed_bytes_v1 simple_kpf_borrow_v1(
    const void *data,
    uint64_t size) {
    simple_kpf_borrowed_bytes_v1 value;
    memset(&value, 0, sizeof(value));
    value.abi_version = SIMPLE_KPF_ABI_V1;
    value.struct_size = (uint32_t)sizeof(value);
    value.data = (const uint8_t *)data;
    value.size = size;
    return value;
}

static inline simple_kpf_output_buffer_v1 simple_kpf_output_v1(
    void *data,
    uint64_t capacity) {
    simple_kpf_output_buffer_v1 value;
    memset(&value, 0, sizeof(value));
    value.abi_version = SIMPLE_KPF_ABI_V1;
    value.struct_size = (uint32_t)sizeof(value);
    value.data = (uint8_t *)data;
    value.capacity = capacity;
    return value;
}

static inline simple_kpf_call_header_v1 simple_kpf_call_v1(
    uint64_t generation,
    uint64_t session,
    uint64_t request,
    uint32_t interface_slot,
    uint32_t operation_slot,
    uint64_t deadline_ns) {
    simple_kpf_call_header_v1 value;
    memset(&value, 0, sizeof(value));
    value.abi_version = SIMPLE_KPF_ABI_V1;
    value.struct_size = (uint32_t)sizeof(value);
    value.generation = generation;
    value.session = session;
    value.request = request;
    value.interface_slot = interface_slot;
    value.operation_slot = operation_slot;
    value.deadline_ns = deadline_ns;
    return value;
}

#endif
