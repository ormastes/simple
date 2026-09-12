#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "simple_gpu_provider_abi_v1.h"

static uint64_t checksum_v1(const uint8_t *bytes, uint64_t length) {
    uint64_t value = UINT64_C(14695981039346656037), i;
    for (i = 0; i < length; i++) { value ^= bytes[i]; value *= UINT64_C(1099511628211); }
    return value;
}

#ifdef SIMPLE_GPU_ABI_PROVIDER
static SimpleGpuOperationV1 operations[SIMPLE_GPU_OP_COUNT];
static SimpleGpuProviderAbiV1 table;
static uint8_t resource_bytes[64];
static uint64_t resource_size;
static int64_t operation_stub(void) { return 1; }
static SimpleGpuStatusV1 shutdown_v1(void) { return SIMPLE_GPU_STATUS_OK; }
static SimpleGpuStatusV1 session_open_v1(uint64_t backend, uint64_t device,
        SimpleGpuHandleV1 *out) {
    if (backend != SIMPLE_GPU_BACKEND_VULKAN || device != 3 || !out)
        return SIMPLE_GPU_STATUS_INVALID;
    *out = 101; return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 session_close_v1(SimpleGpuHandleV1 session) {
    return session == 101 ? SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}
static SimpleGpuStatusV1 resource_alloc_v1(SimpleGpuHandleV1 session,
        const SimpleGpuResourceDescV1 *desc, SimpleGpuHandleV1 *out) {
    uint64_t i;
    if (session != 101 || !desc || !out || desc->struct_size != sizeof(*desc) ||
            desc->size_bytes == 0 || desc->size_bytes > sizeof(resource_bytes))
        return SIMPLE_GPU_STATUS_INVALID;
    resource_size = desc->size_bytes;
    for (i = 0; i < resource_size; i++) resource_bytes[i] = (uint8_t)(i + 1);
    *out = 202; return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 resource_release_v1(SimpleGpuHandleV1 session,
        SimpleGpuHandleV1 resource) {
    if (session != 101 || resource != 202) return SIMPLE_GPU_STATUS_INVALID;
    resource_size = 0; return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 submit_v1(SimpleGpuHandleV1 session,
        const SimpleGpuSubmitV1 *request, SimpleGpuHandleV1 *out) {
    if (session != 101 || !request || !out || request->struct_size != sizeof(*request) ||
            !request->data || request->length != 4 || request->correlation_id != 909)
        return SIMPLE_GPU_STATUS_INVALID;
    if (request->output_resource != 202) return SIMPLE_GPU_STATUS_INVALID;
    *out = 303; return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 wait_v1(SimpleGpuHandleV1 session,
        SimpleGpuHandleV1 completion, uint64_t timeout_ns, SimpleGpuReceiptV1 *receipt) {
    if (session != 101 || completion != 303 || !timeout_ns || !receipt)
        return SIMPLE_GPU_STATUS_INVALID;
    *receipt = (SimpleGpuReceiptV1){sizeof(*receipt), SIMPLE_GPU_STATUS_OK,
        909, 7001, 3, 202, checksum_v1(resource_bytes, resource_size), 77};
    return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 readback_v1(SimpleGpuHandleV1 session,
        SimpleGpuHandleV1 resource, SimpleGpuBytesV1 *bytes) {
    if (session != 101 || resource != 202 || !bytes || !bytes->data ||
            bytes->length < resource_size) return SIMPLE_GPU_STATUS_INVALID;
    memcpy(bytes->data, resource_bytes, resource_size);
    bytes->length = resource_size;
    return SIMPLE_GPU_STATUS_OK;
}
static SimpleGpuStatusV1 completion_release_v1(SimpleGpuHandleV1 session,
        SimpleGpuHandleV1 completion) {
    return session == 101 && completion == 303 ?
        SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}
__attribute__((visibility("default")))
const SimpleGpuProviderAbiV1 *simple_gpu_provider_query_v1(void) {
    static int initialized;
    if (!initialized) {
        operations[0] = operation_stub;
        table = (SimpleGpuProviderAbiV1){sizeof(table),
            SIMPLE_GPU_PROVIDER_ABI_MAJOR, SIMPLE_GPU_PROVIDER_ABI_MINOR,
            SIMPLE_GPU_BACKEND_VULKAN,
            SIMPLE_GPU_CAP_DEVICE_READBACK | SIMPLE_GPU_CAP_ASYNC_COMPLETION,
            7001, SIMPLE_GPU_OP_COUNT, 0, operations, shutdown_v1,
            session_open_v1, session_close_v1, submit_v1, wait_v1, readback_v1,
            resource_alloc_v1, resource_release_v1, completion_release_v1};
        initialized = 1;
    }
    return &table;
}
#else
int64_t rt_gpu_provider_loaded(int64_t);
int64_t rt_gpu_provider_identity(int64_t);
int64_t rt_gpu_provider_capability_bits(int64_t);
int64_t rt_gpu_provider_generation(int64_t);
int64_t rt_gpu_provider_session_open(int64_t, int64_t);
int64_t rt_gpu_provider_session_close(int64_t, int64_t);
int64_t rt_gpu_provider_resource_alloc(int64_t, int64_t, int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_resource_release(int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_submit_raw(int64_t, int64_t, int64_t, int64_t, int64_t,
        int64_t, int64_t);
int64_t rt_gpu_provider_wait_raw(int64_t, int64_t, int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_readback_raw(int64_t, int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_completion_release(int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_device_image_authority_word(
        int64_t, int64_t, int64_t, int64_t);
int64_t rt_gpu_provider_unload(int64_t);

int main(int argc, char **argv) {
    int64_t session, resource, completion;
    uint8_t input[4] = {9, 8, 7, 6}, output[16] = {0}, expected[16];
    uint64_t i;
    SimpleGpuReceiptV1 receipt = {.struct_size = sizeof(receipt)};
    SimpleGpuBytesV1 bytes = {.struct_size = sizeof(bytes), .data = output,
        .length = sizeof(output)};
    if (argc != 3 || setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1) ||
            setenv("SIMPLE_VULKAN_PROVIDER_SHA256", argv[2], 1)) return 2;
    if (!rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) ||
            rt_gpu_provider_identity(SIMPLE_GPU_BACKEND_VULKAN) != 7001 ||
            rt_gpu_provider_capability_bits(SIMPLE_GPU_BACKEND_VULKAN) != 3 ||
            rt_gpu_provider_generation(SIMPLE_GPU_BACKEND_VULKAN) <= 0) return 3;
    session = rt_gpu_provider_session_open(SIMPLE_GPU_BACKEND_VULKAN, 3);
    if (!session || rt_gpu_provider_device_image_authority_word(
            SIMPLE_GPU_BACKEND_VULKAN, session, 1, 0) != 0) return 8;
    resource = rt_gpu_provider_resource_alloc(SIMPLE_GPU_BACKEND_VULKAN,
        session, sizeof(output), 0, 1);
    for (i = 0; i < sizeof(expected); i++) expected[i] = (uint8_t)(i + 1);
    completion = rt_gpu_provider_submit_raw(SIMPLE_GPU_BACKEND_VULKAN,
        session, resource, 1, (int64_t)(uintptr_t)input, sizeof(input), 909);
    if (!session || !resource || !completion ||
            rt_gpu_provider_submit_raw(SIMPLE_GPU_BACKEND_VULKAN, session,
                resource, 1, (int64_t)(uintptr_t)input, sizeof(input), 910) != 0 ||
            rt_gpu_provider_resource_release(SIMPLE_GPU_BACKEND_VULKAN,
                session, resource) != SIMPLE_GPU_STATUS_BUSY ||
            rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN) != 0) return 4;
    if (rt_gpu_provider_wait_raw(SIMPLE_GPU_BACKEND_VULKAN, session, completion,
            1000000, (int64_t)(uintptr_t)&receipt) != SIMPLE_GPU_STATUS_OK ||
            receipt.checksum != checksum_v1(expected, sizeof(expected)) ||
            receipt.device_elapsed_ns != 77 ||
            rt_gpu_provider_wait_raw(SIMPLE_GPU_BACKEND_VULKAN, session, completion,
                1000000, (int64_t)(uintptr_t)&receipt) != SIMPLE_GPU_STATUS_INVALID) return 5;
    if (rt_gpu_provider_readback_raw(SIMPLE_GPU_BACKEND_VULKAN, session, resource,
            (int64_t)(uintptr_t)&bytes) != SIMPLE_GPU_STATUS_OK ||
            bytes.length != sizeof(output) || output[0] != 1 || output[15] != 16) return 6;
    if (rt_gpu_provider_completion_release(SIMPLE_GPU_BACKEND_VULKAN, session, completion) ||
            rt_gpu_provider_completion_release(SIMPLE_GPU_BACKEND_VULKAN, session, completion)
                != SIMPLE_GPU_STATUS_INVALID ||
            rt_gpu_provider_resource_release(SIMPLE_GPU_BACKEND_VULKAN, session, resource) ||
            rt_gpu_provider_session_close(SIMPLE_GPU_BACKEND_VULKAN, session) ||
            !rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN)) return 7;
    puts("gpu_provider_abi_lifetime_v1=pass authenticated=true exact_once=true retained_unload=true");
    return 0;
}
#endif
