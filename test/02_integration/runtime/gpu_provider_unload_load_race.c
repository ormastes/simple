#define _POSIX_C_SOURCE 200809L

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include "simple_gpu_provider_abi_v1.h"

#ifdef SIMPLE_GPU_RACE_PROVIDER

#ifndef SIMPLE_GPU_RACE_IDENTITY
#define SIMPLE_GPU_RACE_IDENTITY 7001
#endif

static int64_t operation_stub(void) { return 1; }
static SimpleGpuOperationV1 operations[SIMPLE_GPU_OP_COUNT];
static SimpleGpuProviderAbiV1 table;

static SimpleGpuStatusV1 provider_shutdown(void) {
#ifdef SIMPLE_GPU_RACE_SLOW_SHUTDOWN
    const char *marker = getenv("SIMPLE_GPU_RACE_MARKER");
    struct timespec pause = {0, 200000000};
    FILE *file = marker ? fopen(marker, "wb") : NULL;
    if (file) fclose(file);
    nanosleep(&pause, NULL);
#endif
    return SIMPLE_GPU_STATUS_OK;
}

static SimpleGpuStatusV1 session_open(
        uint64_t backend, uint64_t device, SimpleGpuHandleV1 *out) {
    if (backend != SIMPLE_GPU_BACKEND_VULKAN || !out)
        return SIMPLE_GPU_STATUS_INVALID;
    *out = device + 1;
    return SIMPLE_GPU_STATUS_OK;
}

static SimpleGpuStatusV1 handle_close(SimpleGpuHandleV1 handle) {
    return handle ? SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}

static SimpleGpuStatusV1 handle_release(
        SimpleGpuHandleV1 session, SimpleGpuHandleV1 handle) {
    return session && handle ? SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}

static SimpleGpuStatusV1 submit(
        SimpleGpuHandleV1 session, const SimpleGpuSubmitV1 *request,
        SimpleGpuHandleV1 *out) {
    if (!session || !request || !out) return SIMPLE_GPU_STATUS_INVALID;
    *out = request->correlation_id + 1;
    return SIMPLE_GPU_STATUS_OK;
}

static SimpleGpuStatusV1 wait_done(
        SimpleGpuHandleV1 session, SimpleGpuHandleV1 completion,
        uint64_t timeout_ns, SimpleGpuReceiptV1 *receipt) {
    return session && completion && timeout_ns && receipt ?
        SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}

static SimpleGpuStatusV1 readback(
        SimpleGpuHandleV1 session, SimpleGpuHandleV1 resource,
        SimpleGpuBytesV1 *bytes) {
    return session && resource && bytes ?
        SIMPLE_GPU_STATUS_OK : SIMPLE_GPU_STATUS_INVALID;
}

static SimpleGpuStatusV1 resource_alloc(
        SimpleGpuHandleV1 session, const SimpleGpuResourceDescV1 *desc,
        SimpleGpuHandleV1 *out) {
    if (!session || !desc || !out) return SIMPLE_GPU_STATUS_INVALID;
    *out = desc->size_bytes + 1;
    return SIMPLE_GPU_STATUS_OK;
}

__attribute__((visibility("default")))
const SimpleGpuProviderAbiV1 *simple_gpu_provider_query_v1(void) {
    static int initialized;
    uint32_t index;
    if (!initialized) {
        for (index = 0; index < SIMPLE_GPU_OP_COUNT; index++)
            operations[index] = (SimpleGpuOperationV1)operation_stub;
        table.struct_size = sizeof(table);
        table.abi_major = SIMPLE_GPU_PROVIDER_ABI_MAJOR;
        table.abi_minor = SIMPLE_GPU_PROVIDER_ABI_MINOR;
        table.backend_bits = SIMPLE_GPU_BACKEND_VULKAN;
        table.capability_bits = SIMPLE_GPU_CAP_DEVICE_READBACK |
            SIMPLE_GPU_CAP_ASYNC_COMPLETION;
        table.provider_identity = SIMPLE_GPU_RACE_IDENTITY;
        table.operation_count = SIMPLE_GPU_OP_COUNT;
        table.operations = operations;
        table.shutdown = provider_shutdown;
        table.session_open = session_open;
        table.session_close = handle_close;
        table.submit = submit;
        table.wait = wait_done;
        table.readback = readback;
        table.resource_alloc = resource_alloc;
        table.resource_release = handle_release;
        table.completion_release = handle_release;
        initialized = 1;
    }
    return &table;
}

#else

#include <pthread.h>
#include <unistd.h>

int64_t rt_gpu_provider_loaded(int64_t backend);
int64_t rt_gpu_provider_identity(int64_t backend);
int64_t rt_gpu_provider_unload(int64_t backend);

static int64_t unload_result;

static void *unload_worker(void *unused) {
    (void)unused;
    unload_result = rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN);
    return NULL;
}

int main(int argc, char **argv) {
    pthread_t worker;
    struct timespec poll = {0, 1000000};
    int attempts = 0;
    if (argc != 4 || setenv("SIMPLE_GPU_RACE_MARKER", argv[3], 1) != 0 ||
            setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1) != 0)
        return 2;
    unlink(argv[3]);
    if (rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 1 ||
            rt_gpu_provider_identity(SIMPLE_GPU_BACKEND_VULKAN) != 7001)
        return 3;
    if (setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[2], 1) != 0 ||
            pthread_create(&worker, NULL, unload_worker, NULL) != 0)
        return 4;
    while (access(argv[3], F_OK) != 0 && attempts++ < 5000)
        nanosleep(&poll, NULL);
    if (access(argv[3], F_OK) != 0 ||
            rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 0)
        return 5;
    if (pthread_join(worker, NULL) != 0 || unload_result != 1)
        return 6;
    if (rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 1 ||
            rt_gpu_provider_identity(SIMPLE_GPU_BACKEND_VULKAN) != 7002 ||
            rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN) != 1)
        return 7;
    puts("gpu_provider_unload_load_race=pass closing_admission_rejected=true replacement_after_close=true");
    return 0;
}

#endif
