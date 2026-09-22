/* Exact extracted runtime adapter + typed synthetic provider. No GPU claim. */
#include <stdint.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>
#define SIMPLE_GPU_BACKEND_CUDA 1
typedef struct { void *symbol; } SimpleGpuCallPinV1;
static int available = 1, acquired, released, provider_calls, launch_calls;
static int64_t scratch[42];
static int expected_args = 3;

static int64_t provider_bytes(int64_t ptr, int64_t length) {
    ++provider_calls;
    if (!ptr || length <= 0) return -1;
    if (length != 3) return -9;
    return memcmp((const void *)(intptr_t)ptr, "abc", 3) == 0 ? 44 : -99;
}
static int simple_gpu_call_acquire_v1(int backend, const char *name, SimpleGpuCallPinV1 *pin) {
    assert(backend == SIMPLE_GPU_BACKEND_CUDA);
    assert(strcmp(name, "rt_cuda_module_load_data_bytes") == 0);
    if (!available) return 0;
    ++acquired;
    pin->symbol = (void *)provider_bytes;
    return 1;
}
static void simple_gpu_call_release_v1(SimpleGpuCallPinV1 *pin) {
    assert(pin->symbol == (void *)provider_bytes);
    ++released;
}
#include "cuda_span_adapter.inc"

int64_t fixture_scratch(void) {
    scratch[40] = 31337;
    scratch[41] = -31337;
    return (int64_t)(intptr_t)scratch;
}
void fixture_expected_args(int64_t count) { expected_args = (int)count; }
int64_t fixture_launch_calls(void) { return launch_calls; }
void fixture_available(int64_t value) { available = value != 0; }
int64_t rt_cuda_launch_kernel(int64_t module, const uint8_t *name, uint64_t length,
    int64_t gx, int64_t gy, int64_t gz, int64_t bx, int64_t by, int64_t bz, int64_t args) {
    ++launch_calls;
    assert(module == 44 && length == 3 && memcmp(name, "abc", 3) == 0);
    assert(gx == 1 && gy == 2 && gz == 3 && bx == 4 && by == 5 && bz == 6);
    assert(args == (int64_t)(intptr_t)&scratch[20]);
    int64_t **pointers = (int64_t **)(intptr_t)args;
    assert(pointers[0] == &scratch[0] && *pointers[0] == 17);
    assert(pointers[1] == &scratch[1] && *pointers[1] == -23);
    assert(pointers[2] == &scratch[2] && *pointers[2] == 4096);
    for (int n = 3; n < expected_args; ++n)
        assert(pointers[n] == &scratch[n] && *pointers[n] == n + 1);
    assert(scratch[40] == 31337 && scratch[41] == -31337);
    return available ? 0 : -3;
}
#ifdef CUDA_NATIVE_BOUNDARY
extern int64_t caller__cuda_native_boundary_check(void);
#endif
int main(void) {
#ifndef CUDA_NATIVE_BOUNDARY
    assert(rt_cuda_module_load_data((const uint8_t *)"abc", 3) == 44);
    int calls_before = provider_calls;
    int pins_before = acquired;
    assert(rt_cuda_module_load_data((const uint8_t *)"abc", UINT64_MAX) == -1);
    assert(provider_calls == calls_before && acquired == pins_before);
    assert(rt_cuda_module_load_data((const uint8_t *)"abc", (uint64_t)INT64_MAX) == -9);
    assert(rt_cuda_module_load_data(NULL, 0) == -1);
    available = 0;
    assert(rt_cuda_module_load_data((const uint8_t *)"abc", 3) == -3);
    available = 1;
    clock_t start = clock();
    for (int n = 0; n < 10000; ++n)
        assert(rt_cuda_module_load_data((const uint8_t *)"abc", 3) == 44);
    assert(acquired == released);
    printf("span-cases=5 warmed_calls=10000 cpu_seconds=%.6f leases_balanced=1\n",
        (double)(clock() - start) / CLOCKS_PER_SEC);
#else
    assert(caller__cuda_native_boundary_check() == 0);
    assert(acquired == released);
    puts("compiled-simple-span-and-argument-boundary=PASS");
#endif
    return 0;
}
