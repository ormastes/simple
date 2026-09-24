/* Synthetic ABI provider test, not GPU/device-execution evidence. */
#include <stdint.h>
#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#if defined(TEST_CUDA_PROVIDER) || defined(TEST_VULKAN_PROVIDER)
#ifndef TEST_PROVIDER_ABI
#define TEST_PROVIDER_ABI 1
#endif
int64_t rt_simple_gpu_provider_abi_version(void) { return TEST_PROVIDER_ABI; }
#define REQUIRED(name) int64_t name(void) { return 0; }
#ifdef TEST_CUDA_PROVIDER
int64_t rt_simple_gpu_provider_backend_bits(void) { return 1; }
int64_t rt_cuda_provider_available(void) { return 1; }
int64_t rt_cuda_provider_device_count(void) { return 1; }
int64_t rt_cuda_init(void) { return 0; }
int64_t rt_cuda_device_get(int64_t ordinal) { return ordinal == 2 ? 41 : -99; }
int64_t rt_cuda_device_identity(int64_t device) { return device == 41 ? 901 : 0; }
int64_t rt_cuda_ctx_create(int64_t device) { return device == 41 ? 42 : -99; }
int64_t rt_cuda_ctx_destroy(int64_t ctx) { return ctx == 42 ? 0 : -99; }
int64_t rt_cuda_mem_alloc(int64_t count) { return count == 3 ? 43 : -99; }
int64_t rt_cuda_mem_free(int64_t ptr) { return ptr == 43 ? 0 : -99; }
int64_t rt_cuda_module_unload(int64_t module) { return module == 44 ? 0 : -99; }
int64_t rt_cuda_module_get_function(int64_t module, const char *name) {
    return module == 44 && strcmp(name, "abc") == 0 ? 45 : -99;
}
const char *rt_cuda_device_name(int64_t device) { return device == 41 ? "fixture-cuda" : "bad-device"; }
const char *rt_cuda_get_error_string(int64_t code) { (void)code; return "fixture-error"; }
int64_t rt_cuda_sync(void) { return 0; }
int64_t rt_cuda_memcpy_dtoh(int64_t dst, int64_t src, int64_t size) {
    if (src != 43 || size != 3) return -99;
    memcpy((void *)(intptr_t)dst, "abc", 3); return 0;
}
#ifndef TEST_OMIT_REQUIRED
int64_t rt_cuda_memcpy_htod(int64_t dst, int64_t src, int64_t size) {
    return dst == 43 && size == 2 && memcmp((void *)(intptr_t)src, "ab", 2) == 0 ? 0 : -99;
}
#endif
int64_t rt_cuda_module_load_data_bytes(int64_t ptr, int64_t size) {
    return size == 3 && memcmp((void *)(intptr_t)ptr, "abc", 3) == 0 ? 44 : -99;
}
int64_t rt_cuda_launch_kernel_name(int64_t module, int64_t name, int64_t length,
        int64_t gx, int64_t gy, int64_t gz, int64_t bx, int64_t by, int64_t bz, int64_t args) {
    return module == 44 && length == 3 && memcmp((void *)(intptr_t)name, "abc", 3) == 0 &&
        gx == 1 && gy == 2 && gz == 3 && bx == 4 && by == 5 && bz == 6 && args == 47 ? 0 : -99;
}
int64_t rt_cuda_device_compute_capability(int64_t device) { return device == 41 ? 80 : -99; }
int64_t rt_cuda_ctx_set_current(int64_t ctx) { return ctx == 42 ? 0 : -99; }
int64_t rt_cuda_ctx_synchronize(void) { return 0; }
int64_t rt_cuda_memcpy_dtod(int64_t dst, int64_t src, int64_t len) { return dst == 43 && src == 44 && len == 3 ? 0 : -99; }
int64_t rt_cuda_memset(int64_t dst, int64_t byte, int64_t len) { return dst == 43 && byte == 7 && len == 3 ? 0 : -99; }
int64_t rt_cuda_module_load(const uint8_t *path, uint64_t len) { return len == 3 && memcmp(path, "abc", 3) == 0 ? 46 : -99; }
REQUIRED(rt_cuda_memset_d32)
#else
int64_t rt_simple_gpu_provider_backend_bits(void) { return 2; }
int64_t rt_vulkan_provider_is_available(void) { return 1; }
int64_t rt_vulkan_provider_device_count(void) { return 1; }
int32_t rt_vk_provider_available(void) { return 1; }
int64_t rt_vulkan_compile_spirv_raw(int64_t ptr, int64_t count) {
    return count == 3 && memcmp((void *)(intptr_t)ptr, "abc", 3) == 0 ? 51 : 0;
}
int64_t rt_vulkan_copy_to_buffer_raw(int64_t handle, int64_t ptr, int64_t count, int64_t offset) {
    return handle == 52 && offset == 7 && count >= 2 && count <= 3 &&
        memcmp((void *)(intptr_t)ptr, "abc", (size_t)count) == 0;
}
REQUIRED(rt_vulkan_init)
REQUIRED(rt_vulkan_shutdown)
REQUIRED(rt_vulkan_select_device)
REQUIRED(rt_vulkan_alloc_buffer)
REQUIRED(rt_vulkan_free_buffer)
REQUIRED(rt_vulkan_copy_from_buffer_raw)
REQUIRED(rt_vulkan_copy_from_buffer_strided_raw)
REQUIRED(rt_vulkan_copy_from_buffer_regions_raw)
REQUIRED(rt_vulkan_destroy_shader)
REQUIRED(rt_vulkan_create_compute_pipeline_raw)
REQUIRED(rt_vulkan_destroy_pipeline)
REQUIRED(rt_vulkan_create_descriptor_set)
REQUIRED(rt_vulkan_bind_buffer)
REQUIRED(rt_vulkan_destroy_descriptor_set)
REQUIRED(rt_vulkan_begin_compute)
REQUIRED(rt_vulkan_bind_pipeline)
REQUIRED(rt_vulkan_bind_descriptors)
REQUIRED(rt_vulkan_push_constants_raw)
REQUIRED(rt_vulkan_dispatch)
REQUIRED(rt_vulkan_end_compute)
REQUIRED(rt_vulkan_discard_command)
REQUIRED(rt_vulkan_fence_submission_supported)
REQUIRED(rt_vulkan_accepted_compute_submit_count)
REQUIRED(rt_vulkan_submit_and_wait_fence)
REQUIRED(rt_vulkan_submit_no_wait)
REQUIRED(rt_vulkan_wait_fence)
REQUIRED(rt_vulkan_destroy_fence)
REQUIRED(rt_vulkan_wait_idle)
REQUIRED(rt_vulkan_device_name)
REQUIRED(rt_vulkan_device_type)
REQUIRED(rt_vulkan_selected_device_type)
REQUIRED(rt_vulkan_device_driver_identity)
REQUIRED(rt_vulkan_selected_device_driver_identity)
REQUIRED(rt_vulkan_selected_device_driver_identity_hash)
REQUIRED(rt_vulkan_get_last_error)
REQUIRED(rt_vulkan_init_headless_present)
REQUIRED(rt_vulkan_init_window_present)
REQUIRED(rt_vulkan_init_external_window_present)
REQUIRED(rt_vulkan_present_buffer)
REQUIRED(rt_vulkan_present_buffer_regions_raw)
REQUIRED(rt_vulkan_last_present_copy_bytes)
REQUIRED(rt_vulkan_last_present_copy_rects)
REQUIRED(rt_vulkan_destroy_swapchain)
#endif
#else
#include "runtime.h"
int64_t rt_cuda_init(void);
int64_t rt_cuda_device_get(int64_t);
int64_t rt_cuda_device_identity(int64_t);
const char *rt_cuda_device_name(int64_t);
int64_t rt_cuda_ctx_create(int64_t);
int64_t rt_cuda_ctx_destroy(int64_t);
int64_t rt_cuda_mem_alloc(int64_t);
int64_t rt_cuda_mem_free(int64_t);
int64_t rt_cuda_memcpy_dtoh(int64_t,int64_t,int64_t);
int64_t rt_cuda_memcpy_htod_array(int64_t,int64_t,int64_t);
int64_t rt_cuda_module_load_data_array(int64_t);
int64_t rt_cuda_module_unload(int64_t);
int64_t rt_cuda_module_get_function(int64_t,int64_t);
int64_t rt_cuda_ctx_set_current(int64_t);
int64_t rt_cuda_ctx_synchronize(void);
int64_t rt_cuda_device_compute_capability(int64_t);
const char *rt_cuda_get_error_string(int64_t);
int64_t rt_cuda_memcpy_dtod(int64_t,int64_t,int64_t);
int64_t rt_cuda_memcpy_htod(int64_t,int64_t,int64_t);
int64_t rt_cuda_memset(int64_t,int64_t,int64_t);
int64_t rt_cuda_module_load(const uint8_t *,uint64_t);
int64_t rt_cuda_module_load_data(const uint8_t *,uint64_t);
#ifdef TEST_NATIVE_BOUNDARY
int64_t phase2_native_gpu_check(int64_t good);
#endif
int64_t rt_cuda_launch_kernel(int64_t,const uint8_t *,uint64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_cuda_launch_kernel_name_array(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_cuda_sync(void);
int64_t rt_vulkan_compile_spirv(int64_t);
int64_t rt_vulkan_compile_spirv_array(int64_t);
int64_t rt_vulkan_copy_to_buffer(int64_t,int64_t,int64_t);
int64_t rt_vulkan_copy_to_buffer_array(int64_t,int64_t,int64_t,int64_t);

int main(int argc, char **argv) {
    assert(argc == 4);
    assert(setenv("SIMPLE_CUDA_PROVIDER_PATH", argv[1], 1) == 0);
    assert(setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[2], 1) == 0);
    int good = strcmp(argv[3], "good") == 0;
    SplArray *array = rt_array_new(3);
    for (int i = 0; i < 3; i++) rt_array_push(array, rt_value_int('a' + i));
    int64_t a = (int64_t)(intptr_t)array;
    assert(rt_cuda_init() == (good ? 0 : 3));
    assert(rt_cuda_device_get(2) == (good ? 41 : -3));
    assert(rt_cuda_device_identity(41) == (good ? 901 : 0));
    const char *name = rt_cuda_device_name(41);
    assert(strcmp(name, good ? "fixture-cuda" : "No CUDA") == 0);
    assert(rt_cuda_ctx_create(41) == (good ? 42 : -3));
    assert(rt_cuda_ctx_destroy(42) == (good ? 0 : -3));
    assert(rt_cuda_mem_alloc(3) == (good ? 43 : -3));
    assert(rt_cuda_mem_free(43) == (good ? 0 : -3));
    assert(rt_cuda_module_load_data_array(a) == (good ? 44 : -3));
    int64_t function_name = rt_string_new((const uint8_t *)"abc", 3);
    assert(rt_cuda_module_get_function(44, function_name) == (good ? 45 : -3));
    assert(rt_cuda_module_get_function(44, rt_string_new((const uint8_t *)"a\0c", 3)) == -1);
    assert(rt_cuda_module_unload(44) == (good ? 0 : -3));
    assert(rt_cuda_memcpy_htod_array(43, a, 2) == (good ? 0 : -3));
    char out[4] = {0};
    assert(rt_cuda_memcpy_dtoh((int64_t)(intptr_t)out, 43, 3) == (good ? 0 : -3));
    assert(strcmp(out, good ? "abc" : "") == 0);
    assert(rt_cuda_launch_kernel(44, (const uint8_t *)"abc", 3, 1,2,3,4,5,6,47) == (good ? 0 : -3));
    assert(rt_cuda_launch_kernel_name_array(44, a, 1,2,3,4,5,6,47) == (good ? 0 : -3));
    assert(rt_cuda_sync() == (good ? 0 : -3));
    assert(rt_cuda_ctx_set_current(42) == (good ? 0 : -3));
    assert(rt_cuda_ctx_synchronize() == (good ? 0 : -3));
    assert(rt_cuda_device_compute_capability(41) == (good ? 80 : 0));
    const char *error = rt_cuda_get_error_string(-3);
    assert(strcmp(error, good ? "fixture-error" : "CUDA_ERROR_NOT_INITIALIZED") == 0);
    assert(rt_cuda_memcpy_dtod(43,44,3) == (good ? 0 : -3));
    assert(rt_cuda_memcpy_htod(43,(int64_t)(intptr_t)"abc",2) == (good ? 0 : -3));
    assert(rt_cuda_memset(43,7,3) == (good ? 0 : -3));
    assert(rt_cuda_module_load((const uint8_t *)"abc",3) == (good ? 46 : -3));
    assert(rt_cuda_module_load_data((const uint8_t *)"abc",3) == (good ? 44 : -3));
    assert(rt_vulkan_compile_spirv(a) == (good ? 51 : 0));
    assert(rt_vulkan_compile_spirv_array(a) == (good ? 51 : 0));
    assert(rt_vulkan_copy_to_buffer(52, a, 7) == good);
    assert(rt_vulkan_copy_to_buffer_array(52, a, 2, 7) == good);
    assert(rt_gpu_provider_loaded(1) == good && rt_gpu_provider_loaded(2) == good);
    SplArray *packed = rt_byte_array_new_len(3);
    assert(rt_array_bytes_store_checked((int64_t)(intptr_t)packed, (const uint8_t *)"abc", 3) == 3);
    assert(rt_cuda_module_load_data_array((int64_t)(intptr_t)packed) == (good ? 44 : -3));
    assert(rt_vulkan_compile_spirv_array((int64_t)(intptr_t)packed) == (good ? 51 : 0));
    int64_t copied[3] = {-9,-9,-9};
    assert(rt_array_i64_validate(a) == 3);
    assert(rt_array_i64_copy_checked(a, copied, 2) == -22 && copied[0] == -9);
    assert(rt_array_i64_copy_checked(a, copied, 3) == 3 && copied[0] == 97 && copied[2] == 99);
    assert(rt_array_i64_validate((int64_t)(intptr_t)packed) == -22);
    assert(rt_array_i64_validate(0x10001) == -22);
    assert(rt_array_i64_copy_checked(0x10001, copied, 3) == -22);
    rt_array_set(array, 1, function_name);
    assert(rt_array_i64_validate(a) == -22);
    rt_array_set(array, 1, rt_value_int(98));
#ifdef TEST_NATIVE_BOUNDARY
    assert(phase2_native_gpu_check(good) == 0);
#endif
    assert(rt_cuda_memcpy_htod_array(43, a, 4) == -1);
    assert(rt_cuda_memcpy_htod_array(43, a, -1) == -1);
    assert(rt_vulkan_copy_to_buffer_array(52, a, 4, 7) == 0);
    assert(rt_vulkan_copy_to_buffer_array(52, a, 2, -1) == 0);
    rt_array_set(array, 1, rt_value_int(0));
    assert(rt_cuda_launch_kernel_name_array(44, a, 1,2,3,4,5,6,47) == -1);
    rt_array_set(array, 1, rt_value_int(256));
    assert(rt_cuda_module_load_data_array(a) == -1);
    assert(rt_vulkan_compile_spirv_array(a) == 0);
    if (good) {
        assert(rt_cuda_device_get(3) == -99);
        assert(rt_cuda_launch_kernel(44, (const uint8_t *)"abc", 3, 1,2,3,4,5,7,47) == -99);
        assert(rt_gpu_provider_unload(1) == 1);
        assert(strcmp(name, "fixture-cuda") == 0); /* copied before lease release */
        assert(strcmp(error, "fixture-error") == 0);
        assert(rt_gpu_provider_unload(2) == 1);
    }
    rt_array_free(array);
    rt_array_free(packed);
    puts(good ? "phase2-gpu-loader: provider forwarding PASS" : "phase2-gpu-loader: unavailable PASS");
    return 0;
}
#endif
