/* Synthetic raw provider + consumer: ABI evidence, never GPU evidence. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>
#include <time.h>
#include <stdatomic.h>
#include <pthread.h>
#include <sched.h>

#ifdef PHASE2_GPU_READBACK_PROVIDER
int64_t rt_simple_gpu_provider_abi_version(void) { return 1; }
int64_t rt_simple_gpu_provider_backend_bits(void) { return 2; }
static int64_t calls;
static atomic_int entered, released;
int64_t phase2_gpu_vulkan_readback_calls(void) { return calls; }
int phase2_gpu_vulkan_readback_entered(void) { return atomic_load(&entered); }
void phase2_gpu_vulkan_readback_release(void) { atomic_store(&released, 1); }
static uint8_t source(int64_t offset) { return (uint8_t)offset; }
int64_t rt_vulkan_copy_from_buffer_raw(int64_t ptr, int64_t count, int64_t handle, int64_t offset) {
    ++calls;
    assert(ptr && count >= 0 && offset >= 0 && count <= 2097152 && offset <= 2097152 - count);
    if (handle == 55) {
        atomic_store(&entered, 1);
        while (!atomic_load(&released)) sched_yield();
    }
    uint8_t *out = (uint8_t *)(intptr_t)ptr;
    for (int64_t i = 0; i < count; ++i) out[i] = source(offset + i);
    return handle == 51 || handle == 55; /* handle52 deliberately writes then fails */
}
int64_t rt_vulkan_copy_to_buffer_raw(int64_t handle, int64_t ptr, int64_t count, int64_t offset) {
    ++calls;
    const uint8_t expected[] = {1,2,3,4,255,255,255,255,0,0,0,128};
    if (count == 0) return handle == 51 && offset == 0;
    return handle == 51 && offset == 7 && count == 12 &&
        memcmp((const void *)(intptr_t)ptr, expected, sizeof(expected)) == 0;
}
int64_t rt_vulkan_copy_from_buffer_strided_raw(int64_t ptr, int64_t length,
        int64_t handle, int64_t offset, int64_t width, int64_t rows, int64_t stride) {
    ++calls;
    assert(ptr && length == width * rows && rows >= 0 && rows <= 16384);
    uint8_t *out = (uint8_t *)(intptr_t)ptr;
    for (int64_t row = 0; row < rows; ++row)
        for (int64_t col = 0; col < width; ++col) *out++ = source(offset + row * stride + col);
    return handle == 51;
}
static uint64_t field(const uint8_t *bytes) {
    uint64_t n = 0;
    for (int i = 0; i < 8; ++i) n |= (uint64_t)bytes[i] << (i * 8);
    return n;
}
int64_t rt_vulkan_copy_from_buffer_regions_raw(int64_t ptr, int64_t length,
        int64_t handle, int64_t records, int64_t records_len) {
    ++calls;
    assert(ptr && records && records_len > 0 && records_len % 32 == 0);
    uint8_t *out = (uint8_t *)(intptr_t)ptr;
    const uint8_t *record = (const uint8_t *)(intptr_t)records;
    int64_t written = 0;
    for (int64_t i = 0; i < records_len; i += 32) {
        uint64_t offset = field(record + i), width = field(record + i + 8);
        uint64_t rows = field(record + i + 16), stride = field(record + i + 24);
        for (uint64_t row = 0; row < rows; ++row)
            for (uint64_t col = 0; col < width; ++col) {
                assert(written < length);
                out[written++] = source((int64_t)(offset + row * stride + col));
            }
    }
    assert(written == length);
    return handle == 51;
}
/* Required census surfaces not exercised by this focused adapter fixture. */
#define UNUSED_SURFACE(name) int64_t name(void) { abort(); }
UNUSED_SURFACE(rt_vulkan_provider_is_available)
UNUSED_SURFACE(rt_vulkan_provider_device_count)
UNUSED_SURFACE(rt_vk_provider_available)
UNUSED_SURFACE(rt_vulkan_init)
UNUSED_SURFACE(rt_vulkan_shutdown)
UNUSED_SURFACE(rt_vulkan_select_device)
UNUSED_SURFACE(rt_vulkan_alloc_buffer)
UNUSED_SURFACE(rt_vulkan_free_buffer)
UNUSED_SURFACE(rt_vulkan_compile_spirv_raw)
UNUSED_SURFACE(rt_vulkan_destroy_shader)
UNUSED_SURFACE(rt_vulkan_create_compute_pipeline_raw)
UNUSED_SURFACE(rt_vulkan_destroy_pipeline)
UNUSED_SURFACE(rt_vulkan_create_descriptor_set)
UNUSED_SURFACE(rt_vulkan_bind_buffer)
UNUSED_SURFACE(rt_vulkan_destroy_descriptor_set)
UNUSED_SURFACE(rt_vulkan_begin_compute)
UNUSED_SURFACE(rt_vulkan_bind_pipeline)
UNUSED_SURFACE(rt_vulkan_bind_descriptors)
UNUSED_SURFACE(rt_vulkan_push_constants_raw)
UNUSED_SURFACE(rt_vulkan_dispatch)
UNUSED_SURFACE(rt_vulkan_end_compute)
UNUSED_SURFACE(rt_vulkan_discard_command)
UNUSED_SURFACE(rt_vulkan_fence_submission_supported)
UNUSED_SURFACE(rt_vulkan_accepted_compute_submit_count)
UNUSED_SURFACE(rt_vulkan_submit_and_wait_fence)
UNUSED_SURFACE(rt_vulkan_submit_no_wait)
UNUSED_SURFACE(rt_vulkan_wait_fence)
UNUSED_SURFACE(rt_vulkan_destroy_fence)
UNUSED_SURFACE(rt_vulkan_wait_idle)
UNUSED_SURFACE(rt_vulkan_device_name)
UNUSED_SURFACE(rt_vulkan_device_type)
UNUSED_SURFACE(rt_vulkan_selected_device_type)
UNUSED_SURFACE(rt_vulkan_device_driver_identity)
UNUSED_SURFACE(rt_vulkan_selected_device_driver_identity)
UNUSED_SURFACE(rt_vulkan_selected_device_driver_identity_hash)
UNUSED_SURFACE(rt_vulkan_get_last_error)
UNUSED_SURFACE(rt_vulkan_init_headless_present)
UNUSED_SURFACE(rt_vulkan_init_window_present)
UNUSED_SURFACE(rt_vulkan_init_external_window_present)
UNUSED_SURFACE(rt_vulkan_present_buffer)
UNUSED_SURFACE(rt_vulkan_present_buffer_regions_raw)
UNUSED_SURFACE(rt_vulkan_last_present_copy_bytes)
UNUSED_SURFACE(rt_vulkan_last_present_copy_rects)
UNUSED_SURFACE(rt_vulkan_destroy_swapchain)
#else
#include "runtime.h"
#include <dlfcn.h>
int64_t rt_vulkan_copy_from_buffer_array(int64_t,int64_t,int64_t,int64_t);
int64_t rt_vulkan_copy_from_buffer_regions(int64_t,int64_t,int64_t);
int64_t rt_vulkan_copy_from_buffer_strided(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_vulkan_copy_to_buffer_u32(int64_t,int64_t,int64_t);
int64_t rt_vulkan_read_buffer_bytes(int64_t,int64_t,int64_t);
int64_t rt_vulkan_readback_u32_array(int64_t,int64_t,int64_t);
int64_t rt_vulkan_readback_u32_array_checksum(int64_t,int64_t,int64_t);
int64_t rt_vulkan_readback_u32_checksum(int64_t,int64_t,int64_t,int64_t);
#ifdef PHASE2_GPU_READBACK_NATIVE
int64_t phase2_gpu_vulkan_readback_native(void);
#endif
static int64_t value(SplArray *a) { return (int64_t)(intptr_t)a; }
static SplArray *integers(const int64_t *words, int64_t count) {
    SplArray *a = rt_array_new(count);
    for (int64_t i = 0; i < count; ++i) assert(rt_array_push(a, rt_value_int(words[i])));
    return a;
}
static void bytes_equal(SplArray *a, const uint8_t *expected, int64_t n) {
    uint8_t actual[32];
    assert(n <= 32 && rt_array_bytes_copy_checked(value(a), actual, 32) == n);
    assert(memcmp(actual, expected, (size_t)n) == 0);
}
static void empty_result(int64_t result) {
    SplArray *a = (SplArray *)(intptr_t)result;
    assert(a && rt_array_header_ptr(a) && rt_array_len(a) == 0);
    rt_array_free(a);
}
static void *pinned_readback(void *result) {
    *(int64_t *)result = rt_vulkan_readback_u32_array_checksum(55, 2, 0);
    return NULL;
}
int main(int argc, char **argv) {
    assert(argc == 3);
    assert(setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1) == 0);
    SplArray *packed = rt_byte_array_new_len(6);
    const uint8_t original[] = {9,9,9,9,9,9};
    assert(rt_array_bytes_store_checked(value(packed), original, 6) == 6);
    int64_t words[] = {67305985,-1,INT32_MIN};
    SplArray *upload = integers(words, 3);
    int64_t regions_words[] = {258,2,2,4,257,2,1,2};
    SplArray *regions = integers(regions_words, 8);
    if (strcmp(argv[2], "absent") == 0) {
        assert(rt_vulkan_copy_from_buffer_array(value(packed), 6, 51, 0) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, 0, 2, 3, 4) == 0);
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(regions)) == 0);
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 0);
        empty_result(rt_vulkan_read_buffer_bytes(51, 6, 0));
        empty_result(rt_vulkan_readback_u32_array(51, 2, 0));
        assert(rt_vulkan_readback_u32_array_checksum(51, 2, 0) == -1);
        assert(rt_vulkan_readback_u32_checksum(value(upload), 2, 51, 0) == -1);
        assert(rt_value_as_int(rt_array_get(upload,0)) == 67305985);
        bytes_equal(packed, original, 6);
    } else {
        void *provider = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
        assert(provider);
        int64_t (*calls)(void) = (int64_t (*)(void))dlsym(provider, "phase2_gpu_vulkan_readback_calls");
        assert(calls);
        assert(rt_vulkan_copy_from_buffer_array(value(packed), 4, 51, 2) == 1);
        const uint8_t prefix[] = {2,3,4,5,9,9}; bytes_equal(packed, prefix, 6);
        assert(rt_vulkan_copy_from_buffer_array(value(packed), 6, 52, 0) == 0);
        bytes_equal(packed, prefix, 6);
        int64_t tagged_words[] = {0,0,0,0,0,0};
        SplArray *tagged = integers(tagged_words, 6);
        assert(rt_vulkan_copy_from_buffer_strided(value(tagged), 51, 1, 2, 3, 4) == 1);
        const uint8_t stride[] = {1,2,5,6,9,10}; bytes_equal(tagged, stride, 6);
        assert(rt_vulkan_copy_from_buffer_strided(value(tagged), 52, 1, 2, 3, 4) == 0);
        bytes_equal(tagged, stride, 6);
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(regions)) == 1);
        const uint8_t region[] = {2,3,6,7,1,2}; bytes_equal(packed, region, 6);
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 52, value(regions)) == 0);
        bytes_equal(packed, region, 6);
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 1);
        rt_array_set(upload, 1, rt_value_int(UINT32_MAX));
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 1);
        assert(rt_vulkan_copy_to_buffer_u32(52, value(upload), 7) == 0);
        SplArray *bytes = (SplArray *)(intptr_t)rt_vulkan_read_buffer_bytes(51, 6, 0);
        const uint8_t range[] = {0,1,2,3,4,5}; bytes_equal(bytes, range, 6);
        SplArray *pixels = (SplArray *)(intptr_t)rt_vulkan_readback_u32_array(51, 2, 0);
        assert(rt_array_len(pixels) == 2);
        assert(rt_value_as_int(rt_array_get(pixels,0)) == 50462976);
        assert(rt_value_as_int(rt_array_get(pixels,1)) == 117835012);
        assert(rt_vulkan_readback_u32_array_checksum(51, 2, 0) == 168297988);
        assert(rt_vulkan_readback_u32_array_checksum(51, 1, 252) == 2147417597);
        SplArray *high = (SplArray *)(intptr_t)rt_vulkan_readback_u32_array(51, 1, 252);
        assert(rt_value_as_int(rt_array_get(high, 0)) == INT64_C(4294901244));
        rt_array_free(high);
        assert(rt_vulkan_readback_u32_checksum(value(upload), 2, 51, 0) == 168297988);
        assert(rt_value_as_int(rt_array_get(upload,0)) == 50462976);
        assert(rt_value_as_int(rt_array_get(upload,1)) == 117835012);
        assert(rt_value_as_int(rt_array_get(upload,2)) == INT32_MIN);
        assert(rt_vulkan_readback_u32_checksum(value(upload), 2, 52, 0) == -1);
        assert(rt_value_as_int(rt_array_get(upload,0)) == 50462976);
        assert(rt_value_as_int(rt_array_get(upload,1)) == 117835012);
        empty_result(rt_vulkan_read_buffer_bytes(52, 6, 0));
        empty_result(rt_vulkan_readback_u32_array(52, 2, 0));
        assert(rt_vulkan_readback_u32_array_checksum(52, 2, 0) == -1);
        SplArray *empty = rt_array_new(0);
        assert(rt_vulkan_copy_from_buffer_array(value(empty), 0, 51, 0) == 1);
        assert(rt_vulkan_copy_from_buffer_strided(value(empty), 51, 0, 0, 3, 0) == 1);
        assert(rt_vulkan_copy_to_buffer_u32(51, value(empty), 0) == 1);
        empty_result(rt_vulkan_read_buffer_bytes(51, 0, 0));
        int64_t before = calls();
        assert(rt_vulkan_readback_u32_checksum(value(upload), 4, 51, 0) == -1);
        assert(rt_vulkan_readback_u32_checksum(value(upload), 0, 51, 0) == -1);
        assert(rt_vulkan_readback_u32_checksum(value(upload), INT64_MAX, 51, 0) == -1);
        assert(rt_vulkan_readback_u32_checksum(value(upload), 2, 51, INT64_MAX) == -1);
        assert(rt_vulkan_readback_u32_checksum(value(packed), 1, 51, 0) == -1);
        assert(rt_vulkan_copy_from_buffer_array(value(packed), 7, 51, 0) == 0);
        assert(rt_vulkan_copy_from_buffer_array(value(packed), -1, 51, 0) == 0);
        assert(rt_vulkan_copy_from_buffer_array(value(packed), 6, 51, INT64_MAX) == 0);
        assert(rt_vulkan_copy_from_buffer_array(3, 0, 51, 0) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, 0, 2, 3, 1) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, 0, 2, 4, 4) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, 0, 2, 16385, 4) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, 0, INT64_MAX, 3, INT64_MAX) == 0);
        assert(rt_vulkan_copy_from_buffer_strided(value(packed), 51, INT64_MAX, 2, 3, 4) == 0);
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(empty)) == 0);
        rt_array_set(regions, 3, rt_value_int(1));
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(regions)) == 0);
        rt_array_set(regions, 3, rt_value_int(4));
        rt_array_set(regions, 0, rt_value_int(-1));
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(regions)) == 0);
        rt_array_set(regions, 0, rt_value_int(258));
        rt_array_set(regions, 2, rt_value_int(1));
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(regions)) == 0);
        rt_array_set(upload, 0, rt_value_int(INT64_C(4294967296)));
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 0);
        rt_array_set(upload, 0, rt_value_int(INT64_C(-2147483649)));
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 0);
        rt_array_set(upload, 0, rt_value_bool(1));
        assert(rt_vulkan_copy_to_buffer_u32(51, value(upload), 7) == 0);
        assert(rt_vulkan_copy_to_buffer_u32(51, value(packed), 0) == 0);
        empty_result(rt_vulkan_read_buffer_bytes(51, -1, 0));
        empty_result(rt_vulkan_read_buffer_bytes(51, INT64_C(2147483649), 0));
        empty_result(rt_vulkan_readback_u32_array(51, INT64_MAX, 0));
        empty_result(rt_vulkan_readback_u32_array(51, 0, 0));
        assert(rt_vulkan_readback_u32_array_checksum(51, 0, 0) == -1);
        assert(rt_vulkan_readback_u32_array_checksum(51, INT64_MAX, 0) == -1);
        assert(calls() == before); /* malformed requests never reach provider */
        bytes_equal(packed, region, 6);
        /* Boundary records and cumulative rows: zero-sized rows count toward
         * the canonical aggregate ceiling but add no output bytes. */
        SplArray *many = rt_array_new(1028);
        for (int i = 0; i < 256; ++i) {
            rt_array_push(many, rt_value_int(0));
            rt_array_push(many, rt_value_int(i == 0 ? 6 : 0));
            rt_array_push(many, rt_value_int(1));
            rt_array_push(many, rt_value_int(6));
        }
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(many)) == 1);
        before = calls();
        for (int i = 0; i < 4; ++i) rt_array_push(many, rt_value_int(0));
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(many)) == 0);
        assert(calls() == before);
        rt_array_free(many);
        int64_t capped[] = {0,6,1,6,0,0,16383,0};
        many = integers(capped, 8);
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(many)) == 1);
        before = calls();
        rt_array_set(many, 6, rt_value_int(16384));
        assert(rt_vulkan_copy_from_buffer_regions(value(packed), 51, value(many)) == 0);
        assert(calls() == before);
        rt_array_free(many);
#ifdef PHASE2_GPU_READBACK_NATIVE
        int64_t native = phase2_gpu_vulkan_readback_native();
        printf("native Simple boundary result=%lld\n", (long long)native);
        assert(native == 0);
#endif
        clock_t start = clock();
        for (int i = 0; i < 10000; ++i)
            assert(rt_vulkan_copy_from_buffer_array(value(packed), 6, 51, 0) == 1);
        printf("readback iterations=10000 cpu_ms=%.3f\n", 1000.0 * (clock()-start)/CLOCKS_PER_SEC);
        SplArray *frame = rt_array_new(480000);
        for (int i = 0; i < 480000; ++i) assert(rt_array_push(frame, rt_value_int(0)));
        start = clock();
        int64_t frame_checksum = rt_vulkan_readback_u32_checksum(value(frame), 480000, 51, 0);
        assert(frame_checksum >= 0);
        for (int i = 1; i < 20; ++i)
            assert(rt_vulkan_readback_u32_checksum(value(frame), 480000, 51, 0) == frame_checksum);
        printf("800x600 readback iterations=20 cpu_ms=%.3f checksum=%lld\n",
            1000.0 * (clock()-start)/CLOCKS_PER_SEC, (long long)frame_checksum);
        rt_array_free(frame);
        int (*is_entered)(void) = (int (*)(void))dlsym(provider, "phase2_gpu_vulkan_readback_entered");
        void (*release)(void) = (void (*)(void))dlsym(provider, "phase2_gpu_vulkan_readback_release");
        assert(is_entered && release);
        pthread_t worker;
        int64_t pinned_result = -1;
        assert(pthread_create(&worker, NULL, pinned_readback, &pinned_result) == 0);
        while (!is_entered()) sched_yield();
        assert(rt_gpu_provider_unload(2) == 0);
        release();
        assert(pthread_join(worker, NULL) == 0);
        assert(pinned_result == 168297988);
        dlclose(provider);
        assert(rt_gpu_provider_unload(2) == 1);
        bytes_equal(bytes, range, 6); /* returned value owns its storage */
        assert(rt_value_as_int(rt_array_get(pixels,1)) == 117835012);
        rt_array_free(bytes); rt_array_free(pixels); rt_array_free(tagged); rt_array_free(empty);
    }
    rt_array_free(packed); rt_array_free(upload); rt_array_free(regions);
    puts("phase2-gpu-vulkan-readback: PASS");
    return 0;
}
#endif
