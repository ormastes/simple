/* Synthetic provider ABI/lifetime fixture: no physical GPU evidence. */
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <assert.h>
#include <time.h>
#include <stdatomic.h>
#include <pthread.h>
#include <dlfcn.h>

#ifdef PHASE2_SCALAR_PROVIDER
#ifndef PHASE2_SCALAR_ABI
#define PHASE2_SCALAR_ABI 1
#endif
int64_t rt_simple_gpu_provider_abi_version(void) { return PHASE2_SCALAR_ABI; }
int64_t rt_simple_gpu_provider_backend_bits(void) { return 2; }
int32_t rt_vk_provider_available(void) { return 1; }
int64_t rt_vulkan_provider_is_available(void) { return 1; }
int64_t rt_vulkan_provider_device_count(void) { return 1; }
int64_t rt_vulkan_init(void) { return 1; }
int64_t rt_vulkan_alloc_buffer(void) { return 1; }
int64_t rt_vulkan_copy_to_buffer_raw(void) { return 1; }
int64_t rt_vulkan_copy_from_buffer_raw(void) { return 1; }
int64_t rt_vulkan_copy_from_buffer_strided_raw(void) { return 1; }
int64_t rt_vulkan_copy_from_buffer_regions_raw(void) { return 1; }
int64_t rt_vulkan_compile_spirv_raw(void) { return 1; }
int64_t rt_vulkan_create_compute_pipeline_raw(void) { return 1; }
int64_t rt_vulkan_push_constants_raw(void) { return 1; }
int64_t rt_vulkan_init_headless_present(void) { return 1; }
int64_t rt_vulkan_init_window_present(void) { return 1; }
int64_t rt_vulkan_init_external_window_present(void) { return 1; }
int64_t rt_vulkan_present_buffer(void) { return 1; }
int64_t rt_vulkan_present_buffer_regions_raw(void) { return 1; }
int64_t rt_vulkan_last_present_copy_bytes(void) { return 1; }
int64_t rt_vulkan_last_present_copy_rects(void) { return 1; }
int64_t rt_vulkan_destroy_swapchain(void) { return 1; }
int64_t rt_vulkan_accepted_compute_submit_count(void) { return 100; }
int64_t rt_vulkan_begin_compute(void) { return 101; }
int64_t rt_vulkan_bind_buffer(int64_t a0, int64_t a1, int64_t a2) { return a0 == 41 && a1 == -17 && a2 == 123456 ? 1 : 0; }
int64_t rt_vulkan_bind_descriptors(int64_t a0, int64_t a1) { return a0 == 41 && a1 == -17 ? 1 : 0; }
int64_t rt_vulkan_bind_pipeline(int64_t a0, int64_t a1) { return a0 == 41 && a1 == -17 ? 1 : 0; }
int64_t rt_vulkan_create_descriptor_set(int64_t a0) { return a0 == 41 ? 105 : -777; }
int64_t rt_vulkan_destroy_descriptor_set(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_destroy_fence(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_destroy_pipeline(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_destroy_shader(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_discard_command(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_dispatch(int64_t a0, int64_t a1, int64_t a2, int64_t a3) { return a0 == 41 && a1 == -17 && a2 == 123456 && a3 == 7 ? 1 : 0; }
int64_t rt_vulkan_end_compute(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_fence_submission_supported(void) { return 113; }
int64_t rt_vulkan_free_buffer(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_select_device(int64_t a0) { return a0 == 41 ? 1 : 0; }
int64_t rt_vulkan_selected_device_driver_identity_hash(void) { return 116; }
static char text_values[6][4096];
static atomic_int phase2_gpu_vulkan_scalar_getter_entered;
int64_t phase2_gpu_vulkan_scalar_getter_active(void) {
    return atomic_load(&phase2_gpu_vulkan_scalar_getter_entered);
}
int64_t rt_vulkan_shutdown(void) {
    if (atomic_load(&phase2_gpu_vulkan_scalar_getter_entered))
        strcpy(text_values[1], "shutdown-invalidated");
    return 1;
}
#ifndef PHASE2_SCALAR_OMIT_OPTIONAL
int64_t rt_vulkan_submit_and_wait(int64_t a0) { return a0 == 41 ? 1 : 0; }
#endif
int64_t rt_vulkan_submit_and_wait_fence(int64_t a0) { return a0 == 41 ? 119 : -777; }
int64_t rt_vulkan_submit_no_wait(int64_t a0) { return a0 == 41 ? 120 : -777; }
int64_t rt_vulkan_wait_fence(int64_t a0, int64_t a1) { return a0 == 41 && a1 == -17 ? 1 : 0; }
#ifndef PHASE2_SCALAR_OMIT_REQUIRED
int64_t rt_vulkan_wait_idle(void) { return 1; }
#endif
static char unterminated[4096];
__attribute__((constructor)) static void phase2_gpu_vulkan_scalar_text_init(void) {
    memset(unterminated, 'x', sizeof(unterminated));
    strcpy(text_values[0], "device_driver_identity");
    strcpy(text_values[1], "device_name");
    strcpy(text_values[2], "device_type");
    strcpy(text_values[3], "get_last_error");
    strcpy(text_values[4], "selected_device_driver_identity");
    strcpy(text_values[5], "selected_device_type");
}
__attribute__((destructor)) static void phase2_gpu_vulkan_scalar_text_destroy(void) {
    memset(text_values, '!', sizeof(text_values));
}
const char *rt_vulkan_device_driver_identity(int64_t device) {
    if (device == -2) return NULL;
    if (device == -3) return unterminated;
    if (device != 41) return "";
    return text_values[0];
}
const char *rt_vulkan_device_name(int64_t device) {
    if (device == 999) {
        struct timespec delay = {0, 50000000};
        atomic_store(&phase2_gpu_vulkan_scalar_getter_entered, 1);
        nanosleep(&delay, NULL);
        return text_values[1];
    }
    if (device == -2) return NULL;
    if (device == -3) return unterminated;
    if (device != 41) return "";
    return text_values[1];
}
const char *rt_vulkan_device_type(int64_t device) {
    if (device == -2) return NULL;
    if (device == -3) return unterminated;
    if (device != 41) return "";
    return text_values[2];
}
const char *rt_vulkan_get_last_error(void) {
    return text_values[3];
}
const char *rt_vulkan_selected_device_driver_identity(void) {
    return text_values[4];
}
const char *rt_vulkan_selected_device_type(void) {
    return text_values[5];
}
#else
#include "runtime.h"
#ifdef PHASE2_SCALAR_LOADER
/* The production loader also includes the scalar fragment after integration.
 * Suppress that include for baseline/lock-removal probes so their selected
 * implementation, rather than the normal guarded one, is exercised. */
#if defined(PHASE2_SCALAR_BASELINE) || defined(PHASE2_SCALAR_HEADER)
#define SIMPLE_GPU_VULKAN_SCALAR_PRIVATE_H
#endif
#include "../../../src/runtime/runtime_dynload.c"
#ifndef PHASE2_SCALAR_BASELINE
#ifdef PHASE2_SCALAR_HEADER
#undef SIMPLE_GPU_VULKAN_SCALAR_PRIVATE_H
#else
#define PHASE2_SCALAR_HEADER "../../../src/runtime/runtime_gpu_vulkan_scalar_private.h"
#endif
#include PHASE2_SCALAR_HEADER
#endif
#else
int64_t rt_vulkan_accepted_compute_submit_count(void);
int64_t rt_vulkan_begin_compute(void);
int64_t rt_vulkan_bind_buffer(int64_t, int64_t, int64_t);
int64_t rt_vulkan_bind_descriptors(int64_t, int64_t);
int64_t rt_vulkan_bind_pipeline(int64_t, int64_t);
int64_t rt_vulkan_create_descriptor_set(int64_t);
int64_t rt_vulkan_destroy_descriptor_set(int64_t);
int64_t rt_vulkan_destroy_fence(int64_t);
int64_t rt_vulkan_destroy_pipeline(int64_t);
int64_t rt_vulkan_destroy_shader(int64_t);
int64_t rt_vulkan_discard_command(int64_t);
int64_t rt_vulkan_dispatch(int64_t, int64_t, int64_t, int64_t);
int64_t rt_vulkan_end_compute(int64_t);
int64_t rt_vulkan_fence_submission_supported(void);
int64_t rt_vulkan_free_buffer(int64_t);
int64_t rt_vulkan_select_device(int64_t);
int64_t rt_vulkan_selected_device_driver_identity_hash(void);
int64_t rt_vulkan_shutdown(void);
int64_t rt_vulkan_submit_and_wait(int64_t);
int64_t rt_vulkan_submit_and_wait_fence(int64_t);
int64_t rt_vulkan_submit_no_wait(int64_t);
int64_t rt_vulkan_wait_fence(int64_t, int64_t);
int64_t rt_vulkan_wait_idle(void);
const char *rt_vulkan_device_driver_identity(int64_t);
const char *rt_vulkan_device_name(int64_t);
const char *rt_vulkan_device_type(int64_t);
const char *rt_vulkan_get_last_error(void);
const char *rt_vulkan_selected_device_driver_identity(void);
const char *rt_vulkan_selected_device_type(void);
int64_t phase2_gpu_vulkan_scalar_retire(void) {
    if (setenv("SIMPLE_VULKAN_PROVIDER_PATH", "/nonexistent/phase2-scalar-provider", 1)) return 0;
    return rt_gpu_provider_unload(2);
}
#ifdef PHASE2_SCALAR_NATIVE_SUPPORT
extern int spl_main(void);
extern void __simple_call_module_inits(void);
int main(void) {
    __simple_call_module_inits();
    return spl_main();
}
#endif
#ifndef PHASE2_SCALAR_NATIVE_SUPPORT
static void *phase2_gpu_vulkan_scalar_race_getter(void *arg) {
    int *ok = arg;
    *ok = strcmp(rt_vulkan_device_name(999), "device_name") == 0;
    return NULL;
}
static int phase2_gpu_vulkan_scalar_race(const char *path) {
    pthread_t worker;
    int ok = 0;
    void *provider = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    assert(provider);
    int64_t (*active)(void) = (int64_t (*)(void))dlsym(provider,
        "phase2_gpu_vulkan_scalar_getter_active");
    assert(active);
    assert(pthread_create(&worker, NULL, phase2_gpu_vulkan_scalar_race_getter, &ok) == 0);
    struct timespec delay = {0, 1000000};
    int ticks = 0;
    while (!active() && ++ticks < 2000) nanosleep(&delay, NULL);
    assert(active());
    assert(rt_vulkan_shutdown() == 1);
    assert(pthread_join(worker, NULL) == 0);
    assert(rt_gpu_provider_unload(2) == 1);
    assert(dlclose(provider) == 0);
    if (!ok) { fputs("shutdown/text copy race detected\n", stderr); return 73; }
    puts("phase2_gpu_vulkan_scalar: shutdown/text lifetime PASS");
    return 0;
}
static uint64_t phase2_gpu_vulkan_scalar_nanos(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}
int main(int argc, char **argv) {
    assert(argc == 3);
    int good = strcmp(argv[2], "good") == 0 || strcmp(argv[2], "optional") == 0;
    int optional = strcmp(argv[2], "optional") == 0;
    assert(setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1) == 0);
    assert(unsetenv("SIMPLE_VULKAN_PROVIDER_SHA256") == 0);
    if (strcmp(argv[2], "race") == 0) return phase2_gpu_vulkan_scalar_race(argv[1]);
    assert(rt_vulkan_accepted_compute_submit_count() == (good ? 100 : 0));
    assert(rt_vulkan_begin_compute() == (good ? 101 : 0));
    assert(rt_vulkan_bind_buffer(41, -17, 123456) == (good ? 1 : 0));
    assert(rt_vulkan_bind_buffer(42, -17, 123456) == 0);
    assert(rt_vulkan_bind_descriptors(41, -17) == (good ? 1 : 0));
    assert(rt_vulkan_bind_descriptors(42, -17) == 0);
    assert(rt_vulkan_bind_pipeline(41, -17) == (good ? 1 : 0));
    assert(rt_vulkan_bind_pipeline(42, -17) == 0);
    assert(rt_vulkan_create_descriptor_set(41) == (good ? 105 : 0));
    assert(rt_vulkan_create_descriptor_set(42) == (good ? -777 : 0));
    assert(rt_vulkan_destroy_descriptor_set(41) == (good ? 1 : 0));
    assert(rt_vulkan_destroy_descriptor_set(42) == 0);
    assert(rt_vulkan_destroy_fence(41) == (good ? 1 : 0));
    assert(rt_vulkan_destroy_fence(42) == 0);
    assert(rt_vulkan_destroy_pipeline(41) == (good ? 1 : 0));
    assert(rt_vulkan_destroy_pipeline(42) == 0);
    assert(rt_vulkan_destroy_shader(41) == (good ? 1 : 0));
    assert(rt_vulkan_destroy_shader(42) == 0);
    assert(rt_vulkan_discard_command(41) == (good ? 1 : 0));
    assert(rt_vulkan_discard_command(42) == 0);
    assert(rt_vulkan_dispatch(41, -17, 123456, 7) == (good ? 1 : 0));
    assert(rt_vulkan_dispatch(42, -17, 123456, 7) == 0);
    assert(rt_vulkan_end_compute(41) == (good ? 1 : 0));
    assert(rt_vulkan_end_compute(42) == 0);
    assert(rt_vulkan_fence_submission_supported() == (good ? 113 : 0));
    assert(rt_vulkan_free_buffer(41) == (good ? 1 : 0));
    assert(rt_vulkan_free_buffer(42) == 0);
    assert(rt_vulkan_select_device(41) == (good ? 1 : 0));
    assert(rt_vulkan_select_device(42) == 0);
    assert(rt_vulkan_selected_device_driver_identity_hash() == (good ? 116 : 0));
    assert(rt_vulkan_shutdown() == (good ? 1 : 0));
    assert(rt_vulkan_submit_and_wait(41) == (good && !optional ? 1 : 0));
    assert(rt_vulkan_submit_and_wait(42) == 0);
    assert(rt_vulkan_submit_and_wait_fence(41) == (good ? 119 : 0));
    assert(rt_vulkan_submit_and_wait_fence(42) == (good ? -777 : 0));
    assert(rt_vulkan_submit_no_wait(41) == (good ? 120 : 0));
    assert(rt_vulkan_submit_no_wait(42) == (good ? -777 : 0));
    assert(rt_vulkan_wait_fence(41, -17) == (good ? 1 : 0));
    assert(rt_vulkan_wait_fence(42, -17) == 0);
    assert(rt_vulkan_wait_idle() == (good ? 1 : 0));
    const char *saved0 = rt_vulkan_device_driver_identity(41);
    assert(strcmp(saved0, good ? "device_driver_identity" : "") == 0);
    assert(strcmp(rt_vulkan_device_driver_identity(-2), "") == 0);
    assert(strcmp(rt_vulkan_device_driver_identity(-3), "") == 0);
    const char *saved1 = rt_vulkan_device_name(41);
    assert(strcmp(saved1, good ? "device_name" : "") == 0);
    assert(strcmp(rt_vulkan_device_name(-2), "") == 0);
    assert(strcmp(rt_vulkan_device_name(-3), "") == 0);
    const char *saved2 = rt_vulkan_device_type(41);
    assert(strcmp(saved2, good ? "device_type" : "") == 0);
    assert(strcmp(rt_vulkan_device_type(-2), "") == 0);
    assert(strcmp(rt_vulkan_device_type(-3), "") == 0);
    const char *saved3 = rt_vulkan_get_last_error();
    assert(strcmp(saved3, good ? "get_last_error" : "Vulkan provider unavailable or invalid error text") == 0);
    const char *saved4 = rt_vulkan_selected_device_driver_identity();
    assert(strcmp(saved4, good ? "selected_device_driver_identity" : "") == 0);
    const char *saved5 = rt_vulkan_selected_device_type();
    assert(strcmp(saved5, good ? "selected_device_type" : "") == 0);
    assert(rt_gpu_provider_loaded(2) == good);
    if (good) {
        uint64_t start = phase2_gpu_vulkan_scalar_nanos();
        for (int i=0; i<100000; ++i) assert(rt_vulkan_bind_buffer(41, -17, 123456) == 1);
        printf("scalar_calls=100000 elapsed_ns=%llu\n", (unsigned long long)(phase2_gpu_vulkan_scalar_nanos()-start));
        assert(phase2_gpu_vulkan_scalar_retire() == 1);
        assert(strcmp(saved0, "device_driver_identity") == 0);
        assert(strcmp(saved1, "device_name") == 0);
        assert(strcmp(saved2, "device_type") == 0);
        assert(strcmp(saved3, "get_last_error") == 0);
        assert(strcmp(saved4, "selected_device_driver_identity") == 0);
        assert(strcmp(saved5, "selected_device_type") == 0);
        assert(rt_vulkan_begin_compute() == 0);
    }
    printf("phase2_gpu_vulkan_scalar: %s PASS (29 symbols)\n", argv[2]);
    return 0;
}
#endif
#endif
#endif
