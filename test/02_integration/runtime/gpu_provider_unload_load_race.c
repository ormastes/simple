#define _POSIX_C_SOURCE 200809L

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>

enum {
    SIMPLE_GPU_BACKEND_CUDA = 1,
    SIMPLE_GPU_BACKEND_VULKAN = 2
};

#ifdef SIMPLE_GPU_RACE_PROVIDER

#ifndef SIMPLE_GPU_RACE_DEVICE_COUNT
#define SIMPLE_GPU_RACE_DEVICE_COUNT 7
#endif

#ifdef SIMPLE_GPU_RACE_SLOW_CALL
static void touch_marker(const char *environment_name) {
    const char *path = getenv(environment_name);
    FILE *file = path ? fopen(path, "ab") : NULL;
    if (file) {
        fputc('x', file);
        fclose(file);
    }
}

__attribute__((destructor))
static void provider_closed(void) {
    touch_marker("SIMPLE_GPU_RACE_CLOSE_MARKER");
}
#endif

__attribute__((visibility("default")))
int64_t rt_simple_gpu_provider_abi_version(void) { return 1; }

__attribute__((visibility("default")))
int64_t rt_simple_gpu_provider_backend_bits(void) {
    return SIMPLE_GPU_BACKEND_CUDA | SIMPLE_GPU_BACKEND_VULKAN;
}

__attribute__((visibility("default")))
int64_t rt_vulkan_provider_device_count(void) {
#ifdef SIMPLE_GPU_RACE_SLOW_CALL
    struct timespec pause = {0, 200000000};
    touch_marker("SIMPLE_GPU_RACE_ENTER_MARKER");
    nanosleep(&pause, NULL);
#endif
    return SIMPLE_GPU_RACE_DEVICE_COUNT;
}

__attribute__((visibility("default")))
int64_t rt_cuda_launch_kernel_ex(
        int64_t module, const uint8_t *name, uint64_t name_len,
        int64_t grid_x, int64_t grid_y, int64_t grid_z,
        int64_t block_x, int64_t block_y, int64_t block_z,
        int64_t shared_bytes, int64_t stream, int64_t args_ptr) {
    return module == 11 && name && name_len == 1 && name[0] == 'k' &&
        grid_x == 1 && grid_y == 2 && grid_z == 3 &&
        block_x == 4 && block_y == 5 && block_z == 6 &&
        shared_bytes == 7 && stream == 8 && args_ptr == 9 ? 91 : -1;
}

#define PROVIDER_STUB(name) \
    __attribute__((visibility("default"))) int64_t name(void) { return 1; }

PROVIDER_STUB(rt_vulkan_provider_is_available)
PROVIDER_STUB(rt_vk_provider_available)
PROVIDER_STUB(rt_vulkan_init)
PROVIDER_STUB(rt_vulkan_shutdown)
PROVIDER_STUB(rt_vulkan_select_device)
PROVIDER_STUB(rt_vulkan_alloc_buffer)
PROVIDER_STUB(rt_vulkan_free_buffer)
PROVIDER_STUB(rt_vulkan_copy_to_buffer_raw)
PROVIDER_STUB(rt_vulkan_copy_from_buffer_raw)
PROVIDER_STUB(rt_vulkan_copy_from_buffer_strided_raw)
PROVIDER_STUB(rt_vulkan_copy_from_buffer_regions_raw)
PROVIDER_STUB(rt_vulkan_compile_spirv_raw)
PROVIDER_STUB(rt_vulkan_destroy_shader)
PROVIDER_STUB(rt_vulkan_create_compute_pipeline_raw)
PROVIDER_STUB(rt_vulkan_destroy_pipeline)
PROVIDER_STUB(rt_vulkan_create_descriptor_set)
PROVIDER_STUB(rt_vulkan_bind_buffer)
PROVIDER_STUB(rt_vulkan_destroy_descriptor_set)
PROVIDER_STUB(rt_vulkan_begin_compute)
PROVIDER_STUB(rt_vulkan_bind_pipeline)
PROVIDER_STUB(rt_vulkan_bind_descriptors)
PROVIDER_STUB(rt_vulkan_push_constants_raw)
PROVIDER_STUB(rt_vulkan_dispatch)
PROVIDER_STUB(rt_vulkan_end_compute)
PROVIDER_STUB(rt_vulkan_discard_command)
PROVIDER_STUB(rt_vulkan_fence_submission_supported)
PROVIDER_STUB(rt_vulkan_accepted_compute_submit_count)
PROVIDER_STUB(rt_vulkan_submit_and_wait_fence)
PROVIDER_STUB(rt_vulkan_submit_no_wait)
PROVIDER_STUB(rt_vulkan_wait_fence)
PROVIDER_STUB(rt_vulkan_destroy_fence)
PROVIDER_STUB(rt_vulkan_wait_idle)
PROVIDER_STUB(rt_vulkan_device_name)
PROVIDER_STUB(rt_vulkan_device_type)
PROVIDER_STUB(rt_vulkan_selected_device_type)
PROVIDER_STUB(rt_vulkan_device_driver_identity)
PROVIDER_STUB(rt_vulkan_selected_device_driver_identity)
PROVIDER_STUB(rt_vulkan_selected_device_driver_identity_hash)
PROVIDER_STUB(rt_vulkan_get_last_error)
PROVIDER_STUB(rt_vulkan_init_headless_present)
PROVIDER_STUB(rt_vulkan_init_window_present)
PROVIDER_STUB(rt_vulkan_init_external_window_present)
PROVIDER_STUB(rt_vulkan_present_buffer)
PROVIDER_STUB(rt_vulkan_present_buffer_regions_raw)
PROVIDER_STUB(rt_vulkan_last_present_copy_bytes)
PROVIDER_STUB(rt_vulkan_last_present_copy_rects)
PROVIDER_STUB(rt_vulkan_destroy_swapchain)

PROVIDER_STUB(rt_cuda_provider_available)
PROVIDER_STUB(rt_cuda_provider_device_count)
PROVIDER_STUB(rt_cuda_init)
PROVIDER_STUB(rt_cuda_device_get)
PROVIDER_STUB(rt_cuda_device_compute_capability)
PROVIDER_STUB(rt_cuda_ctx_create)
PROVIDER_STUB(rt_cuda_ctx_set_current)
PROVIDER_STUB(rt_cuda_ctx_destroy)
PROVIDER_STUB(rt_cuda_ctx_synchronize)
PROVIDER_STUB(rt_cuda_mem_alloc)
PROVIDER_STUB(rt_cuda_mem_free)
PROVIDER_STUB(rt_cuda_memcpy_htod)
PROVIDER_STUB(rt_cuda_memcpy_dtoh)
PROVIDER_STUB(rt_cuda_memcpy_dtod)
PROVIDER_STUB(rt_cuda_memset)
PROVIDER_STUB(rt_cuda_memset_d32)
PROVIDER_STUB(rt_cuda_module_load_data_bytes)
PROVIDER_STUB(rt_cuda_module_unload)
PROVIDER_STUB(rt_cuda_launch_kernel_name)
PROVIDER_STUB(rt_cuda_sync)
PROVIDER_STUB(rt_cuda_device_name)
PROVIDER_STUB(rt_cuda_get_error_string)

#else

#include <pthread.h>
#include <unistd.h>

int64_t rt_gpu_provider_loaded(int64_t backend);
const char *rt_gpu_provider_path(int64_t backend);
int64_t rt_gpu_provider_unload(int64_t backend);
int64_t rt_vulkan_device_count(void);
int64_t rt_cuda_launch_kernel_ex(
    int64_t, const uint8_t *, uint64_t, int64_t, int64_t, int64_t,
    int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
uint64_t simple_gpu_test_generation_v1(int64_t backend);

static int64_t call_result;

static void *call_worker(void *unused) {
    (void)unused;
    call_result = rt_vulkan_device_count();
    return NULL;
}

static int marker_size(const char *path) {
    struct stat info;
    return stat(path, &info) == 0 ? (int)info.st_size : 0;
}

int main(int argc, char **argv) {
    pthread_t worker;
    struct timespec poll = {0, 1000000};
    const char *pinned_path;
    uint64_t first_generation;
    uint64_t next_generation;
    int attempts = 0;
    static const uint8_t kernel_name[] = {'k'};

    if (argc != 5 ||
            setenv("SIMPLE_GPU_RACE_ENTER_MARKER", argv[3], 1) != 0 ||
            setenv("SIMPLE_GPU_RACE_CLOSE_MARKER", argv[4], 1) != 0 ||
            setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1) != 0 ||
            setenv("SIMPLE_CUDA_PROVIDER_PATH", argv[2], 1) != 0)
        return 2;
    unlink(argv[3]);
    unlink(argv[4]);

    if (rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 1)
        return 3;
    pinned_path = rt_gpu_provider_path(SIMPLE_GPU_BACKEND_VULKAN);
    first_generation = simple_gpu_test_generation_v1(
        SIMPLE_GPU_BACKEND_VULKAN);
    if (strcmp(pinned_path, argv[1]) != 0 || first_generation == 0 ||
            pthread_create(&worker, NULL, call_worker, NULL) != 0)
        return 4;

    while (access(argv[3], F_OK) != 0 && attempts++ < 5000)
        nanosleep(&poll, NULL);
    if (access(argv[3], F_OK) != 0 || marker_size(argv[4]) != 0)
        return 5;

    if (rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN) != 0 ||
            marker_size(argv[4]) != 0 ||
            rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 0 ||
            rt_vulkan_device_count() != 0)
        return 6;

    if (pthread_join(worker, NULL) != 0 || call_result != 7 ||
            marker_size(argv[4]) != 0 || strcmp(pinned_path, argv[1]) != 0)
        return 7;

    if (rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN) != 1 ||
            marker_size(argv[4]) != 1 || strcmp(pinned_path, argv[1]) != 0)
        return 8;

    if (setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[2], 1) != 0 ||
            rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_VULKAN) != 1 ||
            rt_vulkan_device_count() != 9)
        return 9;
    next_generation = simple_gpu_test_generation_v1(
        SIMPLE_GPU_BACKEND_VULKAN);
    if (next_generation <= first_generation ||
            strcmp(rt_gpu_provider_path(SIMPLE_GPU_BACKEND_VULKAN), argv[2]) != 0 ||
            rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_VULKAN) != 1)
        return 10;

    if (rt_gpu_provider_loaded(SIMPLE_GPU_BACKEND_CUDA) != 1 ||
            rt_cuda_launch_kernel_ex(11, kernel_name, 1, 1, 2, 3,
                4, 5, 6, 7, 8, 9) != 91 ||
            rt_gpu_provider_unload(SIMPLE_GPU_BACKEND_CUDA) != 1)
        return 11;

    puts("gpu_provider_unload_load_race=pass busy_retire=true "
         "closing_admission_rejected=true close_once=true "
         "replacement_generation=true handwritten_wrapper_pinned=true "
         "path_copy_lifetime=true");
    return 0;
}

#endif
