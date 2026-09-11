#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
/* Hosted dynamic loading for pure-Simple native binaries. */

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#if defined(__linux__)
#include <linux/memfd.h>
#include <sys/syscall.h>
#endif
#endif

#include "runtime.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#define SIMPLE_GPU_THREAD_LOCAL __declspec(thread)
#else
#define SIMPLE_GPU_THREAD_LOCAL _Thread_local
#endif

enum { SIMPLE_GPU_PATH_COPY_CAPACITY_V1 = 4096 };
static SIMPLE_GPU_THREAD_LOCAL char
    simple_gpu_path_copy_v1[SIMPLE_GPU_PATH_COPY_CAPACITY_V1];

enum {
    SIMPLE_GPU_PROVIDER_ABI_V1 = 1,
    SIMPLE_GPU_BACKEND_CUDA = 1,
    SIMPLE_GPU_BACKEND_VULKAN = 2,
    SIMPLE_GPU_BACKEND_METAL = 4
};

typedef enum SimpleGpuProviderPhaseV1 {
    SIMPLE_GPU_PROVIDER_EMPTY_V1 = 0,
    SIMPLE_GPU_PROVIDER_LOADING_V1 = 1,
    SIMPLE_GPU_PROVIDER_ACTIVE_V1 = 2,
    SIMPLE_GPU_PROVIDER_RETIRING_V1 = 3,
    SIMPLE_GPU_PROVIDER_CLOSING_V1 = 4,
    SIMPLE_GPU_PROVIDER_FAILED_V1 = 5
} SimpleGpuProviderPhaseV1;

typedef struct SimpleGpuProviderState {
    int64_t backend_bit;
    const char *path_env;
    void *handle;
    int64_t abi_version;
    int64_t backend_bits;
    char *path;
    uint64_t generation;
    uint64_t in_flight;
    SimpleGpuProviderPhaseV1 phase;
} SimpleGpuProviderState;

typedef struct SimpleGpuCallPinV1 {
    SimpleGpuProviderState *state;
    void *symbol;
    uint64_t generation;
    int active;
} SimpleGpuCallPinV1;

static SimpleGpuProviderState simple_gpu_providers[] = {
    {SIMPLE_GPU_BACKEND_CUDA, "SIMPLE_CUDA_PROVIDER_PATH", NULL, 0, 0,
        NULL, 0, 0, SIMPLE_GPU_PROVIDER_EMPTY_V1},
    {SIMPLE_GPU_BACKEND_VULKAN, "SIMPLE_VULKAN_PROVIDER_PATH", NULL, 0, 0,
        NULL, 0, 0, SIMPLE_GPU_PROVIDER_EMPTY_V1},
    {SIMPLE_GPU_BACKEND_METAL, "SIMPLE_METAL_PROVIDER_PATH", NULL, 0, 0,
        NULL, 0, 0, SIMPLE_GPU_PROVIDER_EMPTY_V1}
};
static atomic_flag simple_gpu_provider_lock = ATOMIC_FLAG_INIT;

static void simple_gpu_lock(void) {
    while (atomic_flag_test_and_set_explicit(
        &simple_gpu_provider_lock, memory_order_acquire)) { }
}

static void simple_gpu_unlock(void) {
    atomic_flag_clear_explicit(&simple_gpu_provider_lock, memory_order_release);
}

/* Forward declaration: the definition is Windows-only and lives near the
 * bottom of this file, but simple_gpu_open() below calls it. Without this
 * clang-cl emits an implicit declaration returning int and then errors with
 * "conflicting types for 'runtime_dynload_open_utf8'" at the real HMODULE
 * definition, which broke the Windows MSVC stage 2 runtime probe. */
#ifdef _WIN32
static HMODULE runtime_dynload_open_utf8(const char *path);
#endif

static void *simple_gpu_open(const char *path) {
#ifdef _WIN32
    return (void *)runtime_dynload_open_utf8(path);
#else
    return dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

static void *simple_gpu_symbol(void *handle, const char *name) {
    if (!handle || !name) return NULL;
#ifdef _WIN32
    return (void *)GetProcAddress((HMODULE)handle, name);
#else
    return dlsym(handle, name);
#endif
}

static int simple_gpu_close(void *handle) {
    if (!handle) return 1;
#ifdef _WIN32
    return FreeLibrary((HMODULE)handle) != 0;
#else
    return dlclose(handle) == 0;
#endif
}

static SimpleGpuProviderState *simple_gpu_state(int64_t backend_bit) {
    size_t i;
    for (i = 0; i < sizeof(simple_gpu_providers) / sizeof(simple_gpu_providers[0]); i++) {
        if (simple_gpu_providers[i].backend_bit == backend_bit) return &simple_gpu_providers[i];
    }
    return NULL;
}

static const char *const simple_cuda_required[] = {
    "rt_cuda_provider_available", "rt_cuda_provider_device_count", "rt_cuda_init",
    "rt_cuda_device_get", "rt_cuda_device_compute_capability", "rt_cuda_ctx_create",
    "rt_cuda_ctx_set_current", "rt_cuda_ctx_destroy", "rt_cuda_ctx_synchronize",
    "rt_cuda_mem_alloc", "rt_cuda_mem_free", "rt_cuda_memcpy_htod",
    "rt_cuda_memcpy_dtoh", "rt_cuda_memcpy_dtod", "rt_cuda_memset",
    "rt_cuda_memset_d32", "rt_cuda_module_load_data_bytes", "rt_cuda_module_unload",
    "rt_cuda_launch_kernel_name", "rt_cuda_sync", "rt_cuda_device_name",
    "rt_cuda_get_error_string"
};

static const char *const simple_vulkan_required[] = {
    "rt_vulkan_provider_is_available", "rt_vulkan_provider_device_count",
    "rt_vk_provider_available", "rt_vulkan_init", "rt_vulkan_shutdown",
    "rt_vulkan_select_device", "rt_vulkan_alloc_buffer", "rt_vulkan_free_buffer",
    "rt_vulkan_copy_to_buffer_raw", "rt_vulkan_copy_from_buffer_raw",
    "rt_vulkan_copy_from_buffer_strided_raw", "rt_vulkan_copy_from_buffer_regions_raw",
    "rt_vulkan_compile_spirv_raw", "rt_vulkan_destroy_shader",
    "rt_vulkan_create_compute_pipeline_raw", "rt_vulkan_destroy_pipeline",
    "rt_vulkan_create_descriptor_set", "rt_vulkan_bind_buffer",
    "rt_vulkan_destroy_descriptor_set", "rt_vulkan_begin_compute",
    "rt_vulkan_bind_pipeline", "rt_vulkan_bind_descriptors",
    "rt_vulkan_push_constants_raw", "rt_vulkan_dispatch", "rt_vulkan_end_compute",
    "rt_vulkan_discard_command", "rt_vulkan_fence_submission_supported",
    "rt_vulkan_accepted_compute_submit_count", "rt_vulkan_submit_and_wait_fence",
    "rt_vulkan_submit_no_wait", "rt_vulkan_wait_fence", "rt_vulkan_destroy_fence",
    "rt_vulkan_wait_idle", "rt_vulkan_device_name", "rt_vulkan_device_type",
    "rt_vulkan_selected_device_type", "rt_vulkan_device_driver_identity",
    "rt_vulkan_selected_device_driver_identity",
    "rt_vulkan_selected_device_driver_identity_hash", "rt_vulkan_get_last_error",
    "rt_vulkan_init_headless_present", "rt_vulkan_init_window_present",
    "rt_vulkan_init_external_window_present", "rt_vulkan_present_buffer",
    "rt_vulkan_present_buffer_regions_raw", "rt_vulkan_last_present_copy_bytes",
    "rt_vulkan_last_present_copy_rects", "rt_vulkan_destroy_swapchain"
};

static const char *const simple_metal_required[] = {
    "rt_metal_init", "rt_metal_is_available", "rt_metal_device_count",
    "rt_metal_device_name", "rt_metal_device_memory", "rt_metal_create_device",
    "rt_metal_destroy_device", "rt_metal_alloc_buffer", "rt_metal_free_buffer",
    "rt_metal_destroy_shader", "rt_metal_destroy_pipeline", "rt_metal_dispatch_compute",
    "rt_metal_create_compute_encoder", "rt_metal_end_compute_encoder",
    "rt_metal_destroy_compute_encoder", "rt_metal_set_buffer", "rt_metal_get_last_error",
    "rt_metal_create_render_pipeline", "rt_metal_destroy_render_pipeline",
    "rt_metal_create_texture", "rt_metal_free_texture", "rt_metal_begin_render_pass",
    "rt_metal_end_render_pass", "rt_metal_draw_indexed", "rt_metal_draw_primitives",
    "rt_metal_create_command_queue", "rt_metal_destroy_command_queue",
    "rt_metal_create_command_buffer", "rt_metal_commit_command_buffer",
    "rt_metal_wait_completed", "rt_metal_destroy_command_buffer",
    "rt_metal_create_sampler", "rt_metal_destroy_sampler", "rt_metal_set_viewport",
    "rt_metal_set_scissor", "rt_metal_create_swapchain", "rt_metal_destroy_swapchain",
    "rt_metal_present", "rt_metal_run_blit_frame", "rt_metal_run_compute_frame",
    "rt_metal_compile_shader_raw", "rt_metal_create_compute_pipeline_raw",
    "rt_metal_load_library_raw", "rt_metal_buffer_upload_raw",
    "rt_metal_buffer_download_raw", "rt_metal_set_bytes_raw"
};

static int simple_gpu_has_required(void *handle, const char *const *names, size_t count) {
    size_t i;
    for (i = 0; i < count; i++) if (!simple_gpu_symbol(handle, names[i])) return 0;
    return 1;
}

static int simple_gpu_validate_surface(
        int64_t backend_bit, void *handle,
        int64_t *abi_version, int64_t *backend_bits) {
    typedef int64_t (*QueryFn)(void);
    QueryFn abi = (QueryFn)simple_gpu_symbol(handle, "rt_simple_gpu_provider_abi_version");
    QueryFn bits = (QueryFn)simple_gpu_symbol(handle, "rt_simple_gpu_provider_backend_bits");
    const char *const *required = NULL;
    size_t count = 0;
    if (!abi || !bits || abi() != SIMPLE_GPU_PROVIDER_ABI_V1) return 0;
    *abi_version = SIMPLE_GPU_PROVIDER_ABI_V1;
    *backend_bits = bits();
    if ((*backend_bits & backend_bit) == 0) return 0;
    if (backend_bit == SIMPLE_GPU_BACKEND_CUDA) {
        required = simple_cuda_required;
        count = sizeof(simple_cuda_required) / sizeof(simple_cuda_required[0]);
    } else if (backend_bit == SIMPLE_GPU_BACKEND_VULKAN) {
        required = simple_vulkan_required;
        count = sizeof(simple_vulkan_required) / sizeof(simple_vulkan_required[0]);
    } else if (backend_bit == SIMPLE_GPU_BACKEND_METAL) {
        required = simple_metal_required;
        count = sizeof(simple_metal_required) / sizeof(simple_metal_required[0]);
    }
    return required && simple_gpu_has_required(handle, required, count);
}

static void simple_gpu_clear_state_locked(SimpleGpuProviderState *state) {
    state->handle = NULL;
    state->abi_version = 0;
    state->backend_bits = 0;
    state->path = NULL;
    state->in_flight = 0;
    state->phase = SIMPLE_GPU_PROVIDER_EMPTY_V1;
}

static int simple_gpu_load_v1(SimpleGpuProviderState *state) {
    const char *path;
    char *path_copy = NULL;
    void *handle;
    int64_t abi_version = 0;
    int64_t backend_bits = 0;
    int valid = 0;
    int close_ok;

    simple_gpu_lock();
    if (state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1) {
        simple_gpu_unlock();
        return 1;
    }
    if (state->phase != SIMPLE_GPU_PROVIDER_EMPTY_V1) {
        simple_gpu_unlock();
        return 0;
    }
    state->phase = SIMPLE_GPU_PROVIDER_LOADING_V1;
    simple_gpu_unlock();

    path = getenv(state->path_env);
    if (path && path[0]) {
        path_copy = (char *)malloc(strlen(path) + 1);
        if (path_copy) memcpy(path_copy, path, strlen(path) + 1);
    }
    handle = path_copy ? simple_gpu_open(path_copy) : NULL;
    if (handle) valid = simple_gpu_validate_surface(
        state->backend_bit, handle, &abi_version, &backend_bits);

    simple_gpu_lock();
    if (state->phase != SIMPLE_GPU_PROVIDER_LOADING_V1) {
        simple_gpu_unlock();
        if (handle) simple_gpu_close(handle);
        free(path_copy);
        return 0;
    }
    if (valid && state->generation != UINT64_MAX) {
        state->handle = handle;
        state->abi_version = abi_version;
        state->backend_bits = backend_bits;
        state->path = path_copy;
        state->generation++;
        state->phase = SIMPLE_GPU_PROVIDER_ACTIVE_V1;
        simple_gpu_unlock();
        return 1;
    }
    if (!handle) {
        state->phase = SIMPLE_GPU_PROVIDER_FAILED_V1;
        simple_gpu_unlock();
        free(path_copy);
        return 0;
    }
    state->handle = handle;
    state->path = path_copy;
    state->phase = SIMPLE_GPU_PROVIDER_CLOSING_V1;
    simple_gpu_unlock();
    close_ok = simple_gpu_close(handle);
    simple_gpu_lock();
    if (close_ok) {
        simple_gpu_clear_state_locked(state);
        state->phase = SIMPLE_GPU_PROVIDER_FAILED_V1;
    } else {
        state->phase = SIMPLE_GPU_PROVIDER_FAILED_V1;
    }
    simple_gpu_unlock();
    if (close_ok) free(path_copy);
    return 0;
}

static int simple_gpu_ensure_active_v1(int64_t backend_bit) {
    SimpleGpuProviderState *state = simple_gpu_state(backend_bit);
    int active;
    if (!state) return 0;
    simple_gpu_lock();
    active = state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1;
    simple_gpu_unlock();
    return active || simple_gpu_load_v1(state);
}

static int simple_gpu_call_acquire_v1(
        int64_t backend_bit, const char *name, SimpleGpuCallPinV1 *out) {
    SimpleGpuProviderState *state;
    void *symbol;
    if (!out) return 0;
    memset(out, 0, sizeof(*out));
    if (!simple_gpu_ensure_active_v1(backend_bit)) return 0;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (!state || state->phase != SIMPLE_GPU_PROVIDER_ACTIVE_V1 ||
            state->generation == 0 || state->in_flight == UINT64_MAX) {
        simple_gpu_unlock();
        return 0;
    }
    symbol = simple_gpu_symbol(state->handle, name);
    if (!symbol) {
        simple_gpu_unlock();
        return 0;
    }
    state->in_flight++;
    out->state = state;
    out->symbol = symbol;
    out->generation = state->generation;
    out->active = 1;
    simple_gpu_unlock();
    return 1;
}

static void simple_gpu_call_release_v1(SimpleGpuCallPinV1 *pin) {
    /* This pin covers synchronous host execution only. Device resources and
     * asynchronous completions need their own fence-backed lifetime owner. */
    if (!pin || !pin->active || !pin->state) return;
    simple_gpu_lock();
    if (pin->state->generation == pin->generation &&
            pin->state->in_flight > 0)
        pin->state->in_flight--;
    simple_gpu_unlock();
    pin->active = 0;
}

#ifdef SIMPLE_GPU_PROVIDER_TEST_HOOKS
uint64_t simple_gpu_test_generation_v1(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    uint64_t generation = 0;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1)
        generation = state->generation;
    simple_gpu_unlock();
    return generation;
}
#endif

int64_t rt_gpu_provider_loaded(int64_t backend_bit) {
    return simple_gpu_ensure_active_v1(backend_bit);
}

int64_t rt_gpu_provider_abi_version(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1)
        value = state->abi_version;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_backend_bits(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1)
        value = state->backend_bits;
    simple_gpu_unlock();
    return value;
}

const char *rt_gpu_provider_path(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    size_t length;
    simple_gpu_path_copy_v1[0] = '\0';
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 && state->path) {
        length = strlen(state->path);
        if (length < sizeof(simple_gpu_path_copy_v1))
            memcpy(simple_gpu_path_copy_v1, state->path, length + 1);
    }
    simple_gpu_unlock();
    return simple_gpu_path_copy_v1;
}

int64_t rt_gpu_provider_unload(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    void *handle;
    char *path;
    uint64_t generation;
    int close_ok;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (!state) {
        simple_gpu_unlock();
        return 0;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_EMPTY_V1) {
        simple_gpu_unlock();
        return 1;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_LOADING_V1 ||
            state->phase == SIMPLE_GPU_PROVIDER_CLOSING_V1) {
        simple_gpu_unlock();
        return 0;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1)
        state->phase = SIMPLE_GPU_PROVIDER_RETIRING_V1;
    /* Retirement rejects new calls. A busy result deliberately requires the
     * owner to retry after all synchronous call pins have drained. */
    if (state->phase == SIMPLE_GPU_PROVIDER_RETIRING_V1 &&
            state->in_flight != 0) {
        simple_gpu_unlock();
        return 0;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_FAILED_V1 && !state->handle) {
        simple_gpu_clear_state_locked(state);
        simple_gpu_unlock();
        return 1;
    }
    if ((state->phase != SIMPLE_GPU_PROVIDER_RETIRING_V1 &&
            state->phase != SIMPLE_GPU_PROVIDER_FAILED_V1) || !state->handle) {
        simple_gpu_unlock();
        return 0;
    }
    handle = state->handle;
    path = state->path;
    generation = state->generation;
    state->phase = SIMPLE_GPU_PROVIDER_CLOSING_V1;
    simple_gpu_unlock();
    close_ok = simple_gpu_close(handle);
    simple_gpu_lock();
    if (state->phase != SIMPLE_GPU_PROVIDER_CLOSING_V1 ||
            state->generation != generation || state->handle != handle) {
        simple_gpu_unlock();
        return 0;
    }
    if (!close_ok) {
        state->phase = SIMPLE_GPU_PROVIDER_FAILED_V1;
        simple_gpu_unlock();
        return 0;
    }
    simple_gpu_clear_state_locked(state);
    simple_gpu_unlock();
    free(path);
    return 1;
}

#define GPU_CALL0(ret, name, bit, provider_name, unavailable) \
    ret name(void) { typedef ret (*Fn)(void); SimpleGpuCallPinV1 pin; ret result; \
        if (!simple_gpu_call_acquire_v1(bit, provider_name, &pin)) return unavailable; \
        result = ((Fn)pin.symbol)(); simple_gpu_call_release_v1(&pin); return result; }
#define GPU_CALL1(ret, name, bit, provider_name, unavailable, t1) \
    ret name(t1 a1) { typedef ret (*Fn)(t1); SimpleGpuCallPinV1 pin; ret result; \
        if (!simple_gpu_call_acquire_v1(bit, provider_name, &pin)) return unavailable; \
        result = ((Fn)pin.symbol)(a1); simple_gpu_call_release_v1(&pin); return result; }
#define GPU_CALL2(ret, name, bit, provider_name, unavailable, t1, t2) \
    ret name(t1 a1, t2 a2) { typedef ret (*Fn)(t1,t2); SimpleGpuCallPinV1 pin; ret result; \
        if (!simple_gpu_call_acquire_v1(bit, provider_name, &pin)) return unavailable; \
        result = ((Fn)pin.symbol)(a1,a2); simple_gpu_call_release_v1(&pin); return result; }
#define GPU_CALL3(ret, name, bit, provider_name, unavailable, t1, t2, t3) \
    ret name(t1 a1, t2 a2, t3 a3) { typedef ret (*Fn)(t1,t2,t3); SimpleGpuCallPinV1 pin; ret result; \
        if (!simple_gpu_call_acquire_v1(bit, provider_name, &pin)) return unavailable; \
        result = ((Fn)pin.symbol)(a1,a2,a3); simple_gpu_call_release_v1(&pin); return result; }
#define GPU_CALL4(ret, name, bit, provider_name, unavailable, t1, t2, t3, t4) \
    ret name(t1 a1, t2 a2, t3 a3, t4 a4) { typedef ret (*Fn)(t1,t2,t3,t4); SimpleGpuCallPinV1 pin; ret result; \
        if (!simple_gpu_call_acquire_v1(bit, provider_name, &pin)) return unavailable; \
        result = ((Fn)pin.symbol)(a1,a2,a3,a4); simple_gpu_call_release_v1(&pin); return result; }

GPU_CALL0(int64_t, rt_cuda_available, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_provider_available", 0)
GPU_CALL0(int64_t, rt_cuda_device_count, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_provider_device_count", 0)
GPU_CALL0(int64_t, rt_cuda_init, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_init", 3)
GPU_CALL1(int64_t, rt_cuda_mem_alloc, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_mem_alloc", -3, int64_t)
GPU_CALL3(int64_t, rt_cuda_memset_d32, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memset_d32", -3, int64_t, int64_t, int64_t)
GPU_CALL3(int64_t, rt_cuda_memcpy_dtoh, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memcpy_dtoh", -3, int64_t, int64_t, int64_t)

/* E2 (streams/events/async copies/extended launch): forwarded to the CUDA
 * provider by the exact same symbol names the Simple-facing externs use
 * (`src/lib/nogc_sync_mut/cuda/sffi.spl`) and matching the Rust runtime's
 * ABI 1:1 (`src/compiler_rust/runtime/src/cuda_runtime.rs`). Unavailable
 * sentinels mirror the Rust `#[cfg(not(feature = "cuda"))]` twins exactly
 * (-3 for int64_t returns, -3.0 for the f64 elapsed-time return) so a
 * missing/incompatible provider fails the same way on both lanes instead
 * of lying with a fabricated success value. */
GPU_CALL1(int64_t, rt_cuda_stream_create, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_stream_create", -3, int64_t)
GPU_CALL1(int64_t, rt_cuda_stream_destroy, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_stream_destroy", -3, int64_t)
GPU_CALL1(int64_t, rt_cuda_stream_synchronize, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_stream_synchronize", -3, int64_t)
GPU_CALL1(int64_t, rt_cuda_event_create, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_event_create", -3, int64_t)
GPU_CALL1(int64_t, rt_cuda_event_destroy, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_event_destroy", -3, int64_t)
GPU_CALL2(int64_t, rt_cuda_event_record, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_event_record", -3, int64_t, int64_t)
GPU_CALL1(int64_t, rt_cuda_event_synchronize, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_event_synchronize", -3, int64_t)
GPU_CALL2(double, rt_cuda_event_elapsed_ms, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_event_elapsed_ms", -3.0, int64_t, int64_t)
GPU_CALL4(int64_t, rt_cuda_memcpy_htod_async, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memcpy_htod_async", -3, int64_t, int64_t, int64_t, int64_t)
GPU_CALL4(int64_t, rt_cuda_memcpy_dtoh_async, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memcpy_dtoh_async", -3, int64_t, int64_t, int64_t, int64_t)

/* 12 C-ABI params (module, (func_name_ptr, func_name_len) for the Simple
 * `text` arg, then grid/block/shared_bytes/stream/args_ptr) matching
 * rt_cuda_launch_kernel_ex's Rust signature exactly — too wide for the
 * GPU_CALLn macros above, so written out directly. */
int64_t rt_cuda_launch_kernel_ex(int64_t module, const uint8_t *func_name_ptr, uint64_t func_name_len,
                                  int64_t grid_x, int64_t grid_y, int64_t grid_z,
                                  int64_t block_x, int64_t block_y, int64_t block_z,
                                  int64_t shared_bytes, int64_t stream, int64_t args_ptr) {
    typedef int64_t (*Fn)(int64_t, const uint8_t *, uint64_t, int64_t, int64_t, int64_t,
                           int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_launch_kernel_ex", &pin))
        return -3;
    result = ((Fn)pin.symbol)(module, func_name_ptr, func_name_len,
        grid_x, grid_y, grid_z, block_x, block_y, block_z,
        shared_bytes, stream, args_ptr);
    simple_gpu_call_release_v1(&pin);
    return result;
}

GPU_CALL0(int64_t, rt_vulkan_is_available, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_provider_is_available", 0)
GPU_CALL0(int64_t, rt_vulkan_device_count, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_provider_device_count", 0)
GPU_CALL0(int32_t, rt_vk_available, SIMPLE_GPU_BACKEND_VULKAN, "rt_vk_provider_available", 0)
GPU_CALL0(int64_t, rt_vulkan_init, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_init", 0)
/* Async-session revision 1 is an OPTIONAL extension of provider ABI v1.
 * Older core-v1 providers remain usable; partial async surfaces cannot admit
 * a session. Keep core required symbols unchanged. */
static const char *const simple_vulkan_async_v1[] = {
    "rt_vulkan_async_session_supported", "rt_vulkan_async_session_create",
    "rt_vulkan_async_session_create_with_wait", "rt_vulkan_async_session_acquire",
    "rt_vulkan_async_session_command", "rt_vulkan_async_session_submit",
    "rt_vulkan_async_session_poll", "rt_vulkan_async_session_retire",
    "rt_vulkan_async_session_receipt", "rt_vulkan_async_session_cancel",
    "rt_vulkan_async_session_close", "rt_vulkan_async_session_capacity",
    "rt_vulkan_async_session_in_flight", "rt_vulkan_async_session_published_sequence",
    "rt_vulkan_async_session_recover", "rt_vulkan_async_session_abandon_device",
    "rt_vulkan_async_session_snapshot", "rt_vulkan_async_session_snapshot_word"
};

int64_t rt_vulkan_async_session_supported(void) {
    typedef int64_t (*QueryFn)(void);
    int64_t supported = 0;
    simple_gpu_lock();
    SimpleGpuProviderState *state = simple_gpu_state(SIMPLE_GPU_BACKEND_VULKAN);
    if (state && simple_gpu_load_locked(state) &&
        simple_gpu_has_required(state->handle, simple_vulkan_async_v1,
            sizeof(simple_vulkan_async_v1) / sizeof(simple_vulkan_async_v1[0]))) {
        QueryFn query = (QueryFn)simple_gpu_symbol(state->handle, "rt_vulkan_async_session_supported");
        supported = query() == 1;
    }
    simple_gpu_unlock();
    return supported;
}

int64_t rt_vulkan_async_session_create_with_wait(int64_t capacity, int64_t timeout_ns) {
    typedef int64_t (*CreateFn)(int64_t, int64_t);
    if (!rt_vulkan_async_session_supported()) return 0;
    CreateFn create = (CreateFn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_create_with_wait");
    return create ? create(capacity, timeout_ns) : 0;
}

int64_t rt_vulkan_async_session_create(int64_t capacity) {
    return rt_vulkan_async_session_create_with_wait(capacity, 1000000);
}
/* Keep the async extension forwards explicit.  The ordinary GPU_CALLn macros
 * are ABI-correct, but their generated function names are invisible to the
 * source-level C/Rust dual-lane ratchet.  These wrappers preserve the same
 * provider lookup and fail-closed sentinels while making the C lane
 * mechanically auditable. */
int64_t rt_vulkan_async_session_acquire(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_acquire");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_command(int64_t session, int64_t token) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_command");
    return fn ? fn(session, token) : -1;
}
int64_t rt_vulkan_async_session_submit(int64_t session, int64_t token) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_submit");
    return fn ? fn(session, token) : -1;
}
int64_t rt_vulkan_async_session_poll(int64_t session, int64_t token) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_poll");
    return fn ? fn(session, token) : -1;
}
int64_t rt_vulkan_async_session_retire(int64_t session, int64_t token) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_retire");
    return fn ? fn(session, token) : -1;
}
int64_t rt_vulkan_async_session_receipt(int64_t session, int64_t sequence) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_receipt");
    return fn ? fn(session, sequence) : 0;
}
int64_t rt_vulkan_async_session_cancel(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_cancel");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_close(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_close");
    return fn ? fn(session) : 0;
}
int64_t rt_vulkan_async_session_capacity(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_capacity");
    return fn ? fn(session) : 0;
}
int64_t rt_vulkan_async_session_in_flight(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_in_flight");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_published_sequence(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_published_sequence");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_recover(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_recover");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_abandon_device(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_abandon_device");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_snapshot(int64_t session) {
    typedef int64_t (*Fn)(int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_snapshot");
    return fn ? fn(session) : -1;
}
int64_t rt_vulkan_async_session_snapshot_word(int64_t session, int64_t snapshot, int64_t index) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_VULKAN,
        "rt_vulkan_async_session_snapshot_word");
    return fn ? fn(session, snapshot, index) : -1;
}
GPU_CALL2(int64_t, rt_vulkan_alloc_buffer, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_alloc_buffer", 0, int64_t, int64_t)

static int simple_gpu_array_to_bytes(int64_t array_value, uint8_t **bytes, int64_t *length) {
    SplArray *array = (SplArray *)(intptr_t)array_value;
    int64_t len = rt_array_len(array);
    int64_t i;
    uint8_t *out;
    if (!array || len < 0 || len > INT32_MAX) return 0;
    out = len == 0 ? NULL : (uint8_t *)malloc((size_t)len);
    if (len != 0 && !out) return 0;
    for (i = 0; i < len; i++) {
        int64_t value = rt_value_as_int(rt_array_get(array, i));
        if (value < 0 || value > 255) { free(out); return 0; }
        out[i] = (uint8_t)value;
    }
    *bytes = out;
    *length = len;
    return 1;
}

int64_t rt_metal_compile_shader(int64_t device, int64_t source) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    const uint8_t *data = rt_string_data(source);
    int64_t len = rt_string_len(source);
    int64_t result;
    if (!data || len < 0 || !simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_compile_shader_raw", &pin))
        return 0;
    result = ((Fn)pin.symbol)(device, (int64_t)(intptr_t)data, len);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_metal_create_compute_pipeline(int64_t device, int64_t shader, int64_t entry) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    const uint8_t *data = rt_string_data(entry);
    int64_t len = rt_string_len(entry);
    int64_t result;
    if (!data || len < 0 || !simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_create_compute_pipeline_raw", &pin))
        return 0;
    result = ((Fn)pin.symbol)(device, shader, (int64_t)(intptr_t)data, len);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_metal_load_library_array(int64_t device, int64_t array_value) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result;
    if (!simple_gpu_array_to_bytes(array_value, &bytes, &len)) return 0;
    if (!simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_load_library_raw", &pin)) {
        free(bytes);
        return 0;
    }
    result = ((Fn)pin.symbol)(device, (int64_t)(intptr_t)bytes, len);
    simple_gpu_call_release_v1(&pin);
    free(bytes);
    return result;
}

int64_t rt_metal_buffer_upload(int64_t buffer, int64_t array_value, int64_t requested_len) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result;
    if (!simple_gpu_array_to_bytes(array_value, &bytes, &len) ||
            requested_len != len) {
        free(bytes);
        return 0;
    }
    if (!simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_buffer_upload_raw", &pin)) {
        free(bytes);
        return 0;
    }
    result = ((Fn)pin.symbol)(buffer, (int64_t)(intptr_t)bytes, len);
    simple_gpu_call_release_v1(&pin);
    free(bytes);
    return result;
}

int64_t rt_metal_buffer_download(int64_t array_value, int64_t buffer, int64_t requested_len) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    SplArray *array = (SplArray *)(intptr_t)array_value;
    int64_t len = rt_array_len(array); int64_t i; int64_t result;
    uint8_t *bytes;
    if (!array || len < 0 || requested_len != len) return 0;
    bytes = len == 0 ? NULL : (uint8_t *)malloc((size_t)len);
    if (len != 0 && !bytes) return 0;
    if (!simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_buffer_download_raw", &pin)) {
        free(bytes);
        return 0;
    }
    result = ((Fn)pin.symbol)((int64_t)(intptr_t)bytes, buffer, len);
    simple_gpu_call_release_v1(&pin);
    if (result) for (i = 0; i < len; i++) rt_array_set(array, i, rt_value_int(bytes[i]));
    free(bytes); return result;
}

int64_t rt_metal_set_bytes(int64_t encoder, int64_t array_value, int64_t requested_len, int64_t index) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result;
    if (!simple_gpu_array_to_bytes(array_value, &bytes, &len) ||
            requested_len != len) {
        free(bytes);
        return 0;
    }
    if (!simple_gpu_call_acquire_v1(
            SIMPLE_GPU_BACKEND_METAL, "rt_metal_set_bytes_raw", &pin)) {
        free(bytes);
        return 0;
    }
    result = ((Fn)pin.symbol)(encoder, (int64_t)(intptr_t)bytes, len, index);
    simple_gpu_call_release_v1(&pin);
    free(bytes);
    return result;
}

#ifdef _WIN32
static HMODULE runtime_dynload_open_utf8(const char *path) {
    int wide_len;
    wchar_t *wide_path;
    HMODULE handle;
    if (!path || !path[0]) return NULL;
    wide_len = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS,
        path, -1, NULL, 0);
    if (wide_len <= 0) return NULL;
    wide_path = (wchar_t*)malloc((size_t)wide_len * sizeof(wchar_t));
    if (!wide_path) return NULL;
    if (MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS,
            path, -1, wide_path, wide_len) != wide_len) {
        free(wide_path);
        return NULL;
    }
    handle = LoadLibraryW(wide_path);
    free(wide_path);
    return handle;
}
#endif

int64_t spl_dynlib_snapshot_linux(int64_t path_value) {
#if defined(__linux__)
    const char* path = rt_interp_cstr(path_value);
    if (!path) return -1;
    int source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (source < 0) return -1;
    struct stat source_stat;
    if (fstat(source, &source_stat) != 0 || !S_ISREG(source_stat.st_mode) ||
        source_stat.st_size < 0 || (uint64_t)source_stat.st_size > UINT64_C(1073741824)) {
        close(source);
        return -1;
    }
    int snapshot = (int)syscall(SYS_memfd_create, "simple-sffi-provider",
                                MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (snapshot < 0) { close(source); return -1; }
    uint8_t buffer[65536];
    uint64_t total = 0;
    for (;;) {
        ssize_t got = read(source, buffer, sizeof(buffer));
        if (got == 0) break;
        if (got < 0) {
            if (errno == EINTR) continue;
            close(source); close(snapshot); return -1;
        }
        if ((uint64_t)got > UINT64_C(1073741824) - total) {
            close(source); close(snapshot); return -1;
        }
        total += (uint64_t)got;
        ssize_t offset = 0;
        while (offset < got) {
            ssize_t put = write(snapshot, buffer + offset, (size_t)(got - offset));
            if (put < 0 && errno == EINTR) continue;
            if (put <= 0) { close(source); close(snapshot); return -1; }
            offset += put;
        }
    }
    if (total != (uint64_t)source_stat.st_size || close(source) != 0 ||
        lseek(snapshot, 0, SEEK_SET) < 0 ||
        fcntl(snapshot, F_ADD_SEALS,
              F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL) != 0) {
        close(snapshot);
        return -1;
    }
    return (int64_t)snapshot;
#else
    (void)path_value;
    return -1;
#endif
}

int64_t spl_dlopen(int64_t path_value) {
    int64_t handle = 0;
    return spl_dlopen_checked(path_value, &handle) == 0 ? handle : 0;
}

int64_t spl_dlopen_checked(int64_t path_value, int64_t* out_handle) {
    if (!out_handle) return 1;
    *out_handle = 0;
    const char* path = rt_interp_cstr(path_value);
    if (!path || !path[0]) return 1;
#ifdef _WIN32
    HMODULE handle = runtime_dynload_open_utf8(path);
    if (!handle) return 2;
    *out_handle = (int64_t)(intptr_t)handle;
#else
    void* handle = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (!handle) return 2;
    *out_handle = (int64_t)(intptr_t)handle;
#endif
    return 0;
}

int64_t spl_dlsym(int64_t handle, int64_t name_value) {
    int64_t symbol = 0;
    return spl_dlsym_checked(handle, name_value, &symbol) == 0 ? symbol : 0;
}

int64_t spl_dlsym_checked(int64_t handle, int64_t name_value, int64_t* out_symbol) {
    if (!out_symbol) return 1;
    *out_symbol = 0;
    const char* name = rt_interp_cstr(name_value);
    if (!handle || !name || !name[0]) return 1;
#ifdef _WIN32
    FARPROC symbol = GetProcAddress((HMODULE)(intptr_t)handle, name);
    if (!symbol) return 3;
    *out_symbol = (int64_t)(intptr_t)symbol;
#else
    void* symbol = dlsym((void*)(intptr_t)handle, name);
    if (!symbol) return 3;
    *out_symbol = (int64_t)(intptr_t)symbol;
#endif
    return 0;
}

int64_t spl_dlsym_process_checked(int64_t name_value, int64_t* out_symbol) {
    if (!out_symbol) return 1;
    *out_symbol = 0;
    const char* name = rt_interp_cstr(name_value);
    if (!name || !name[0]) return 1;
#ifdef _WIN32
    HMODULE process = GetModuleHandleA(NULL);
    if (!process) return 3;
    FARPROC symbol = GetProcAddress(process, name);
    if (!symbol) return 3;
    *out_symbol = (int64_t)(intptr_t)symbol;
#else
    void* symbol = dlsym(NULL, name);
    if (!symbol) return 3;
    *out_symbol = (int64_t)(intptr_t)symbol;
#endif
    return 0;
}

int64_t spl_dlclose(int64_t handle) {
    if (!handle) return -1;
#ifdef _WIN32
    return FreeLibrary((HMODULE)(intptr_t)handle) ? 0 : -1;
#else
    return (int64_t)dlclose((void*)(intptr_t)handle);
#endif
}
