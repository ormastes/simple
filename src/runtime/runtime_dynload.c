/* Hosted dynamic loading for pure-Simple native binaries. */

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#endif

#include "runtime.h"

#include <stdatomic.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

enum {
    SIMPLE_GPU_PROVIDER_ABI_V1 = 1,
    SIMPLE_GPU_BACKEND_CUDA = 1,
    SIMPLE_GPU_BACKEND_VULKAN = 2,
    SIMPLE_GPU_BACKEND_METAL = 4
};

typedef struct SimpleGpuProviderState {
    int64_t backend_bit;
    const char *path_env;
    void *handle;
    int64_t abi_version;
    int64_t backend_bits;
    char *path;
    int attempted;
} SimpleGpuProviderState;

static SimpleGpuProviderState simple_gpu_providers[] = {
    {SIMPLE_GPU_BACKEND_CUDA, "SIMPLE_CUDA_PROVIDER_PATH", NULL, 0, 0, NULL, 0},
    {SIMPLE_GPU_BACKEND_VULKAN, "SIMPLE_VULKAN_PROVIDER_PATH", NULL, 0, 0, NULL, 0},
    {SIMPLE_GPU_BACKEND_METAL, "SIMPLE_METAL_PROVIDER_PATH", NULL, 0, 0, NULL, 0}
};
static atomic_flag simple_gpu_provider_lock = ATOMIC_FLAG_INIT;

static void simple_gpu_lock(void) {
    while (atomic_flag_test_and_set_explicit(
        &simple_gpu_provider_lock, memory_order_acquire)) { }
}

static void simple_gpu_unlock(void) {
    atomic_flag_clear_explicit(&simple_gpu_provider_lock, memory_order_release);
}

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

static void simple_gpu_close(void *handle) {
    if (!handle) return;
#ifdef _WIN32
    FreeLibrary((HMODULE)handle);
#else
    dlclose(handle);
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

static int simple_gpu_validate_surface(SimpleGpuProviderState *state, void *handle) {
    typedef int64_t (*QueryFn)(void);
    QueryFn abi = (QueryFn)simple_gpu_symbol(handle, "rt_simple_gpu_provider_abi_version");
    QueryFn bits = (QueryFn)simple_gpu_symbol(handle, "rt_simple_gpu_provider_backend_bits");
    const char *const *required = NULL;
    size_t count = 0;
    if (!abi || !bits || abi() != SIMPLE_GPU_PROVIDER_ABI_V1) return 0;
    state->abi_version = SIMPLE_GPU_PROVIDER_ABI_V1;
    state->backend_bits = bits();
    if ((state->backend_bits & state->backend_bit) == 0) return 0;
    if (state->backend_bit == SIMPLE_GPU_BACKEND_CUDA) {
        required = simple_cuda_required;
        count = sizeof(simple_cuda_required) / sizeof(simple_cuda_required[0]);
    } else if (state->backend_bit == SIMPLE_GPU_BACKEND_VULKAN) {
        required = simple_vulkan_required;
        count = sizeof(simple_vulkan_required) / sizeof(simple_vulkan_required[0]);
    } else if (state->backend_bit == SIMPLE_GPU_BACKEND_METAL) {
        required = simple_metal_required;
        count = sizeof(simple_metal_required) / sizeof(simple_metal_required[0]);
    }
    return required && simple_gpu_has_required(handle, required, count);
}

static void simple_gpu_clear_state(SimpleGpuProviderState *state) {
    simple_gpu_close(state->handle);
    state->handle = NULL;
    state->abi_version = 0;
    state->backend_bits = 0;
    free(state->path);
    state->path = NULL;
}

static int simple_gpu_load_locked(SimpleGpuProviderState *state) {
    const char *path;
    void *handle;
    if (state->attempted) return state->handle != NULL;
    state->attempted = 1;
    path = getenv(state->path_env);
    if (!path || !path[0]) return 0;
    handle = simple_gpu_open(path);
    if (!handle) return 0;
    if (!simple_gpu_validate_surface(state, handle)) {
        simple_gpu_close(handle);
        state->abi_version = 0;
        state->backend_bits = 0;
        return 0;
    }
    state->path = (char *)malloc(strlen(path) + 1);
    if (!state->path) {
        simple_gpu_close(handle);
        state->abi_version = 0;
        state->backend_bits = 0;
        return 0;
    }
    memcpy(state->path, path, strlen(path) + 1);
    state->handle = handle;
    return 1;
}

static void *simple_gpu_provider_symbol(int64_t backend_bit, const char *name) {
    SimpleGpuProviderState *state;
    void *symbol = NULL;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && simple_gpu_load_locked(state)) symbol = simple_gpu_symbol(state->handle, name);
    simple_gpu_unlock();
    return symbol;
}

int64_t rt_gpu_provider_loaded(int64_t backend_bit) {
    return simple_gpu_provider_symbol(backend_bit,
        "rt_simple_gpu_provider_abi_version") != NULL;
}

int64_t rt_gpu_provider_abi_version(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->handle) value = state->abi_version;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_backend_bits(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->handle) value = state->backend_bits;
    simple_gpu_unlock();
    return value;
}

const char *rt_gpu_provider_path(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    const char *value = "";
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->handle && state->path) value = state->path;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_unload(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (!state) {
        simple_gpu_unlock();
        return 0;
    }
    simple_gpu_clear_state(state);
    state->attempted = 0;
    simple_gpu_unlock();
    return 1;
}

#define GPU_CALL0(ret, name, bit, provider_name, unavailable) \
    ret name(void) { typedef ret (*Fn)(void); Fn fn = (Fn)simple_gpu_provider_symbol(bit, provider_name); return fn ? fn() : unavailable; }
#define GPU_CALL1(ret, name, bit, provider_name, unavailable, t1) \
    ret name(t1 a1) { typedef ret (*Fn)(t1); Fn fn = (Fn)simple_gpu_provider_symbol(bit, provider_name); return fn ? fn(a1) : unavailable; }
#define GPU_CALL2(ret, name, bit, provider_name, unavailable, t1, t2) \
    ret name(t1 a1, t2 a2) { typedef ret (*Fn)(t1,t2); Fn fn = (Fn)simple_gpu_provider_symbol(bit, provider_name); return fn ? fn(a1,a2) : unavailable; }
#define GPU_CALL3(ret, name, bit, provider_name, unavailable, t1, t2, t3) \
    ret name(t1 a1, t2 a2, t3 a3) { typedef ret (*Fn)(t1,t2,t3); Fn fn = (Fn)simple_gpu_provider_symbol(bit, provider_name); return fn ? fn(a1,a2,a3) : unavailable; }

GPU_CALL0(int64_t, rt_cuda_available, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_provider_available", 0)
GPU_CALL0(int64_t, rt_cuda_device_count, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_provider_device_count", 0)
GPU_CALL0(int64_t, rt_cuda_init, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_init", 3)
GPU_CALL1(int64_t, rt_cuda_mem_alloc, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_mem_alloc", -3, int64_t)
GPU_CALL3(int64_t, rt_cuda_memset_d32, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memset_d32", -3, int64_t, int64_t, int64_t)
GPU_CALL3(int64_t, rt_cuda_memcpy_dtoh, SIMPLE_GPU_BACKEND_CUDA, "rt_cuda_memcpy_dtoh", -3, int64_t, int64_t, int64_t)

GPU_CALL0(int64_t, rt_vulkan_is_available, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_provider_is_available", 0)
GPU_CALL0(int64_t, rt_vulkan_device_count, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_provider_device_count", 0)
GPU_CALL0(int32_t, rt_vk_available, SIMPLE_GPU_BACKEND_VULKAN, "rt_vk_provider_available", 0)
GPU_CALL0(int64_t, rt_vulkan_init, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_init", 0)
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
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_compile_shader_raw");
    const uint8_t *data = rt_string_data(source);
    int64_t len = rt_string_len(source);
    return fn && data && len >= 0 ? fn(device, (int64_t)(intptr_t)data, len) : 0;
}

int64_t rt_metal_create_compute_pipeline(int64_t device, int64_t shader, int64_t entry) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_create_compute_pipeline_raw");
    const uint8_t *data = rt_string_data(entry);
    int64_t len = rt_string_len(entry);
    return fn && data && len >= 0 ? fn(device, shader, (int64_t)(intptr_t)data, len) : 0;
}

int64_t rt_metal_load_library_array(int64_t device, int64_t array_value) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_load_library_raw");
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result = 0;
    if (fn && simple_gpu_array_to_bytes(array_value, &bytes, &len)) result = fn(device, (int64_t)(intptr_t)bytes, len);
    free(bytes); return result;
}

int64_t rt_metal_buffer_upload(int64_t buffer, int64_t array_value, int64_t requested_len) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_buffer_upload_raw");
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result = 0;
    if (fn && simple_gpu_array_to_bytes(array_value, &bytes, &len) && requested_len == len) result = fn(buffer, (int64_t)(intptr_t)bytes, len);
    free(bytes); return result;
}

int64_t rt_metal_buffer_download(int64_t array_value, int64_t buffer, int64_t requested_len) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_buffer_download_raw");
    SplArray *array = (SplArray *)(intptr_t)array_value;
    int64_t len = rt_array_len(array); int64_t i; int64_t result = 0;
    uint8_t *bytes;
    if (!fn || !array || len < 0 || requested_len != len) return 0;
    bytes = len == 0 ? NULL : (uint8_t *)malloc((size_t)len);
    if (len != 0 && !bytes) return 0;
    result = fn((int64_t)(intptr_t)bytes, buffer, len);
    if (result) for (i = 0; i < len; i++) rt_array_set(array, i, rt_value_int(bytes[i]));
    free(bytes); return result;
}

int64_t rt_metal_set_bytes(int64_t encoder, int64_t array_value, int64_t requested_len, int64_t index) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    Fn fn = (Fn)simple_gpu_provider_symbol(SIMPLE_GPU_BACKEND_METAL, "rt_metal_set_bytes_raw");
    uint8_t *bytes = NULL; int64_t len = 0; int64_t result = 0;
    if (fn && simple_gpu_array_to_bytes(array_value, &bytes, &len) && requested_len == len) result = fn(encoder, (int64_t)(intptr_t)bytes, len, index);
    free(bytes); return result;
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

int64_t spl_dlopen(int64_t path_value) {
    const char* path = rt_interp_cstr(path_value);
    if (!path) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)runtime_dynload_open_utf8(path);
#else
    return (int64_t)(intptr_t)dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

int64_t spl_dlsym(int64_t handle, int64_t name_value) {
    const char* name = rt_interp_cstr(name_value);
    if (!handle || !name) return 0;
#ifdef _WIN32
    return (int64_t)(intptr_t)GetProcAddress((HMODULE)(intptr_t)handle, name);
#else
    return (int64_t)(intptr_t)dlsym((void*)(intptr_t)handle, name);
#endif
}

int64_t spl_dlclose(int64_t handle) {
    if (!handle) return -1;
#ifdef _WIN32
    return FreeLibrary((HMODULE)(intptr_t)handle) ? 0 : -1;
#else
    return (int64_t)dlclose((void*)(intptr_t)handle);
#endif
}
