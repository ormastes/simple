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
#include "simple_gpu_provider_abi_v1.h"

#include <stdatomic.h>
#include <limits.h>
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
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

enum { SIMPLE_GPU_PROVIDER_ABI_V1 = 1 };

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
    const char *digest_env;
    void *handle;
    int64_t abi_version;
    int64_t backend_bits;
    char *path;
    uint64_t generation;
    uint64_t in_flight;
    uint64_t retained;
    uint64_t capability_bits;
    uint64_t provider_identity;
    uint8_t artifact_digest[32];
    int snapshot_fd;
    SimpleGpuProviderAbiV1 api_storage;
    const SimpleGpuProviderAbiV1 *api;
    int authenticated;
    SimpleGpuProviderPhaseV1 phase;
} SimpleGpuProviderState;

typedef struct SimpleGpuCallPinV1 {
    SimpleGpuProviderState *state;
    void *symbol;
    uint64_t generation;
    int active;
} SimpleGpuCallPinV1;

static SimpleGpuProviderState simple_gpu_providers[] = {
    {.backend_bit = SIMPLE_GPU_BACKEND_CUDA,
        .path_env = "SIMPLE_CUDA_PROVIDER_PATH",
        .digest_env = "SIMPLE_CUDA_PROVIDER_SHA256", .snapshot_fd = -1},
    {.backend_bit = SIMPLE_GPU_BACKEND_VULKAN,
        .path_env = "SIMPLE_VULKAN_PROVIDER_PATH",
        .digest_env = "SIMPLE_VULKAN_PROVIDER_SHA256", .snapshot_fd = -1},
    {.backend_bit = SIMPLE_GPU_BACKEND_METAL,
        .path_env = "SIMPLE_METAL_PROVIDER_PATH",
        .digest_env = "SIMPLE_METAL_PROVIDER_SHA256", .snapshot_fd = -1}
};
static atomic_flag simple_gpu_provider_lock = ATOMIC_FLAG_INIT;
#if defined(__linux__)
/* dlopen may retain NODELETE/external references after a successful close.
 * Never reuse an authenticated /proc/self/fd pathname in this process. */
static uint64_t simple_gpu_snapshot_fd_floor_v1 = 1024;
#endif

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

static void simple_gpu_snapshot_close_v1(int snapshot_fd) {
#ifdef _WIN32
    (void)snapshot_fd;
#else
    if (snapshot_fd >= 0) close(snapshot_fd);
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

static int simple_gpu_hex_nibble(char value) {
    if (value >= '0' && value <= '9') return value - '0';
    if (value >= 'a' && value <= 'f') return value - 'a' + 10;
    if (value >= 'A' && value <= 'F') return value - 'A' + 10;
    return -1;
}

static int simple_gpu_digest_matches_expected(
        const char *expected, const uint8_t digest[32]) {
    size_t i;
    if (!expected || strlen(expected) != 64 || !digest) return 0;
    for (i = 0; i < 32; i++) {
        int high = simple_gpu_hex_nibble(expected[i * 2]);
        int low = simple_gpu_hex_nibble(expected[i * 2 + 1]);
        if (high < 0 || low < 0 || digest[i] != (uint8_t)((high << 4) | low))
            return 0;
    }
    return 1;
}

#if defined(__linux__)
static int simple_gpu_snapshot_linux_v1(const char *path) {
    int source, snapshot, unique_snapshot = -1;
    struct stat source_stat;
    uint8_t buffer[65536];
    uint64_t total = 0;
    source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW | O_NONBLOCK);
    if (source < 0 || fstat(source, &source_stat) != 0 ||
            !S_ISREG(source_stat.st_mode) || source_stat.st_size < 0 ||
            (uint64_t)source_stat.st_size > UINT64_C(1073741824)) {
        if (source >= 0) close(source);
        return -1;
    }
    snapshot = (int)syscall(SYS_memfd_create, "simple-gpu-provider-v1",
        MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (snapshot < 0) { close(source); return -1; }
    for (;;) {
        ssize_t got = read(source, buffer, sizeof(buffer));
        ssize_t offset = 0;
        if (got == 0) break;
        if (got < 0) {
            if (errno == EINTR) continue;
            close(source); close(snapshot); return -1;
        }
        if ((uint64_t)got > UINT64_C(1073741824) - total) {
            close(source); close(snapshot); return -1;
        }
        total += (uint64_t)got;
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
        close(snapshot); return -1;
    }
    simple_gpu_lock();
    if (simple_gpu_snapshot_fd_floor_v1 <= INT_MAX) {
        unique_snapshot = fcntl(snapshot, F_DUPFD_CLOEXEC,
            (int)simple_gpu_snapshot_fd_floor_v1);
        if (unique_snapshot >= 0)
            simple_gpu_snapshot_fd_floor_v1 = (uint64_t)unique_snapshot + 1;
    }
    simple_gpu_unlock();
    close(snapshot);
    return unique_snapshot;
}
#endif

static void *simple_gpu_open_with_authentication_v1(
        const char *path, const char *digest_env, uint8_t digest[32],
        int *authenticated, int *retained_snapshot_fd) {
    const char *expected = digest_env ? getenv(digest_env) : NULL;
    void *handle;
    *authenticated = 0;
    *retained_snapshot_fd = -1;
    if (!expected || !expected[0]) return simple_gpu_open(path);
#if defined(__linux__)
    {
        int snapshot = simple_gpu_snapshot_linux_v1(path);
        char snapshot_path[64];
        if (snapshot < 0 || snprintf(snapshot_path, sizeof(snapshot_path),
                "/proc/self/fd/%d", snapshot) <= 0 ||
                !rt_sha256_file_raw_v1(snapshot_path, digest) ||
                !simple_gpu_digest_matches_expected(expected, digest)) {
            if (snapshot >= 0) close(snapshot);
            return NULL;
        }
        handle = simple_gpu_open(snapshot_path);
        if (!handle) close(snapshot);
        else *retained_snapshot_fd = snapshot;
        *authenticated = handle != NULL;
        return handle;
    }
#else
    /* No non-Linux platform currently offers this owner an immutable mapped
     * snapshot primitive. Never upgrade a before/after pathname hash into
     * exact-byte authority; generic ABI admission stays unavailable. */
    (void)path; (void)digest; (void)handle;
    return NULL;
#endif
}

static const SimpleGpuProviderAbiV1 *simple_gpu_validate_api(
        int64_t backend_bit, void *handle, int authenticated) {
    SimpleGpuProviderQueryV1 query;
    const SimpleGpuProviderAbiV1 *api;
    size_t required_size = offsetof(SimpleGpuProviderAbiV1, completion_release) +
        sizeof(((SimpleGpuProviderAbiV1 *)0)->completion_release);
    if (!authenticated || sizeof(void *) != 8 || sizeof(uintptr_t) != 8)
        return NULL;
    query = (SimpleGpuProviderQueryV1)simple_gpu_symbol(
        handle, "simple_gpu_provider_query_v1");
    if (!query || !(api = query()) || api->struct_size < required_size ||
            api->abi_major != SIMPLE_GPU_PROVIDER_ABI_MAJOR ||
            api->abi_minor > SIMPLE_GPU_PROVIDER_ABI_MINOR ||
            api->backend_bits != (uint64_t)backend_bit ||
            api->provider_identity == 0 || api->provider_identity > INT64_MAX ||
            api->operation_count < SIMPLE_GPU_OP_COUNT || !api->operations ||
            !api->shutdown || !api->session_open || !api->session_close ||
            !api->submit || !api->wait || !api->readback ||
            !api->resource_alloc || !api->resource_release ||
            !api->completion_release) return NULL;
    return api;
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
    state->retained = 0;
    state->capability_bits = 0;
    state->provider_identity = 0;
    memset(state->artifact_digest, 0, sizeof(state->artifact_digest));
    state->snapshot_fd = -1;
    memset(&state->api_storage, 0, sizeof(state->api_storage));
    state->api = NULL;
    state->authenticated = 0;
    state->phase = SIMPLE_GPU_PROVIDER_EMPTY_V1;
}

static int simple_gpu_load_v1(SimpleGpuProviderState *state) {
    const char *path;
    char *path_copy = NULL;
    void *handle;
    int64_t abi_version = 0;
    int64_t backend_bits = 0;
    int valid = 0;
    int authenticated = 0;
    uint8_t artifact_digest[32] = {0};
    const SimpleGpuProviderAbiV1 *api = NULL;
    int close_ok;
    int snapshot_fd = -1;

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
    handle = path_copy ? simple_gpu_open_with_authentication_v1(
        path_copy, state->digest_env, artifact_digest, &authenticated,
        &snapshot_fd) : NULL;
    if (handle) valid = simple_gpu_validate_surface(
        state->backend_bit, handle, &abi_version, &backend_bits);
    if (handle && authenticated)
        api = simple_gpu_validate_api(state->backend_bit, handle, authenticated);
    /* The legacy per-symbol surface remains available for existing backends.
     * Generic sessions are admitted only through the authenticated table. */
    if (api) {
        valid = 1;
        abi_version = SIMPLE_GPU_PROVIDER_ABI_V1;
        backend_bits = state->backend_bit;
    }

    simple_gpu_lock();
    if (state->phase != SIMPLE_GPU_PROVIDER_LOADING_V1) {
        simple_gpu_unlock();
        close_ok = handle ? simple_gpu_close(handle) : 1;
        if (close_ok) simple_gpu_snapshot_close_v1(snapshot_fd);
        free(path_copy);
        return 0;
    }
    if (valid && state->generation != UINT64_MAX) {
        state->handle = handle;
        state->abi_version = abi_version;
        state->backend_bits = backend_bits;
        state->path = path_copy;
        state->snapshot_fd = snapshot_fd;
        if (api) {
            state->api_storage = *api;
            state->api = &state->api_storage;
        } else state->api = NULL;
        state->authenticated = api != NULL;
        if (api) {
            state->capability_bits = api->capability_bits;
            state->provider_identity = api->provider_identity;
            memcpy(state->artifact_digest, artifact_digest, 32);
        }
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
    state->snapshot_fd = snapshot_fd;
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
    if (close_ok) {
        simple_gpu_snapshot_close_v1(snapshot_fd);
        free(path_copy);
    }
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

enum { SIMPLE_GPU_OWNER_CAPACITY_V1 = 256 };
enum { SIMPLE_GPU_RESOURCE_MAX_BYTES_V1 = 1073741824 };

static uint64_t simple_gpu_readback_checksum_v1(
        const uint8_t *bytes, uint64_t length) {
    uint64_t value = UINT64_C(14695981039346656037);
    uint64_t i;
    for (i = 0; i < length; i++) {
        value ^= bytes[i];
        value *= UINT64_C(1099511628211);
    }
    return value;
}

typedef struct SimpleGpuOwnedSessionV1 {
    uint64_t token;
    uint64_t generation;
    uint64_t provider_handle;
    uint64_t device;
    uint32_t resources;
    uint32_t completions;
    int quarantined;
    int busy;
    SimpleGpuProviderState *state;
} SimpleGpuOwnedSessionV1;

typedef struct SimpleGpuOwnedResourceV1 {
    uint64_t token;
    uint64_t session_token;
    uint64_t provider_handle;
    uint64_t size_bytes;
    uint64_t generation;
    int quarantined;
    int busy;
    SimpleGpuProviderState *state;
} SimpleGpuOwnedResourceV1;

typedef struct SimpleGpuOwnedCompletionV1 {
    uint64_t token;
    uint64_t session_token;
    uint64_t provider_handle;
    uint64_t correlation_id;
    uint64_t generation;
    uint64_t terminal_resource_token;
    uint64_t checksum;
    uint64_t readback_length;
    int terminal;
    int readback_observed;
    int quarantined;
    int busy;
    SimpleGpuProviderState *state;
} SimpleGpuOwnedCompletionV1;

static SimpleGpuOwnedSessionV1 simple_gpu_sessions[SIMPLE_GPU_OWNER_CAPACITY_V1];
static SimpleGpuOwnedResourceV1 simple_gpu_resources[SIMPLE_GPU_OWNER_CAPACITY_V1];
static SimpleGpuOwnedCompletionV1 simple_gpu_completions[SIMPLE_GPU_OWNER_CAPACITY_V1];

static int simple_gpu_resource_has_completion_locked_v1(
        SimpleGpuOwnedSessionV1 *session, SimpleGpuOwnedResourceV1 *resource) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        SimpleGpuOwnedCompletionV1 *completion = &simple_gpu_completions[i];
        if (completion->token && completion->token != UINT64_MAX &&
                completion->state == session->state &&
                completion->session_token == session->token &&
                completion->generation == session->generation &&
                completion->terminal_resource_token == resource->token)
            return 1;
    }
    return 0;
}

static int simple_gpu_token_exists_locked_v1(uint64_t token) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++)
        if (simple_gpu_sessions[i].token == token ||
                simple_gpu_resources[i].token == token ||
                simple_gpu_completions[i].token == token) return 1;
    return 0;
}

static uint64_t simple_gpu_next_token_locked_v1(void) {
    int attempt;
    for (attempt = 0; attempt < 16; attempt++) {
        uint64_t value = 0;
#ifdef _WIN32
        typedef BOOLEAN (WINAPI *RandomFn)(PVOID, ULONG);
        HMODULE library = LoadLibraryA("advapi32.dll");
        RandomFn fill = library ? (RandomFn)GetProcAddress(library, "SystemFunction036") : NULL;
        if (!fill || !fill(&value, (ULONG)sizeof(value))) {
            if (library) FreeLibrary(library);
            return 0;
        }
        FreeLibrary(library);
#else
        int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
        size_t offset = 0;
        if (fd < 0) return 0;
        while (offset < sizeof(value)) {
            ssize_t got = read(fd, (uint8_t *)&value + offset,
                sizeof(value) - offset);
            if (got < 0 && errno == EINTR) continue;
            if (got <= 0) { close(fd); return 0; }
            offset += (size_t)got;
        }
        close(fd);
#endif
        value &= UINT64_C(0x7fffffffffffffff);
        if (value != 0 && value != UINT64_MAX &&
                !simple_gpu_token_exists_locked_v1(value)) return value;
    }
    return 0;
}

static int simple_gpu_api_acquire_v1(
        int64_t backend_bit, SimpleGpuCallPinV1 *out,
        const SimpleGpuProviderAbiV1 **api) {
    SimpleGpuProviderState *state;
    if (!out || !api) return 0;
    memset(out, 0, sizeof(*out));
    *api = NULL;
    if (!simple_gpu_ensure_active_v1(backend_bit)) return 0;
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (!state || state->phase != SIMPLE_GPU_PROVIDER_ACTIVE_V1 ||
            !state->authenticated || !state->api || state->generation == 0 ||
            state->in_flight == UINT64_MAX) {
        simple_gpu_unlock();
        return 0;
    }
    state->in_flight++;
    out->state = state;
    out->generation = state->generation;
    out->active = 1;
    *api = state->api;
    simple_gpu_unlock();
    return 1;
}

static SimpleGpuOwnedSessionV1 *simple_gpu_session_locked_v1(
        int64_t backend_bit, uint64_t token) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        SimpleGpuOwnedSessionV1 *entry = &simple_gpu_sessions[i];
        if (entry->token == token && entry->state &&
                entry->state->backend_bit == backend_bit &&
                entry->generation == entry->state->generation)
            return entry;
    }
    return NULL;
}

static SimpleGpuOwnedResourceV1 *simple_gpu_resource_locked_v1(
        SimpleGpuOwnedSessionV1 *session, uint64_t token) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        SimpleGpuOwnedResourceV1 *entry = &simple_gpu_resources[i];
        if (entry->token == token && entry->state == session->state &&
                entry->session_token == session->token &&
                entry->generation == session->generation)
            return entry;
    }
    return NULL;
}

static SimpleGpuOwnedCompletionV1 *simple_gpu_completion_locked_v1(
        SimpleGpuOwnedSessionV1 *session, uint64_t token) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        SimpleGpuOwnedCompletionV1 *entry = &simple_gpu_completions[i];
        if (entry->token == token && entry->state == session->state &&
                entry->session_token == session->token &&
                entry->generation == session->generation)
            return entry;
    }
    return NULL;
}

static int simple_gpu_session_children_quarantined_locked_v1(
        SimpleGpuOwnedSessionV1 *session) {
    size_t i;
    uint32_t resources = 0, completions = 0;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        if (simple_gpu_resources[i].state == session->state &&
                simple_gpu_resources[i].session_token == session->token) {
            if (!simple_gpu_resources[i].quarantined) return 0;
            resources++;
        }
        if (simple_gpu_completions[i].state == session->state &&
                simple_gpu_completions[i].session_token == session->token) {
            if (!simple_gpu_completions[i].quarantined) return 0;
            completions++;
        }
    }
    return resources == session->resources && completions == session->completions;
}

static void simple_gpu_session_children_clear_locked_v1(
        SimpleGpuOwnedSessionV1 *session) {
    size_t i;
    for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
        if (simple_gpu_resources[i].state == session->state &&
                simple_gpu_resources[i].session_token == session->token) {
            memset(&simple_gpu_resources[i], 0, sizeof(simple_gpu_resources[i]));
            if (session->state->retained) session->state->retained--;
        }
        if (simple_gpu_completions[i].state == session->state &&
                simple_gpu_completions[i].session_token == session->token) {
            memset(&simple_gpu_completions[i], 0, sizeof(simple_gpu_completions[i]));
            if (session->state->retained) session->state->retained--;
        }
    }
    session->resources = 0;
    session->completions = 0;
}

int64_t rt_gpu_provider_session_open(int64_t backend_bit, int64_t device) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuHandleV1 provider_handle = 0;
    size_t slot;
    uint64_t token, result_token = 0;
    SimpleGpuStatusV1 status, cleanup_status = SIMPLE_GPU_STATUS_OK;
    if (device < 0 || !simple_gpu_api_acquire_v1(backend_bit, &pin, &api)) return 0;
    simple_gpu_lock();
    for (slot = 0; slot < SIMPLE_GPU_OWNER_CAPACITY_V1; slot++)
        if (simple_gpu_sessions[slot].token == 0) break;
    token = slot < SIMPLE_GPU_OWNER_CAPACITY_V1 ? simple_gpu_next_token_locked_v1() : 0;
    if (token) simple_gpu_sessions[slot].token = UINT64_MAX;
    simple_gpu_unlock();
    if (!token) { simple_gpu_call_release_v1(&pin); return 0; }
    status = api->session_open((uint64_t)backend_bit, (uint64_t)device, &provider_handle);
    simple_gpu_lock();
    if (status == SIMPLE_GPU_STATUS_OK && provider_handle &&
            pin.state->generation == pin.generation &&
            pin.state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 &&
            pin.state->retained != UINT64_MAX) {
        simple_gpu_sessions[slot] = (SimpleGpuOwnedSessionV1){
            token, pin.generation, provider_handle, (uint64_t)device,
            0, 0, 0, 0, pin.state};
        pin.state->retained++;
        result_token = token;
    } else {
        simple_gpu_sessions[slot].token = UINT64_MAX;
    }
    simple_gpu_unlock();
    if (!result_token && provider_handle)
        cleanup_status = api->session_close(provider_handle);
    if (!result_token) {
        int uncertain = status != SIMPLE_GPU_STATUS_REJECTED || provider_handle != 0;
        if (provider_handle && cleanup_status == SIMPLE_GPU_STATUS_OK) uncertain = 0;
        simple_gpu_lock();
        if (uncertain &&
                pin.state->retained != UINT64_MAX) {
            simple_gpu_sessions[slot] = (SimpleGpuOwnedSessionV1){
                token, pin.generation, provider_handle, (uint64_t)device,
                0, 0, 1, 0, pin.state};
            pin.state->retained++;
            if (pin.state->phase == SIMPLE_GPU_PROVIDER_RETIRING_V1)
                pin.state->phase = SIMPLE_GPU_PROVIDER_ACTIVE_V1;
        } else memset(&simple_gpu_sessions[slot], 0,
            sizeof(simple_gpu_sessions[slot]));
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return (int64_t)result_token;
}

int64_t rt_gpu_provider_session_close(
        int64_t backend_bit, int64_t session_token) {
    SimpleGpuOwnedSessionV1 snapshot;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuStatusV1 status;
    if (session_token <= 0 || !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return SIMPLE_GPU_STATUS_UNAVAILABLE;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    if (!session || session->busy ||
            ((session->resources || session->completions) &&
                !simple_gpu_session_children_quarantined_locked_v1(session))) {
        simple_gpu_unlock(); simple_gpu_call_release_v1(&pin);
        return session ? SIMPLE_GPU_STATUS_BUSY : SIMPLE_GPU_STATUS_INVALID;
    }
    session->busy = 1;
    snapshot = *session;
    simple_gpu_unlock();
    status = api->session_close(snapshot.provider_handle);
    if (status == SIMPLE_GPU_STATUS_OK) {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, snapshot.token);
        if (session && ((session->resources == 0 && session->completions == 0) ||
                simple_gpu_session_children_quarantined_locked_v1(session))) {
            simple_gpu_session_children_clear_locked_v1(session);
            memset(session, 0, sizeof(*session));
            if (pin.state->retained) pin.state->retained--;
        } else status = SIMPLE_GPU_STATUS_BUSY;
        simple_gpu_unlock();
    } else {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, snapshot.token);
        if (session) session->busy = 0;
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return status;
}

int64_t rt_gpu_provider_quarantine_drain(int64_t backend_bit) {
    size_t attempt;
    for (attempt = 0; attempt < SIMPLE_GPU_OWNER_CAPACITY_V1; attempt++) {
        uint64_t token = 0;
        size_t i;
        SimpleGpuStatusV1 status;
        simple_gpu_lock();
        for (i = 0; i < SIMPLE_GPU_OWNER_CAPACITY_V1; i++) {
            SimpleGpuOwnedSessionV1 *session = &simple_gpu_sessions[i];
            if (session->state && session->state->backend_bit == backend_bit &&
                    (session->quarantined ||
                        ((session->resources || session->completions) &&
                            simple_gpu_session_children_quarantined_locked_v1(
                                session)))) {
                token = session->token;
                break;
            }
        }
        simple_gpu_unlock();
        if (!token) return SIMPLE_GPU_STATUS_OK;
        status = (SimpleGpuStatusV1)rt_gpu_provider_session_close(
            backend_bit, (int64_t)token);
        if (status != SIMPLE_GPU_STATUS_OK) return status;
    }
    return SIMPLE_GPU_STATUS_BUSY;
}

int64_t rt_gpu_provider_session_authority_word(
        int64_t backend_bit, int64_t session_token, int64_t word) {
    SimpleGpuOwnedSessionV1 *session;
    uint64_t value = 0;
    if (session_token <= 0 || word < 0 || word > 6) return 0;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    if (session && !session->quarantined) {
        if (word == 0) value = session->state->provider_identity;
        else if (word == 1) value = session->generation;
        else if (word == 2) value = session->device;
        else {
            int i;
            for (i = 0; i < 8; i++)
                value = (value << 8) |
                    session->state->artifact_digest[(word - 3) * 8 + i];
        }
    }
    simple_gpu_unlock();
    return (int64_t)value;
}

int64_t rt_gpu_provider_resource_authority_word(int64_t backend_bit,
        int64_t session_token, int64_t resource_token, int64_t word) {
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedResourceV1 *resource;
    uint64_t value = 0;
    if (session_token <= 0 || resource_token <= 0 || word < 0 || word > 2) return 0;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(
        session, (uint64_t)resource_token) : NULL;
    if (resource && !resource->quarantined) {
        if (word == 0) value = resource->size_bytes;
        else if (word == 1) value = resource->generation;
        else value = resource->session_token;
    }
    simple_gpu_unlock();
    return (int64_t)value;
}

int64_t rt_gpu_provider_completion_authority_word(int64_t backend_bit,
        int64_t session_token, int64_t completion_token, int64_t word) {
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedCompletionV1 *completion;
    uint64_t value = 0;
    if (session_token <= 0 || completion_token <= 0 || word < 0 || word > 6)
        return 0;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    completion = session ? simple_gpu_completion_locked_v1(
        session, (uint64_t)completion_token) : NULL;
    if (completion && !completion->quarantined && completion->terminal &&
            completion->readback_observed) {
        if (word == 0) value = completion->correlation_id;
        else if (word == 1) value = completion->generation;
        else if (word == 2) value = completion->terminal_resource_token;
        else if (word == 3) value = completion->checksum;
        else if (word == 4) value = completion->readback_length;
        else if (word == 5) value = 1;
        else value = session->device;
    }
    simple_gpu_unlock();
    return (int64_t)value;
}

int64_t rt_gpu_provider_resource_alloc(int64_t backend_bit, int64_t session_token,
        int64_t size_bytes, int64_t flags, int64_t usage_bits) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuResourceDescV1 desc;
    SimpleGpuHandleV1 provider_handle = 0;
    uint64_t provider_session = 0, token = 0, result_token = 0;
    size_t slot;
    SimpleGpuStatusV1 status, cleanup_status = SIMPLE_GPU_STATUS_OK;
    if (session_token <= 0 || size_bytes <= 0 ||
            size_bytes > SIMPLE_GPU_RESOURCE_MAX_BYTES_V1 || flags < 0 ||
            (uint64_t)flags > UINT32_MAX || usage_bits < 0 ||
            !simple_gpu_api_acquire_v1(backend_bit, &pin, &api)) return 0;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    for (slot = 0; session && slot < SIMPLE_GPU_OWNER_CAPACITY_V1; slot++)
        if (simple_gpu_resources[slot].token == 0) break;
    if (session && !session->busy && slot < SIMPLE_GPU_OWNER_CAPACITY_V1 &&
            session->resources != UINT32_MAX && pin.state->retained != UINT64_MAX)
        token = simple_gpu_next_token_locked_v1();
    if (token) {
        simple_gpu_resources[slot].token = UINT64_MAX;
        provider_session = session->provider_handle;
        session->busy = 1;
    }
    simple_gpu_unlock();
    if (!token) { simple_gpu_call_release_v1(&pin); return 0; }
    desc = (SimpleGpuResourceDescV1){sizeof(desc), (uint32_t)flags,
        (uint64_t)size_bytes, (uint64_t)usage_bits};
    status = api->resource_alloc(provider_session, &desc, &provider_handle);
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    if (status == SIMPLE_GPU_STATUS_OK && provider_handle && session) {
        simple_gpu_resources[slot] = (SimpleGpuOwnedResourceV1){token,
            (uint64_t)session_token, provider_handle, (uint64_t)size_bytes,
            pin.generation, 0, 0, pin.state};
        session->resources++; session->busy = 0; pin.state->retained++;
        result_token = token;
    } else {
        simple_gpu_resources[slot].token = UINT64_MAX;
    }
    simple_gpu_unlock();
    if (!result_token && provider_handle)
        cleanup_status = api->resource_release(provider_session, provider_handle);
    if (!result_token) {
        int uncertain = status != SIMPLE_GPU_STATUS_REJECTED || provider_handle != 0;
        if (provider_handle && cleanup_status == SIMPLE_GPU_STATUS_OK) uncertain = 0;
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        if (session && uncertain &&
                session->resources != UINT32_MAX && pin.state->retained != UINT64_MAX) {
            simple_gpu_resources[slot] = (SimpleGpuOwnedResourceV1){token,
                (uint64_t)session_token, provider_handle, (uint64_t)size_bytes,
                pin.generation, 1, 0, pin.state};
            session->resources++; pin.state->retained++;
        } else memset(&simple_gpu_resources[slot], 0,
            sizeof(simple_gpu_resources[slot]));
        if (session) session->busy = 0;
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return (int64_t)result_token;
}

int64_t rt_gpu_provider_resource_release(int64_t backend_bit, int64_t session_token,
        int64_t resource_token) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedResourceV1 *resource;
    uint64_t provider_session, provider_resource;
    SimpleGpuStatusV1 status;
    if (session_token <= 0 || resource_token <= 0 ||
            !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return SIMPLE_GPU_STATUS_UNAVAILABLE;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(session, (uint64_t)resource_token) : NULL;
    if (!resource || session->busy || resource->busy ||
            simple_gpu_resource_has_completion_locked_v1(session, resource)) {
        simple_gpu_unlock(); simple_gpu_call_release_v1(&pin);
        return resource ? SIMPLE_GPU_STATUS_BUSY : SIMPLE_GPU_STATUS_INVALID; }
    resource->busy = 1;
    provider_session = session->provider_handle;
    provider_resource = resource->provider_handle;
    simple_gpu_unlock();
    status = api->resource_release(provider_session, provider_resource);
    if (status == SIMPLE_GPU_STATUS_OK) {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        resource = session ? simple_gpu_resource_locked_v1(session, (uint64_t)resource_token) : NULL;
        if (resource) {
            memset(resource, 0, sizeof(*resource));
            if (session->resources) session->resources--;
            if (pin.state->retained) pin.state->retained--;
        }
        simple_gpu_unlock();
    } else {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        resource = session ? simple_gpu_resource_locked_v1(session, (uint64_t)resource_token) : NULL;
        if (resource) resource->busy = 0;
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return status;
}

int64_t rt_gpu_provider_submit_raw(int64_t backend_bit, int64_t session_token,
        int64_t resource_token, int64_t format, int64_t data, int64_t length,
        int64_t correlation_id) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedResourceV1 *resource;
    SimpleGpuSubmitV1 request;
    SimpleGpuHandleV1 provider_handle = 0;
    uint64_t provider_session = 0, provider_resource = 0;
    uint64_t token = 0, result_token = 0;
    size_t slot;
    SimpleGpuStatusV1 status, cleanup_status = SIMPLE_GPU_STATUS_OK;
    if (session_token <= 0 || resource_token <= 0 ||
            format < 0 || (uint64_t)format > UINT32_MAX ||
            data == 0 || length <= 0 ||
            correlation_id <= 0 || !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return 0;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(
        session, (uint64_t)resource_token) : NULL;
    for (slot = 0; resource && slot < SIMPLE_GPU_OWNER_CAPACITY_V1; slot++)
        if (simple_gpu_completions[slot].token == 0) break;
    if (session && resource && !session->busy && !resource->busy &&
            !resource->quarantined && slot < SIMPLE_GPU_OWNER_CAPACITY_V1 &&
            !simple_gpu_resource_has_completion_locked_v1(session, resource) &&
            session->completions != UINT32_MAX && pin.state->retained != UINT64_MAX)
        token = simple_gpu_next_token_locked_v1();
    if (token) {
        simple_gpu_completions[slot].token = UINT64_MAX;
        provider_session = session->provider_handle;
        provider_resource = resource->provider_handle;
        session->busy = 1;
        resource->busy = 1;
    }
    simple_gpu_unlock();
    if (!token) { simple_gpu_call_release_v1(&pin); return 0; }
    request = (SimpleGpuSubmitV1){sizeof(request), (uint32_t)format,
        (const uint8_t *)(uintptr_t)data, (uint64_t)length,
        (uint64_t)correlation_id, provider_resource};
    status = api->submit(provider_session, &request, &provider_handle);
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(
        session, (uint64_t)resource_token) : NULL;
    if (status == SIMPLE_GPU_STATUS_OK && provider_handle && session && resource) {
        simple_gpu_completions[slot] = (SimpleGpuOwnedCompletionV1){token,
            (uint64_t)session_token, provider_handle, (uint64_t)correlation_id,
            pin.generation, (uint64_t)resource_token, 0, 0, 0, 0, 0, 0,
            pin.state};
        session->completions++; session->busy = 0; resource->busy = 0;
        pin.state->retained++;
        result_token = token;
    } else {
        simple_gpu_completions[slot].token = UINT64_MAX;
    }
    simple_gpu_unlock();
    if (!result_token && provider_handle)
        cleanup_status = api->completion_release(provider_session, provider_handle);
    if (!result_token) {
        int uncertain = (status != SIMPLE_GPU_STATUS_REJECTED) || provider_handle != 0;
        if (provider_handle && cleanup_status == SIMPLE_GPU_STATUS_OK) uncertain = 0;
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        resource = session ? simple_gpu_resource_locked_v1(
            session, (uint64_t)resource_token) : NULL;
        if (session && uncertain && session->completions != UINT32_MAX &&
                pin.state->retained != UINT64_MAX) {
            simple_gpu_completions[slot] = (SimpleGpuOwnedCompletionV1){token,
                (uint64_t)session_token, provider_handle, (uint64_t)correlation_id,
                pin.generation, (uint64_t)resource_token, 0, 0, 0, 0, 1, 0,
                pin.state};
            session->completions++; pin.state->retained++;
            if (resource) resource->quarantined = 1;
        } else memset(&simple_gpu_completions[slot], 0,
            sizeof(simple_gpu_completions[slot]));
        if (session) session->busy = 0;
        if (resource) resource->busy = 0;
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return (int64_t)result_token;
}

int64_t rt_gpu_provider_wait_raw(int64_t backend_bit, int64_t session_token,
        int64_t completion_token, int64_t timeout_ns, int64_t receipt_ptr) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedCompletionV1 *completion;
    SimpleGpuOwnedResourceV1 *resource;
    SimpleGpuReceiptV1 receipt;
    uint64_t provider_session, provider_completion, provider_resource;
    uint64_t correlation, identity, device;
    SimpleGpuStatusV1 status;
    if (session_token <= 0 || completion_token <= 0 || timeout_ns <= 0 ||
            receipt_ptr == 0 || !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return SIMPLE_GPU_STATUS_INVALID;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    completion = session ? simple_gpu_completion_locked_v1(
        session, (uint64_t)completion_token) : NULL;
    resource = completion ? simple_gpu_resource_locked_v1(
        session, completion->terminal_resource_token) : NULL;
    if (!completion || !resource || completion->terminal || completion->busy) {
        simple_gpu_unlock(); simple_gpu_call_release_v1(&pin);
        return SIMPLE_GPU_STATUS_INVALID;
    }
    completion->busy = 1;
    provider_session = session->provider_handle;
    provider_completion = completion->provider_handle;
    provider_resource = resource->provider_handle;
    correlation = completion->correlation_id;
    identity = pin.state->provider_identity;
    device = session->device;
    simple_gpu_unlock();
    memset(&receipt, 0, sizeof(receipt));
    receipt.struct_size = sizeof(receipt);
    status = api->wait(provider_session, provider_completion,
        (uint64_t)timeout_ns, &receipt);
    if (status == SIMPLE_GPU_STATUS_OK) {
        if (receipt.struct_size < sizeof(receipt) ||
                receipt.status != SIMPLE_GPU_STATUS_OK ||
                receipt.correlation_id != correlation ||
                receipt.provider_identity != identity ||
                receipt.device_identity != device || receipt.resource == 0 ||
                receipt.resource != provider_resource ||
                receipt.checksum == 0 ||
                receipt.device_elapsed_ns == 0)
            status = SIMPLE_GPU_STATUS_INCOMPATIBLE;
        else {
            simple_gpu_lock();
            session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
            completion = session ? simple_gpu_completion_locked_v1(
                session, (uint64_t)completion_token) : NULL;
            resource = completion ? simple_gpu_resource_locked_v1(
                session, completion->terminal_resource_token) : NULL;
            if (!completion || completion->terminal || !resource ||
                    resource->provider_handle != receipt.resource)
                status = SIMPLE_GPU_STATUS_INCOMPATIBLE;
            else {
                completion->terminal = 1;
                completion->checksum = receipt.checksum;
                completion->busy = 0;
                receipt.resource = resource->token;
            }
            simple_gpu_unlock();
        }
    }
    if (status != SIMPLE_GPU_STATUS_OK) {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        completion = session ? simple_gpu_completion_locked_v1(
            session, (uint64_t)completion_token) : NULL;
        if (completion) completion->busy = 0;
        simple_gpu_unlock();
    }
    if (status == SIMPLE_GPU_STATUS_OK)
        memcpy((void *)(uintptr_t)receipt_ptr, &receipt, sizeof(receipt));
    simple_gpu_call_release_v1(&pin);
    return status;
}

int64_t rt_gpu_provider_readback_raw(int64_t backend_bit, int64_t session_token,
        int64_t resource_token, int64_t bytes_ptr) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedResourceV1 *resource;
    SimpleGpuOwnedCompletionV1 *completion = NULL;
    SimpleGpuBytesV1 request;
    uint8_t *staging = NULL;
    uint8_t *destination;
    uint64_t provider_session, provider_resource, capacity;
    uint64_t owner_completion_token = 0;
    size_t completion_index;
    SimpleGpuStatusV1 status;
    if (session_token <= 0 || resource_token <= 0 || bytes_ptr == 0 ||
            !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return SIMPLE_GPU_STATUS_INVALID;
    memcpy(&request, (const void *)(uintptr_t)bytes_ptr, sizeof(request));
    if (request.struct_size < sizeof(request) || !request.data || request.length == 0) {
        simple_gpu_call_release_v1(&pin); return SIMPLE_GPU_STATUS_INVALID;
    }
    capacity = request.length;
    destination = request.data;
    if (capacity > SIMPLE_GPU_RESOURCE_MAX_BYTES_V1 ||
            !(staging = (uint8_t *)malloc((size_t)capacity))) {
        simple_gpu_call_release_v1(&pin); return SIMPLE_GPU_STATUS_FAILED;
    }
    request.data = staging;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(session, (uint64_t)resource_token) : NULL;
    for (completion_index = 0; resource && completion_index < SIMPLE_GPU_OWNER_CAPACITY_V1;
            completion_index++) {
        SimpleGpuOwnedCompletionV1 *candidate = &simple_gpu_completions[completion_index];
        if (candidate->state == session->state &&
                candidate->session_token == session->token && candidate->terminal &&
                !candidate->readback_observed && !candidate->busy &&
                candidate->terminal_resource_token == resource->token) {
            completion = candidate; break;
        }
    }
    if (!resource || !completion || resource->busy || capacity > resource->size_bytes) {
        simple_gpu_unlock(); free(staging); simple_gpu_call_release_v1(&pin);
        return SIMPLE_GPU_STATUS_INVALID;
    }
    resource->busy = 1;
    completion->busy = 1;
    owner_completion_token = completion->token;
    provider_session = session->provider_handle;
    provider_resource = resource->provider_handle;
    simple_gpu_unlock();
    status = api->readback(provider_session, provider_resource, &request);
    if (status == SIMPLE_GPU_STATUS_OK && request.length <= capacity &&
            simple_gpu_readback_checksum_v1(staging, request.length) == completion->checksum) {
        memcpy(destination, staging, (size_t)request.length);
        request.data = destination;
        memcpy((void *)(uintptr_t)bytes_ptr, &request, sizeof(request));
    } else if (status == SIMPLE_GPU_STATUS_OK)
        status = SIMPLE_GPU_STATUS_INCOMPATIBLE;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    resource = session ? simple_gpu_resource_locked_v1(session, (uint64_t)resource_token) : NULL;
    if (resource) resource->busy = 0;
    completion = session ? simple_gpu_completion_locked_v1(
        session, owner_completion_token) : NULL;
    if (completion) {
        completion->busy = 0;
        if (status == SIMPLE_GPU_STATUS_OK) {
            completion->readback_observed = 1;
            completion->readback_length = request.length;
        }
    }
    simple_gpu_unlock();
    free(staging);
    simple_gpu_call_release_v1(&pin);
    return status;
}

int64_t rt_gpu_provider_completion_release(int64_t backend_bit,
        int64_t session_token, int64_t completion_token) {
    SimpleGpuCallPinV1 pin;
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuOwnedSessionV1 *session;
    SimpleGpuOwnedCompletionV1 *completion;
    uint64_t provider_session, provider_completion;
    SimpleGpuStatusV1 status;
    if (session_token <= 0 || completion_token <= 0 ||
            !simple_gpu_api_acquire_v1(backend_bit, &pin, &api))
        return SIMPLE_GPU_STATUS_UNAVAILABLE;
    simple_gpu_lock();
    session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
    completion = session ? simple_gpu_completion_locked_v1(
        session, (uint64_t)completion_token) : NULL;
    if (!completion || completion->busy ||
            (completion->terminal && completion->terminal_resource_token != 0 &&
                !completion->readback_observed)) {
        simple_gpu_unlock(); simple_gpu_call_release_v1(&pin);
        return SIMPLE_GPU_STATUS_INVALID; }
    completion->busy = 1;
    provider_session = session->provider_handle;
    provider_completion = completion->provider_handle;
    simple_gpu_unlock();
    status = api->completion_release(provider_session, provider_completion);
    if (status == SIMPLE_GPU_STATUS_OK) {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        completion = session ? simple_gpu_completion_locked_v1(
            session, (uint64_t)completion_token) : NULL;
        if (completion) {
            memset(completion, 0, sizeof(*completion));
            if (session->completions) session->completions--;
            if (pin.state->retained) pin.state->retained--;
        }
        simple_gpu_unlock();
    } else {
        simple_gpu_lock();
        session = simple_gpu_session_locked_v1(backend_bit, (uint64_t)session_token);
        completion = session ? simple_gpu_completion_locked_v1(
            session, (uint64_t)completion_token) : NULL;
        if (completion) completion->busy = 0;
        simple_gpu_unlock();
    }
    simple_gpu_call_release_v1(&pin);
    return status;
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

int64_t rt_gpu_provider_capability_bits(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 &&
            state->authenticated)
        value = (int64_t)state->capability_bits;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_identity(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 &&
            state->authenticated && state->provider_identity <= INT64_MAX)
        value = (int64_t)state->provider_identity;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_generation(int64_t backend_bit) {
    SimpleGpuProviderState *state;
    int64_t value = 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 &&
            state->authenticated && state->generation <= INT64_MAX)
        value = (int64_t)state->generation;
    simple_gpu_unlock();
    return value;
}

int64_t rt_gpu_provider_artifact_digest_word(int64_t backend_bit, int64_t word) {
    SimpleGpuProviderState *state;
    uint64_t value = 0;
    int i;
    if (word < 0 || word >= 4) return 0;
    (void)rt_gpu_provider_loaded(backend_bit);
    simple_gpu_lock();
    state = simple_gpu_state(backend_bit);
    if (state && state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 &&
            state->authenticated) {
        for (i = 0; i < 8; i++)
            value = (value << 8) | state->artifact_digest[word * 8 + i];
    }
    simple_gpu_unlock();
    return (int64_t)value;
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
    const SimpleGpuProviderAbiV1 *api;
    SimpleGpuStatusV1 shutdown_status = SIMPLE_GPU_STATUS_OK;
    int close_ok;
    int snapshot_fd;
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
    /* Retained sessions/resources/completions must remain callable so their
     * owners can drain them. Do not enter retirement until they are gone. */
    if (state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1 && state->retained != 0) {
        simple_gpu_unlock();
        return 0;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_ACTIVE_V1)
        state->phase = SIMPLE_GPU_PROVIDER_RETIRING_V1;
    /* Retirement rejects new calls. A busy result deliberately requires the
     * owner to retry after all synchronous call pins have drained. */
    if (state->phase == SIMPLE_GPU_PROVIDER_RETIRING_V1 &&
            (state->in_flight != 0 || state->retained != 0)) {
        if (state->retained != 0) state->phase = SIMPLE_GPU_PROVIDER_ACTIVE_V1;
        simple_gpu_unlock();
        return 0;
    }
    if (state->phase == SIMPLE_GPU_PROVIDER_FAILED_V1 && !state->handle) {
        snapshot_fd = state->snapshot_fd;
        simple_gpu_clear_state_locked(state);
        simple_gpu_unlock();
        simple_gpu_snapshot_close_v1(snapshot_fd);
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
    api = state->authenticated ? state->api : NULL;
    snapshot_fd = state->snapshot_fd;
    state->phase = SIMPLE_GPU_PROVIDER_CLOSING_V1;
    simple_gpu_unlock();
    if (api) shutdown_status = api->shutdown();
    if (shutdown_status != SIMPLE_GPU_STATUS_OK) {
        simple_gpu_lock();
        if (state->phase == SIMPLE_GPU_PROVIDER_CLOSING_V1 &&
                state->generation == generation && state->handle == handle)
            state->phase = SIMPLE_GPU_PROVIDER_ACTIVE_V1;
        simple_gpu_unlock();
        return 0;
    }
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
    simple_gpu_snapshot_close_v1(snapshot_fd);
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
    SimpleGpuCallPinV1 pin;
    int64_t supported;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_async_session_supported", &pin)) return 0;
    supported = simple_gpu_has_required(pin.state->handle, simple_vulkan_async_v1,
        sizeof(simple_vulkan_async_v1) / sizeof(simple_vulkan_async_v1[0])) &&
        ((QueryFn)pin.symbol)() == 1;
    simple_gpu_call_release_v1(&pin);
    return supported;
}

static int64_t simple_gpu_vulkan_async_call1_v1(
        const char *name, int64_t value, int64_t unavailable) {
    typedef int64_t (*Fn)(int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN, name, &pin))
        return unavailable;
    result = ((Fn)pin.symbol)(value);
    simple_gpu_call_release_v1(&pin);
    return result;
}

static int64_t simple_gpu_vulkan_async_call2_v1(
        const char *name, int64_t first, int64_t second, int64_t unavailable) {
    typedef int64_t (*Fn)(int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN, name, &pin))
        return unavailable;
    result = ((Fn)pin.symbol)(first, second);
    simple_gpu_call_release_v1(&pin);
    return result;
}

static int64_t simple_gpu_vulkan_async_call3_v1(
        const char *name, int64_t first, int64_t second, int64_t third,
        int64_t unavailable) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN, name, &pin))
        return unavailable;
    result = ((Fn)pin.symbol)(first, second, third);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_vulkan_async_session_create_with_wait(int64_t capacity, int64_t timeout_ns) {
    if (!rt_vulkan_async_session_supported()) return 0;
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_create_with_wait", capacity, timeout_ns, 0);
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
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_acquire", session, -1);
}
int64_t rt_vulkan_async_session_command(int64_t session, int64_t token) {
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_command", session, token, -1);
}
int64_t rt_vulkan_async_session_submit(int64_t session, int64_t token) {
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_submit", session, token, -1);
}
int64_t rt_vulkan_async_session_poll(int64_t session, int64_t token) {
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_poll", session, token, -1);
}
int64_t rt_vulkan_async_session_retire(int64_t session, int64_t token) {
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_retire", session, token, -1);
}
int64_t rt_vulkan_async_session_receipt(int64_t session, int64_t sequence) {
    return simple_gpu_vulkan_async_call2_v1(
        "rt_vulkan_async_session_receipt", session, sequence, 0);
}
int64_t rt_vulkan_async_session_cancel(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_cancel", session, -1);
}
int64_t rt_vulkan_async_session_close(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_close", session, 0);
}
int64_t rt_vulkan_async_session_capacity(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_capacity", session, 0);
}
int64_t rt_vulkan_async_session_in_flight(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_in_flight", session, -1);
}
int64_t rt_vulkan_async_session_published_sequence(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_published_sequence", session, -1);
}
int64_t rt_vulkan_async_session_recover(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_recover", session, -1);
}
int64_t rt_vulkan_async_session_abandon_device(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_abandon_device", session, -1);
}
int64_t rt_vulkan_async_session_snapshot(int64_t session) {
    return simple_gpu_vulkan_async_call1_v1(
        "rt_vulkan_async_session_snapshot", session, -1);
}
int64_t rt_vulkan_async_session_snapshot_word(int64_t session, int64_t snapshot, int64_t index) {
    return simple_gpu_vulkan_async_call3_v1(
        "rt_vulkan_async_session_snapshot_word", session, snapshot, index, -1);
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
