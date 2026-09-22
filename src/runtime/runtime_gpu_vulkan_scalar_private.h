/* Private Vulkan scalar/text dynload forwards. Included by runtime_dynload.c.
 * Provider work always runs under a call pin; no device implementation lives here.
 * C-string results are copied before releasing the pin, so unload cannot dangle
 * a returned pointer. Each function has independent bounded thread-local storage,
 * valid until the next call to that function on the same thread. */
#ifndef SIMPLE_GPU_VULKAN_SCALAR_PRIVATE_H
#define SIMPLE_GPU_VULKAN_SCALAR_PRIVATE_H

GPU_CALL0(int64_t, rt_vulkan_accepted_compute_submit_count, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_accepted_compute_submit_count", 0)
GPU_CALL0(int64_t, rt_vulkan_begin_compute, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_begin_compute", 0)
GPU_CALL3(int64_t, rt_vulkan_bind_buffer, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_bind_buffer", 0, int64_t, int64_t, int64_t)
GPU_CALL2(int64_t, rt_vulkan_bind_descriptors, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_bind_descriptors", 0, int64_t, int64_t)
GPU_CALL2(int64_t, rt_vulkan_bind_pipeline, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_bind_pipeline", 0, int64_t, int64_t)
GPU_CALL1(int64_t, rt_vulkan_create_descriptor_set, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_create_descriptor_set", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_destroy_descriptor_set, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_destroy_descriptor_set", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_destroy_fence, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_destroy_fence", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_destroy_pipeline, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_destroy_pipeline", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_destroy_shader, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_destroy_shader", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_discard_command, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_discard_command", 0, int64_t)
GPU_CALL4(int64_t, rt_vulkan_dispatch, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_dispatch", 0, int64_t, int64_t, int64_t, int64_t)
GPU_CALL1(int64_t, rt_vulkan_end_compute, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_end_compute", 0, int64_t)
GPU_CALL0(int64_t, rt_vulkan_fence_submission_supported, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_fence_submission_supported", 0)
GPU_CALL1(int64_t, rt_vulkan_free_buffer, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_free_buffer", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_select_device, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_select_device", 0, int64_t)
GPU_CALL0(int64_t, rt_vulkan_selected_device_driver_identity_hash, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_selected_device_driver_identity_hash", 0)
GPU_CALL1(int64_t, rt_vulkan_submit_and_wait, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_submit_and_wait", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_submit_and_wait_fence, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_submit_and_wait_fence", 0, int64_t)
GPU_CALL1(int64_t, rt_vulkan_submit_no_wait, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_submit_no_wait", 0, int64_t)
GPU_CALL2(int64_t, rt_vulkan_wait_fence, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_wait_fence", 0, int64_t, int64_t)
GPU_CALL0(int64_t, rt_vulkan_wait_idle, SIMPLE_GPU_BACKEND_VULKAN, "rt_vulkan_wait_idle", 0)

/* Provider cached_cstr storage is invalidated by shutdown. The registry call
 * pin prevents dlclose, but does not serialize concurrent provider operations.
 * A separate blocking mutex covers getter+copy and shutdown; the registry
 * lock is never held here. Other scalar/device work remains concurrent. */
#ifdef _WIN32
static SRWLOCK simple_gpu_scalar_text_mutex = SRWLOCK_INIT;
static int simple_gpu_scalar_text_lock(void) {
    AcquireSRWLockExclusive(&simple_gpu_scalar_text_mutex);
    return 1;
}
static void simple_gpu_scalar_text_unlock(void) {
    ReleaseSRWLockExclusive(&simple_gpu_scalar_text_mutex);
}
#else
#include <pthread.h>
static pthread_mutex_t simple_gpu_scalar_text_mutex = PTHREAD_MUTEX_INITIALIZER;
static int simple_gpu_scalar_text_lock(void) {
    return pthread_mutex_lock(&simple_gpu_scalar_text_mutex) == 0;
}
static void simple_gpu_scalar_text_unlock(void) {
    (void)pthread_mutex_unlock(&simple_gpu_scalar_text_mutex);
}
#endif

int64_t rt_vulkan_shutdown(void) {
    typedef int64_t (*Fn)(void);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_shutdown", &pin)) return 0;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return 0;
    }
    result = ((Fn)pin.symbol)();
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

/* Vulkan device names are bounded by the Vulkan API; driver identities and
 * errors also fit this conservative bound. Reject rather than publish a
 * truncated identity. A missing/null/unterminated error remains descriptive. */
static const char *simple_gpu_scalar_copy_text(const char *source,
        char *destination, size_t capacity, const char *unavailable) {
    size_t length;
    if (!source) return unavailable;
    for (length = 0; length < capacity; length++) {
        if (source[length] == '\0') {
            memcpy(destination, source, length + 1);
            return destination;
        }
    }
    return unavailable;
}

const char *rt_vulkan_device_driver_identity(int64_t device) {
    typedef const char *(*Fn)(int64_t);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_device_driver_identity", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(device),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

const char *rt_vulkan_device_name(int64_t device) {
    typedef const char *(*Fn)(int64_t);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_device_name", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(device),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

const char *rt_vulkan_device_type(int64_t device) {
    typedef const char *(*Fn)(int64_t);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_device_type", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(device),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

const char *rt_vulkan_get_last_error(void) {
    typedef const char *(*Fn)(void);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "Vulkan provider unavailable or invalid error text";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_get_last_error", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

const char *rt_vulkan_selected_device_driver_identity(void) {
    typedef const char *(*Fn)(void);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_selected_device_driver_identity", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

const char *rt_vulkan_selected_device_type(void) {
    typedef const char *(*Fn)(void);
    static SIMPLE_GPU_THREAD_LOCAL char copy[4096];
    const char *unavailable = "";
    SimpleGpuCallPinV1 pin;
    const char *result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_selected_device_type", &pin)) return unavailable;
    if (!simple_gpu_scalar_text_lock()) {
        simple_gpu_call_release_v1(&pin);
        return unavailable;
    }
    result = simple_gpu_scalar_copy_text(((Fn)pin.symbol)(),
        copy, sizeof(copy), unavailable);
    simple_gpu_scalar_text_unlock();
    simple_gpu_call_release_v1(&pin);
    return result;
}

#endif
