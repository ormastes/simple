/* Synthetic provider only. No Vulkan device operation is claimed. */
#define _DARWIN_C_SOURCE 1
#include <stdint.h>
#include <string.h>
#include <dlfcn.h>
int64_t rt_simple_gpu_provider_abi_version(void) { return 1; }
int64_t rt_simple_gpu_provider_backend_bits(void) { return 2; }
/* Admission census only; these out-of-slice fixture methods must not be called. */
#define REQUIRED(name) int64_t name(void) { return 0; }
REQUIRED(rt_vulkan_provider_is_available)
REQUIRED(rt_vulkan_provider_device_count)
REQUIRED(rt_vk_provider_available)
REQUIRED(rt_vulkan_init)
REQUIRED(rt_vulkan_shutdown)
REQUIRED(rt_vulkan_select_device)
REQUIRED(rt_vulkan_alloc_buffer)
REQUIRED(rt_vulkan_free_buffer)
REQUIRED(rt_vulkan_copy_to_buffer_raw)
REQUIRED(rt_vulkan_copy_from_buffer_raw)
REQUIRED(rt_vulkan_copy_from_buffer_strided_raw)
REQUIRED(rt_vulkan_copy_from_buffer_regions_raw)
REQUIRED(rt_vulkan_compile_spirv_raw)
REQUIRED(rt_vulkan_destroy_shader)
REQUIRED(rt_vulkan_destroy_pipeline)
REQUIRED(rt_vulkan_create_descriptor_set)
REQUIRED(rt_vulkan_bind_buffer)
REQUIRED(rt_vulkan_destroy_descriptor_set)
REQUIRED(rt_vulkan_begin_compute)
REQUIRED(rt_vulkan_bind_pipeline)
REQUIRED(rt_vulkan_bind_descriptors)
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
#undef REQUIRED
static int failures, calls, glsl_diagnostic;
static int64_t hit(int ok, int64_t result) { ++calls; if (!ok) ++failures; return ok ? result : 0; }
int64_t phase2_gpu_vulkan_pipeline_failures(void) { return failures; }
int64_t phase2_gpu_vulkan_pipeline_calls(void) { return calls; }
int64_t phase2_gpu_vulkan_pipeline_glsl_diagnostic(void) { return glsl_diagnostic; }
int64_t rt_vulkan_compile_glsl(int64_t ignored) { glsl_diagnostic = ignored == 0; return 999; }
int64_t rt_vulkan_create_compute_pipeline_raw(int64_t shader, int64_t p, int64_t n, int64_t size) {
    return hit(shader == 11 && p && n == 12 && size == 4 &&
        !memcmp((void *)(intptr_t)p, "kernel_entry", 12), 101);
}
int64_t rt_vulkan_push_constants_raw(int64_t cmd, int64_t pipe, int64_t p, int64_t n) {
    static const uint8_t want[] = {0,8,127,255};
    return hit(cmd == 21 && pipe == 22 && p && (n == 0 || n == 2 || n == 4) &&
        !memcmp((void *)(intptr_t)p, want, (size_t)n), 1);
}
int64_t rt_vulkan_present_buffer_regions_raw(int64_t sc, int64_t b, int64_t w,
        int64_t h, int64_t rev, int64_t p, int64_t n) {
    static const uint64_t want[] = {1,2,3,4,255,256,257,258};
    int ok = sc == 31 && b == 32 && w == 640 && h == 480 && rev == 33 && p && n == 64;
    if (ok) for (int i = 0; i < 8; ++i) for (int j = 0; j < 8; ++j)
        if (((uint8_t *)(intptr_t)p)[i*8+j] != (uint8_t)(want[i] >> (j*8))) ok = 0;
    return hit(ok, 3);
}
int64_t rt_vulkan_destroy_swapchain(int64_t s) { return hit(s == 31, 1); }
int64_t rt_vulkan_init_headless_present(int64_t a,int64_t b,int64_t c) { return hit(a==41 && b==42 && c==43, 102); }
int64_t rt_vulkan_init_window_present(int64_t a,int64_t b,int64_t c) { return hit(a==44 && b==45 && c==46, 103); }
int64_t rt_vulkan_init_external_window_present(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e,int64_t f) {
    return hit(a==51 && b==52 && c==53 && d==54 && e==55 && f==56, 104);
}
int64_t rt_vulkan_present_buffer(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e) {
    /* Re-enter core while the lease is live: no lock held and unload is busy. */
    typedef int64_t (*Unload)(int64_t);
    Unload unload = (Unload)dlsym(RTLD_DEFAULT, "rt_gpu_provider_unload");
    return hit(a==61 && b==62 && c==63 && d==64 && e==65 && unload && unload(2)==0, 4);
}
int64_t rt_vulkan_last_present_copy_bytes(int64_t s) { return hit(s==31, 4096); }
int64_t rt_vulkan_last_present_copy_rects(int64_t s) { return hit(s==31, 2); }
