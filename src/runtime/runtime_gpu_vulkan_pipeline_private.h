/* Private core-C -> Vulkan provider ABI adapters. Included by runtime_dynload.c
 * after its checked array helper. All raw loans end before the call pin drains. */
#ifndef SIMPLE_GPU_VULKAN_PIPELINE_PRIVATE_H
#define SIMPLE_GPU_VULKAN_PIPELINE_PRIVATE_H

int64_t rt_vulkan_compile_glsl(int64_t source) {
    typedef int64_t (*Fn)(int64_t);
    SimpleGpuCallPinV1 pin;
    (void)source;
    /* Canonical GLSL is unsupported and ignores its source argument. Preserve
     * its diagnostic without sending a core value into the Rust value ABI. */
    if (simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_compile_glsl", &pin)) {
        (void)((Fn)pin.symbol)(0);
        simple_gpu_call_release_v1(&pin);
    }
    return 0;
}

int64_t rt_vulkan_create_compute_pipeline_raw(int64_t shader, int64_t entry_ptr,
        int64_t entry_len, int64_t push_size) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (entry_ptr <= 0 || entry_len <= 0 || entry_len > 4096 ||
            push_size < 0 || (uint64_t)push_size > UINT32_MAX ||
            memchr((const void *)(intptr_t)entry_ptr, 0, (size_t)entry_len)) return 0;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_create_compute_pipeline_raw", &pin)) return 0;
    result = ((Fn)pin.symbol)(shader, entry_ptr, entry_len, push_size);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_vulkan_create_compute_pipeline(int64_t shader, int64_t entry,
        int64_t push_size) {
    return rt_vulkan_create_compute_pipeline_raw(shader,
        (int64_t)(intptr_t)rt_string_data(entry), rt_string_len(entry), push_size);
}

GPU_CALL1(int64_t, rt_vulkan_destroy_swapchain, SIMPLE_GPU_BACKEND_VULKAN,
    "rt_vulkan_destroy_swapchain", 0, int64_t)
GPU_CALL3(int64_t, rt_vulkan_init_headless_present, SIMPLE_GPU_BACKEND_VULKAN,
    "rt_vulkan_init_headless_present", 0, int64_t, int64_t, int64_t)
GPU_CALL3(int64_t, rt_vulkan_init_window_present, SIMPLE_GPU_BACKEND_VULKAN,
    "rt_vulkan_init_window_present", 0, int64_t, int64_t, int64_t)
GPU_CALL1(int64_t, rt_vulkan_last_present_copy_bytes, SIMPLE_GPU_BACKEND_VULKAN,
    "rt_vulkan_last_present_copy_bytes", -1, int64_t)
GPU_CALL1(int64_t, rt_vulkan_last_present_copy_rects, SIMPLE_GPU_BACKEND_VULKAN,
    "rt_vulkan_last_present_copy_rects", -1, int64_t)

int64_t rt_vulkan_init_external_window_present(int64_t kind, int64_t display,
        int64_t window, int64_t width, int64_t height, int64_t flags) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_init_external_window_present", &pin)) return 0;
    result = ((Fn)pin.symbol)(kind, display, window, width, height, flags);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_vulkan_present_buffer(int64_t sc, int64_t buffer, int64_t width,
        int64_t height, int64_t revision) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t result;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_present_buffer", &pin)) return 0;
    result = ((Fn)pin.symbol)(sc, buffer, width, height, revision);
    simple_gpu_call_release_v1(&pin);
    return result;
}

int64_t rt_vulkan_present_buffer_regions(int64_t sc, int64_t buffer,
        int64_t width, int64_t height, int64_t revision, int64_t rects) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t len = rt_array_i64_validate(rects), result = 0;
    int64_t *fields;
    uint8_t *bytes;
    if (len <= 0 || len > 4096 || len % 4 || width <= 0 || height <= 0 ||
            (uint64_t)width > UINT32_MAX || (uint64_t)height > UINT32_MAX) return 0;
    /* len <= 4096 proves both products and their sum fit even size_t32. */
    fields = (int64_t *)malloc((size_t)len * 16);
    if (!fields) return 0;
    bytes = (uint8_t *)(fields + len);
    if (rt_array_i64_copy_checked(rects, fields, len) != len) goto done;
    for (int64_t i = 0; i < len; ++i) {
        if (fields[i] < 0 || (uint64_t)fields[i] > UINT32_MAX) goto done;
        for (unsigned j = 0; j < 8; ++j)
            bytes[i * 8 + j] = (uint8_t)((uint64_t)fields[i] >> (j * 8));
    }
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_present_buffer_regions_raw", &pin)) goto done;
    result = ((Fn)pin.symbol)(sc, buffer, width, height, revision,
        (int64_t)(intptr_t)bytes, len * 8);
    simple_gpu_call_release_v1(&pin);
done:
    free(fields);
    return result;
}

static int64_t simple_gpu_pipeline_push(int64_t cmd, int64_t pipe,
        int64_t data, int64_t count, int whole) {
    typedef int64_t (*Fn)(int64_t,int64_t,int64_t,int64_t);
    SimpleGpuCallPinV1 pin;
    uint8_t *bytes = NULL, empty = 0;
    int64_t len = rt_array_bytes_validate(data), copied = 0, result = 0;
    /* Check provider's 64MiB bound before the shared helper allocates. */
    if (len < 0 || len > 64 * 1024 * 1024) return 0;
    if (whole) count = len;
    if (count < 0 || count > len) return 0;
    if (!simple_gpu_array_to_bytes(data, &bytes, &copied)) return 0;
    if (copied != len) goto done;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_push_constants_raw", &pin)) goto done;
    /* A valid empty array still supplies a nonnull call-scoped loan. */
    result = ((Fn)pin.symbol)(cmd, pipe,
        (int64_t)(intptr_t)(bytes ? bytes : &empty), count);
    simple_gpu_call_release_v1(&pin);
done:
    free(bytes);
    return result;
}

int64_t rt_vulkan_push_constants(int64_t cmd, int64_t pipe, int64_t data) {
    return simple_gpu_pipeline_push(cmd, pipe, data, 0, 1);
}

int64_t rt_vulkan_push_constants_array(int64_t cmd, int64_t pipe,
        int64_t data, int64_t count) {
    return simple_gpu_pipeline_push(cmd, pipe, data, count, 0);
}
#endif
