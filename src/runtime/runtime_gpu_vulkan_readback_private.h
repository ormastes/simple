/* Core-C Vulkan array adapters. Included by runtime_dynload.c after its pin
 * helpers. Provider calls receive only owned raw bytes, never native values. */
#ifndef SIMPLE_GPU_VULKAN_READBACK_PRIVATE_H
#define SIMPLE_GPU_VULKAN_READBACK_PRIVATE_H

#define SIMPLE_GPU_READBACK_MAX_BYTES INT64_C(2147483648)
#define SIMPLE_GPU_READBACK_MAX_ROWS INT64_C(16384)
#define SIMPLE_GPU_READBACK_MAX_REGIONS INT64_C(256)

static int simple_gpu_readback_range(int64_t count, int64_t offset) {
    return count >= 0 && count <= SIMPLE_GPU_READBACK_MAX_BYTES &&
        offset >= 0 && offset <= INT64_MAX - count;
}

static int simple_gpu_readback_shape(int64_t offset, int64_t row_bytes,
        int64_t rows, int64_t stride, int64_t *packed) {
    if (offset < 0 || row_bytes < 0 || rows < 0 || stride < 0 ||
            rows > SIMPLE_GPU_READBACK_MAX_ROWS ||
            (rows > 0 && row_bytes > 0 && stride < row_bytes)) return 0;
    if (rows && row_bytes > SIMPLE_GPU_READBACK_MAX_BYTES / rows) return 0;
    *packed = rows * row_bytes;
    if (rows == 0 || row_bytes == 0) return 1;
    if (offset > INT64_MAX - row_bytes) return 0;
    return rows == 1 || stride <= (INT64_MAX - offset - row_bytes) / (rows - 1);
}

static void simple_gpu_readback_le(uint8_t *out, uint64_t word, int width) {
    for (int i = 0; i < width; ++i) out[i] = (uint8_t)(word >> (i * 8));
}

static uint32_t simple_gpu_readback_u32(const uint8_t *bytes) {
    return (uint32_t)bytes[0] | ((uint32_t)bytes[1] << 8) |
        ((uint32_t)bytes[2] << 16) | ((uint32_t)bytes[3] << 24);
}

/* Allocate one byte even for an empty transfer: the canonical contiguous
 * provider requires a non-null pointer independently of its byte count. */
static uint8_t *simple_gpu_readback_download(int64_t handle,
        int64_t count, int64_t offset) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    if (handle <= 0 || !simple_gpu_readback_range(count, offset)) return NULL;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_copy_from_buffer_raw", &pin)) return NULL;
    uint8_t *bytes = (uint8_t *)malloc(count ? (size_t)count : 1);
    int64_t status = bytes ? ((Fn)pin.symbol)(
        (int64_t)(intptr_t)bytes, count, handle, offset) : 0;
    simple_gpu_call_release_v1(&pin);
    if (!status) { free(bytes); return NULL; }
    return bytes;
}

int64_t rt_vulkan_copy_from_buffer_array(int64_t destination, int64_t count,
        int64_t handle, int64_t offset) {
    if (!simple_gpu_readback_range(count, offset) ||
            rt_array_bytes_validate(destination) < count) return 0;
    uint8_t *bytes = simple_gpu_readback_download(handle, count, offset);
    if (!bytes) return 0;
    int64_t ok = rt_array_bytes_store_checked(destination, bytes, count) == count;
    free(bytes);
    return ok;
}

int64_t rt_vulkan_copy_from_buffer_strided(int64_t destination, int64_t handle,
        int64_t offset, int64_t row_bytes, int64_t rows, int64_t stride) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t, int64_t,
        int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t count;
    if (handle <= 0 || !simple_gpu_readback_shape(offset, row_bytes, rows, stride, &count) ||
            rt_array_bytes_validate(destination) != count) return 0;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_copy_from_buffer_strided_raw", &pin)) return 0;
    uint8_t *bytes = (uint8_t *)malloc(count ? (size_t)count : 1);
    int64_t status = bytes ? ((Fn)pin.symbol)((int64_t)(intptr_t)bytes,
        count, handle, offset, row_bytes, rows, stride) : 0;
    simple_gpu_call_release_v1(&pin);
    if (status) status = rt_array_bytes_store_checked(destination, bytes, count) == count;
    free(bytes);
    return status;
}

int64_t rt_vulkan_copy_from_buffer_regions(int64_t destination,
        int64_t handle, int64_t regions) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t words = rt_array_i64_validate(regions);
    int64_t count = rt_array_bytes_validate(destination);
    if (handle <= 0 || count <= 0 || count > SIMPLE_GPU_READBACK_MAX_BYTES ||
            words <= 0 || words % 4 || words > SIMPLE_GPU_READBACK_MAX_REGIONS * 4) return 0;
    int64_t fields[SIMPLE_GPU_READBACK_MAX_REGIONS * 4];
    uint8_t records[SIMPLE_GPU_READBACK_MAX_REGIONS * 32];
    if (rt_array_i64_copy_checked(regions, fields, words) != words) return 0;
    int64_t total = 0, total_rows = 0;
    for (int64_t i = 0; i < words; i += 4) {
        int64_t packed;
        if (!simple_gpu_readback_shape(fields[i], fields[i + 1],
                fields[i + 2], fields[i + 3], &packed) ||
                packed > count - total ||
                fields[i + 2] > SIMPLE_GPU_READBACK_MAX_ROWS - total_rows) return 0;
        total += packed;
        total_rows += fields[i + 2];
        for (int j = 0; j < 4; ++j)
            simple_gpu_readback_le(records + (i + j) * 8, (uint64_t)fields[i + j], 8);
    }
    if (total != count) return 0;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_copy_from_buffer_regions_raw", &pin)) return 0;
    uint8_t *bytes = (uint8_t *)malloc((size_t)count);
    int64_t status = bytes ? ((Fn)pin.symbol)((int64_t)(intptr_t)bytes, count,
        handle, (int64_t)(intptr_t)records, words * 8) : 0;
    simple_gpu_call_release_v1(&pin);
    if (status) status = rt_array_bytes_store_checked(destination, bytes, count) == count;
    free(bytes);
    return status;
}

int64_t rt_vulkan_copy_to_buffer_u32(int64_t handle, int64_t words, int64_t offset) {
    typedef int64_t (*Fn)(int64_t, int64_t, int64_t, int64_t);
    SimpleGpuCallPinV1 pin;
    int64_t count = rt_array_i64_validate(words);
    if (handle <= 0 || count < 0 || count > SIMPLE_GPU_READBACK_MAX_BYTES / 4 ||
            !simple_gpu_readback_range(count * 4, offset)) return 0;
    if (!simple_gpu_call_acquire_v1(SIMPLE_GPU_BACKEND_VULKAN,
            "rt_vulkan_copy_to_buffer_raw", &pin)) return 0;
    uint8_t *bytes = (uint8_t *)malloc(count ? (size_t)count * 4 : 1);
    if (!bytes) { simple_gpu_call_release_v1(&pin); return 0; }
    for (int64_t i = 0; i < count; ++i) {
        int64_t value = rt_value_as_int(rt_array_get((SplArray *)(intptr_t)words, i));
        if (value < INT32_MIN || value > UINT32_MAX) {
            free(bytes); simple_gpu_call_release_v1(&pin); return 0;
        }
        simple_gpu_readback_le(bytes + i * 4, (uint32_t)value, 4);
    }
    int64_t result = ((Fn)pin.symbol)(handle, (int64_t)(intptr_t)bytes, count * 4, offset);
    simple_gpu_call_release_v1(&pin);
    free(bytes);
    return result;
}

int64_t rt_vulkan_read_buffer_bytes(int64_t handle, int64_t count, int64_t offset) {
    uint8_t *bytes = simple_gpu_readback_download(handle, count, offset);
    if (!bytes) return (int64_t)(intptr_t)rt_byte_array_new(0);
    SplArray *out = rt_byte_array_new_len((uint64_t)count);
    int64_t result = (int64_t)(intptr_t)out;
    if (rt_array_bytes_store_checked(result, bytes, count) != count) {
        rt_array_free(out);
        result = (int64_t)(intptr_t)rt_byte_array_new(0);
    }
    free(bytes);
    return result;
}

int64_t rt_vulkan_readback_u32_array(int64_t handle, int64_t count, int64_t offset) {
    if (count <= 0 || count > SIMPLE_GPU_READBACK_MAX_BYTES / 4)
        return (int64_t)(intptr_t)rt_array_new(0);
    uint8_t *bytes = simple_gpu_readback_download(handle, count * 4, offset);
    if (!bytes) return (int64_t)(intptr_t)rt_array_new(0);
    SplArray *out = rt_array_new(count);
    for (int64_t i = 0; i < count; ++i) {
        if (!rt_array_push(out, rt_value_int(simple_gpu_readback_u32(bytes + i * 4)))) {
            rt_array_free(out); out = rt_array_new(0); break;
        }
    }
    free(bytes);
    return (int64_t)(intptr_t)out;
}

int64_t rt_vulkan_readback_u32_array_checksum(int64_t handle, int64_t count, int64_t offset) {
    if (count <= 0 || count > SIMPLE_GPU_READBACK_MAX_BYTES / 4) return -1;
    uint8_t *bytes = simple_gpu_readback_download(handle, count * 4, offset);
    if (!bytes) return -1;
    /* At most 2^29 words of at most 2^32-1: the sum fits in uint64_t. */
    uint64_t sum = 0;
    for (int64_t i = 0; i < count; ++i)
        sum += simple_gpu_readback_u32(bytes + i * 4);
    free(bytes);
    return (int64_t)(sum % UINT64_C(2147483647));
}

int64_t rt_vulkan_readback_u32_checksum(int64_t destination, int64_t count,
        int64_t handle, int64_t offset) {
    if (count <= 0 || count > SIMPLE_GPU_READBACK_MAX_BYTES / 4 ||
            rt_array_i64_validate(destination) < count) return -1;
    uint8_t *bytes = simple_gpu_readback_download(handle, count * 4, offset);
    if (!bytes) return -1;
    uint64_t sum = 0;
    /* The registered ordinary-integer destination was checked before the
     * provider call. Only this owner can change it; in-range slot stores do
     * not allocate. No writes occur on provider failure; the tail is retained. */
    for (int64_t i = 0; i < count; ++i) {
        uint32_t word = simple_gpu_readback_u32(bytes + i * 4);
        rt_array_set((SplArray *)(intptr_t)destination, i, rt_value_int(word));
        sum += word;
    }
    free(bytes);
    return (int64_t)(sum % UINT64_C(2147483647));
}
#endif
