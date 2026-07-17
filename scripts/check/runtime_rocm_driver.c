#include "runtime.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct TestString { size_t len; uint8_t data[]; } TestString;
typedef struct TestArray { int64_t len; int64_t data[]; } TestArray;

static void require(int ok, const char *what) {
    if (!ok) { fprintf(stderr, "runtime_rocm_mock: %s failed\n", what); exit(1); }
}
static int64_t string_value(const char *value) {
    return rt_string_new((const uint8_t *)value, strlen(value));
}
static TestArray *array_new(const int64_t *values, int64_t len) {
    TestArray *array = calloc(1, sizeof(*array) + (size_t)len * sizeof(*array->data));
    require(array != NULL, "array allocation");
    array->len = len;
    if (values) memcpy(array->data, values, (size_t)len * sizeof(*values));
    return array;
}

int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    TestString *string = malloc(sizeof(*string) + (size_t)len + 1);
    if (!string) return 0;
    string->len = (size_t)len;
    if (len) memcpy(string->data, bytes, (size_t)len);
    string->data[len] = '\0';
    return (int64_t)(uintptr_t)string;
}
int64_t rt_string_len(int64_t value) {
    TestString *string = (TestString *)(uintptr_t)value;
    return string ? (int64_t)string->len : -1;
}
const uint8_t *rt_string_data(int64_t value) {
    TestString *string = (TestString *)(uintptr_t)value;
    return string ? string->data : NULL;
}
int64_t rt_array_len_safe(int64_t value) {
    TestArray *array = (TestArray *)(uintptr_t)value;
    return array ? array->len : 0;
}
int64_t rt_bytes_u8_at(SplArray *value, int64_t index) {
    TestArray *array = (TestArray *)value;
    return array && index >= 0 && index < array->len ? array->data[index] & 0xff : 0;
}
int8_t rt_bytes_u8_set(SplArray *value, int64_t index, int64_t item) {
    TestArray *array = (TestArray *)value;
    if (!array || index < 0 || index >= array->len) return 0;
    array->data[index] = item & 0xff;
    return 1;
}
int64_t rt_typed_words_u32_at(SplArray *value, int64_t index) {
    TestArray *array = (TestArray *)value;
    return array && index >= 0 && index < array->len ? array->data[index] & 0xffffffffLL : 0;
}
int8_t rt_typed_words_u32_set(SplArray *value, int64_t index, int64_t item) {
    TestArray *array = (TestArray *)value;
    if (!array || index < 0 || index >= array->len) return 0;
    array->data[index] = item & 0xffffffffLL;
    return 1;
}
int64_t rt_typed_words_u64_at(SplArray *value, int64_t index) {
    TestArray *array = (TestArray *)value;
    return array && index >= 0 && index < array->len ? array->data[index] : 0;
}

int main(void) {
    const int64_t input_values[] = {1, 2, 3, 4, 5, 6, 7, 8};
    const int64_t launch_values[] = {17, 29};
    const int64_t pixel_values[] = {0x11223344, 0x55667788};
    TestArray *input = array_new(input_values, 8);
    TestArray *output = array_new(NULL, 8);
    TestArray *launch = array_new(launch_values, 2);
    TestArray *pixels = array_new(pixel_values, 2);
    TestArray *readback = array_new(NULL, 2);

    require(rt_rocm_init(), "init");
    require(rt_rocm_is_available(), "availability");
    require(rt_rocm_device_count() == 1, "device count");
    int64_t name = rt_rocm_device_name(0);
    require(rt_string_len(name) == 12 && memcmp(rt_string_data(name), "Mock AMD GPU", 12) == 0, "device name");
    require(rt_rocm_device_memory(0) == ((int64_t)8 << 30), "device memory");
    int64_t identity = rt_rocm_device_identity(0);
    require(identity > 0 && identity == rt_rocm_device_identity(0), "stable device UUID identity");
    require(rt_rocm_set_device(0) && rt_rocm_get_device() == 0, "device selection");
    require(!rt_rocm_set_device(1), "invalid device rejection");
    int64_t error = rt_rocm_get_last_error();
    require(rt_string_len(error) > 0, "last error");
    require(rt_rocm_set_device(0), "device reselection");

    int64_t device = rt_rocm_malloc(32);
    int64_t device2 = rt_rocm_malloc(32);
    require(device > 0 && device2 > 0, "allocation");
    require(rt_rocm_memcpy_h2d(device, (int64_t)(uintptr_t)input, 8), "host to device");
    require(rt_rocm_memcpy_d2d(device2, device, 8), "device to device");
    require(rt_rocm_memcpy_d2h((int64_t)(uintptr_t)output, device2, 8), "device to host");
    for (int i = 0; i < 8; ++i) require(input->data[i] == output->data[i], "copy contents");
    require(rt_rocm_memset(device, 0xab, 8), "memset");
    require(rt_rocm_memcpy_d2h((int64_t)(uintptr_t)output, device, 8), "memset readback");
    for (int i = 0; i < 8; ++i) require(output->data[i] == 0xab, "memset contents");
    require(!rt_rocm_memcpy_h2d(device, (int64_t)(uintptr_t)input, 9), "oversize copy rejection");

    int64_t legacy_device = rt_rocm_mem_alloc(8);
    require(rt_rocm_device_get(0) == 0 && legacy_device > 0, "legacy device and allocation aliases");
    require(rt_rocm_memcpy_htod(legacy_device, (int64_t)(uintptr_t)input, 8), "legacy host to device alias");
    require(rt_rocm_memcpy_dtoh((int64_t)(uintptr_t)output, legacy_device, 8), "legacy device to host alias");
    require(rt_rocm_mem_free(legacy_device), "legacy free alias");

    int64_t source = string_value("extern \"C\" __global__ void mock_kernel() {}");
    int64_t module = rt_rocm_compile_hsaco(source);
    int64_t function = rt_rocm_get_function(module, string_value("mock_kernel"));
    require(module > 0 && function > 0, "HIPRTC module and function");
    require(rt_rocm_launch_kernel(function, 1, 1, 1, 1, 1, 1, 0, (int64_t)(uintptr_t)launch), "kernel launch args");
    require(rt_rocm_synchronize(), "device synchronize");
    int64_t stream = rt_rocm_create_stream();
    require(stream > 0 && rt_rocm_stream_synchronize(stream) && rt_rocm_destroy_stream(stream), "stream lifecycle");
    require(rt_rocm_unload_module(module), "module unload");
    module = rt_rocm_module_load(source);
    require(module > 0 && rt_rocm_kernel_get(module, string_value("mock_kernel")) > 0, "legacy module aliases");
    require(rt_rocm_unload_module(module), "legacy module unload");

    require(rt_engine2d_rocm_upload_pixels(device, (int64_t)(uintptr_t)pixels, 2) == 0, "Engine2D pixel upload");
    require(rt_engine2d_rocm_download_pixels(device, (int64_t)(uintptr_t)readback, 8) == 0, "Engine2D readback");
    require(readback->data[0] == pixel_values[0] && readback->data[1] == pixel_values[1], "Engine2D pixel contents");
    require(rt_engine2d_rocm_upload_host_buf(device, (int64_t)(uintptr_t)pixels, 8) == 0, "Engine2D host upload");
    require(rt_engine2d_rocm_download_pixels(device, (int64_t)(uintptr_t)readback, 8) == 0, "Engine2D host readback");
    require(rt_engine2d_rocm_download_pixels(device, (int64_t)(uintptr_t)readback, 12) == -3, "Engine2D bounds rejection");

    require(rt_rocm_free(device) && rt_rocm_free(device2), "free");
    require(rt_rocm_shutdown(), "shutdown");
    puts("runtime_rocm_mock=pass");
    return 0;
}
