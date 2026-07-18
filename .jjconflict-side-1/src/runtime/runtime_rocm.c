/* Hosted ROCm/HIP provider.  HIP stays optional: no headers or link dependency. */
#include "runtime.h"

#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__linux__)

#include <dlfcn.h>
#include <pthread.h>

typedef int hipError_t;
typedef int hiprtcResult;
typedef void *hipModule_t;
typedef void *hipFunction_t;
typedef void *hipStream_t;
typedef void *hiprtcProgram;

enum {
    HIP_SUCCESS = 0,
    HIP_MEMCPY_HOST_TO_DEVICE = 1,
    HIP_MEMCPY_DEVICE_TO_HOST = 2,
    HIP_MEMCPY_DEVICE_TO_DEVICE = 3
};

typedef struct {
    void *runtime_lib;
    void *rtc_lib;
    int runtime_ready;
    int rtc_ready;
    hipError_t (*init)(unsigned int);
    hipError_t (*get_device_count)(int *);
    hipError_t (*device_get)(int *, int);
    hipError_t (*device_get_name)(char *, int, int);
    hipError_t (*device_total_mem)(size_t *, int);
    hipError_t (*device_get_uuid)(void *, int);
    hipError_t (*set_device)(int);
    hipError_t (*get_device)(int *);
    hipError_t (*malloc_device)(void **, size_t);
    hipError_t (*free_device)(void *);
    hipError_t (*memcpy)(void *, const void *, size_t, int);
    hipError_t (*memset_device)(void *, int, size_t);
    hipError_t (*module_load_data)(hipModule_t *, const void *);
    hipError_t (*module_get_function)(hipFunction_t *, hipModule_t, const char *);
    hipError_t (*module_launch_kernel)(hipFunction_t,
                                       unsigned int, unsigned int, unsigned int,
                                       unsigned int, unsigned int, unsigned int,
                                       unsigned int, hipStream_t, void **, void **);
    hipError_t (*module_unload)(hipModule_t);
    hipError_t (*device_synchronize)(void);
    hipError_t (*stream_create)(hipStream_t *);
    hipError_t (*stream_destroy)(hipStream_t);
    hipError_t (*stream_synchronize)(hipStream_t);
    hipError_t (*get_last_error)(void);
    const char *(*get_error_string)(hipError_t);
    hiprtcResult (*rtc_create_program)(hiprtcProgram *, const char *, const char *,
                                       int, const char *const *, const char *const *);
    hiprtcResult (*rtc_compile_program)(hiprtcProgram, int, const char *const *);
    hiprtcResult (*rtc_get_code_size)(hiprtcProgram, size_t *);
    hiprtcResult (*rtc_get_code)(hiprtcProgram, char *);
    hiprtcResult (*rtc_get_log_size)(hiprtcProgram, size_t *);
    hiprtcResult (*rtc_get_log)(hiprtcProgram, char *);
    hiprtcResult (*rtc_destroy_program)(hiprtcProgram *);
} RocmApi;

static RocmApi rocm;
static pthread_once_t rocm_once = PTHREAD_ONCE_INIT;
static _Thread_local char rocm_error[512] = "ROCm/HIP is unavailable";

static void rocm_set_error(const char *message) {
    snprintf(rocm_error, sizeof(rocm_error), "%s", message ? message : "ROCm/HIP error");
}

static void rocm_set_hip_error(const char *operation, hipError_t error) {
    const char *detail = rocm.get_error_string ? rocm.get_error_string(error) : NULL;
    snprintf(rocm_error, sizeof(rocm_error), "%s failed (%d%s%s)", operation, error,
             detail ? ": " : "", detail ? detail : "");
}

static void *rocm_open_any(const char *const *names) {
    for (size_t i = 0; names[i]; i++) {
        void *lib = dlopen(names[i], RTLD_NOW | RTLD_LOCAL);
        if (lib) return lib;
    }
    return NULL;
}

#define ROCM_LOAD_REQUIRED(lib, member, symbol, okay) do { \
    *(void **)(&rocm.member) = dlsym((lib), (symbol)); \
    if (!rocm.member) (okay) = 0; \
} while (0)

#define ROCM_LOAD_OPTIONAL(lib, member, symbol) \
    (*(void **)(&rocm.member) = dlsym((lib), (symbol)))

static void rocm_load_once(void) {
    static const char *const runtime_names[] = {
        "libamdhip64.so.6", "libamdhip64.so.5", "libamdhip64.so", NULL
    };
    static const char *const rtc_names[] = {
        "libhiprtc.so.6", "libhiprtc.so.5", "libhiprtc.so", NULL
    };
    int runtime_ok = 1;
    int rtc_ok = 1;

    rocm.runtime_lib = rocm_open_any(runtime_names);
    if (!rocm.runtime_lib) {
        rocm_set_error("libamdhip64 was not found");
        return;
    }
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, init, "hipInit", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, get_device_count, "hipGetDeviceCount", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, device_get, "hipDeviceGet", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, device_get_name, "hipDeviceGetName", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, device_total_mem, "hipDeviceTotalMem", runtime_ok);
    ROCM_LOAD_OPTIONAL(rocm.runtime_lib, device_get_uuid, "hipDeviceGetUuid");
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, set_device, "hipSetDevice", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, get_device, "hipGetDevice", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, malloc_device, "hipMalloc", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, free_device, "hipFree", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, memcpy, "hipMemcpy", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, memset_device, "hipMemset", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, module_load_data, "hipModuleLoadData", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, module_get_function, "hipModuleGetFunction", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, module_launch_kernel, "hipModuleLaunchKernel", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, module_unload, "hipModuleUnload", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, device_synchronize, "hipDeviceSynchronize", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, stream_create, "hipStreamCreate", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, stream_destroy, "hipStreamDestroy", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, stream_synchronize, "hipStreamSynchronize", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, get_last_error, "hipGetLastError", runtime_ok);
    ROCM_LOAD_REQUIRED(rocm.runtime_lib, get_error_string, "hipGetErrorString", runtime_ok);
    if (!runtime_ok) {
        rocm_set_error("libamdhip64 is missing required symbols");
        return;
    }
    rocm.runtime_ready = 1;

    rocm.rtc_lib = rocm_open_any(rtc_names);
    if (!rocm.rtc_lib) return;
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_create_program, "hiprtcCreateProgram", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_compile_program, "hiprtcCompileProgram", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_get_code_size, "hiprtcGetCodeSize", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_get_code, "hiprtcGetCode", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_get_log_size, "hiprtcGetProgramLogSize", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_get_log, "hiprtcGetProgramLog", rtc_ok);
    ROCM_LOAD_REQUIRED(rocm.rtc_lib, rtc_destroy_program, "hiprtcDestroyProgram", rtc_ok);
    rocm.rtc_ready = rtc_ok;
}

#undef ROCM_LOAD_REQUIRED
#undef ROCM_LOAD_OPTIONAL

static int rocm_loaded(void) {
    pthread_once(&rocm_once, rocm_load_once);
    return rocm.runtime_ready;
}

static int rocm_hip_ok(const char *operation, hipError_t error) {
    if (error == HIP_SUCCESS) return 1;
    rocm_set_hip_error(operation, error);
    return 0;
}

static int rocm_size(int64_t value, size_t *result) {
    if (value < 0 || (uint64_t)value > SIZE_MAX) {
        rocm_set_error("invalid ROCm byte size");
        return 0;
    }
    *result = (size_t)value;
    return 1;
}

static int rocm_handle(int64_t value, void **result) {
    if (value <= 0) {
        rocm_set_error("invalid ROCm handle");
        return 0;
    }
    *result = (void *)(uintptr_t)value;
    return 1;
}

static int64_t rocm_pointer_handle(void *pointer) {
    intptr_t value = (intptr_t)pointer;
    return value > 0 ? (int64_t)value : 0;
}

static char *rocm_text_copy(int64_t value) {
    int64_t length = rt_string_len(value);
    const uint8_t *data = rt_string_data(value);
    if (length < 0 || (length > 0 && !data) || (uint64_t)length >= SIZE_MAX) {
        rocm_set_error("invalid ROCm text argument");
        return NULL;
    }
    if (length > 0 && memchr(data, '\0', (size_t)length)) {
        rocm_set_error("ROCm text argument contains NUL");
        return NULL;
    }
    char *copy = malloc((size_t)length + 1);
    if (!copy) {
        rocm_set_error("out of memory");
        return NULL;
    }
    if (length > 0) memcpy(copy, data, (size_t)length);
    copy[length] = '\0';
    return copy;
}

static int rocm_array_has(int64_t array, int64_t count) {
    if (count < 0 || rt_array_len_safe(array) < count) {
        rocm_set_error("ROCm array is shorter than requested copy");
        return 0;
    }
    return 1;
}

bool rt_rocm_init(void) {
    return rocm_loaded() && rocm_hip_ok("hipInit", rocm.init(0));
}

bool rt_rocm_shutdown(void) {
    /* HIP libraries and driver state intentionally live for the process lifetime. */
    return true;
}

int64_t rt_rocm_device_count(void) {
    int count = 0;
    if (!rt_rocm_init() || !rocm_hip_ok("hipGetDeviceCount", rocm.get_device_count(&count))) return 0;
    return count > 0 ? count : 0;
}

bool rt_rocm_is_available(void) {
    return rt_rocm_device_count() > 0;
}

int64_t rt_rocm_device_get(int64_t id) {
    int device = 0;
    if (id < 0 || id > INT_MAX || !rt_rocm_init() ||
        !rocm_hip_ok("hipDeviceGet", rocm.device_get(&device, (int)id))) return -1;
    return device;
}

int64_t rt_rocm_device_name(int64_t device) {
    char name[256] = {0};
    if (device < 0 || device > INT_MAX || !rt_rocm_init() ||
        !rocm_hip_ok("hipDeviceGetName", rocm.device_get_name(name, sizeof(name), (int)device))) {
        return rt_string_new(NULL, 0);
    }
    return rt_string_new((const uint8_t *)name, strlen(name));
}

int64_t rt_rocm_device_memory(int64_t device) {
    size_t bytes = 0;
    if (device < 0 || device > INT_MAX || !rt_rocm_init() ||
        !rocm_hip_ok("hipDeviceTotalMem", rocm.device_total_mem(&bytes, (int)device)) ||
        bytes > INT64_MAX) return 0;
    return (int64_t)bytes;
}

int64_t rt_rocm_device_identity(int64_t device) {
    uint8_t uuid[16];
    uint64_t hash = UINT64_C(1469598103934665603);
    if (device < 0 || device > INT_MAX || !rt_rocm_init() || !rocm.device_get_uuid ||
        !rocm_hip_ok("hipDeviceGetUuid", rocm.device_get_uuid(uuid, (int)device))) return 0;
    for (size_t i = 0; i < sizeof(uuid); i++) {
        hash ^= uuid[i];
        hash *= UINT64_C(1099511628211);
    }
    hash &= INT64_MAX;
    return hash ? (int64_t)hash : 1;
}

bool rt_rocm_set_device(int64_t device) {
    return device >= 0 && device <= INT_MAX && rt_rocm_init() &&
           rocm_hip_ok("hipSetDevice", rocm.set_device((int)device));
}

int64_t rt_rocm_get_device(void) {
    int device = 0;
    if (!rt_rocm_init() || !rocm_hip_ok("hipGetDevice", rocm.get_device(&device))) return -1;
    return device;
}

int64_t rt_rocm_malloc(int64_t size) {
    size_t bytes;
    void *pointer = NULL;
    if (size <= 0 || !rocm_size(size, &bytes) || !rt_rocm_init() ||
        !rocm_hip_ok("hipMalloc", rocm.malloc_device(&pointer, bytes))) return 0;
    return rocm_pointer_handle(pointer);
}

bool rt_rocm_free(int64_t ptr) {
    void *pointer;
    return rocm_loaded() && rocm_handle(ptr, &pointer) &&
           rocm_hip_ok("hipFree", rocm.free_device(pointer));
}

bool rt_rocm_memcpy_h2d(int64_t dst, int64_t src_data, int64_t size) {
    size_t bytes;
    void *destination;
    uint8_t *copy;
    if (!rocm_loaded() || !rocm_handle(dst, &destination) || !rocm_size(size, &bytes) ||
        !rocm_array_has(src_data, size)) return false;
    if (bytes == 0) return true;
    copy = malloc(bytes);
    if (!copy) { rocm_set_error("out of memory"); return false; }
    for (int64_t i = 0; i < size; i++)
        copy[i] = (uint8_t)rt_bytes_u8_at((SplArray *)(uintptr_t)src_data, i);
    int ok = rocm_hip_ok("hipMemcpy(H2D)",
                         rocm.memcpy(destination, copy, bytes, HIP_MEMCPY_HOST_TO_DEVICE));
    free(copy);
    return ok;
}

bool rt_rocm_memcpy_d2h(int64_t dst_data, int64_t src, int64_t size) {
    size_t bytes;
    void *source;
    uint8_t *copy;
    if (!rocm_loaded() || !rocm_handle(src, &source) || !rocm_size(size, &bytes) ||
        !rocm_array_has(dst_data, size)) return false;
    if (bytes == 0) return true;
    copy = malloc(bytes);
    if (!copy) { rocm_set_error("out of memory"); return false; }
    int ok = rocm_hip_ok("hipMemcpy(D2H)",
                         rocm.memcpy(copy, source, bytes, HIP_MEMCPY_DEVICE_TO_HOST));
    if (ok) for (int64_t i = 0; i < size; i++)
        rt_bytes_u8_set((SplArray *)(uintptr_t)dst_data, i, copy[i]);
    free(copy);
    return ok;
}

bool rt_rocm_memcpy_d2d(int64_t dst, int64_t src, int64_t size) {
    size_t bytes;
    void *destination;
    void *source;
    return rocm_loaded() && rocm_handle(dst, &destination) && rocm_handle(src, &source) &&
           rocm_size(size, &bytes) &&
           rocm_hip_ok("hipMemcpy(D2D)",
                       rocm.memcpy(destination, source, bytes, HIP_MEMCPY_DEVICE_TO_DEVICE));
}

bool rt_rocm_memset(int64_t ptr, int64_t value, int64_t size) {
    size_t bytes;
    void *pointer;
    return rocm_loaded() && rocm_handle(ptr, &pointer) && rocm_size(size, &bytes) &&
           rocm_hip_ok("hipMemset", rocm.memset_device(pointer, (int)value, bytes));
}

int64_t rt_rocm_compile_hsaco(int64_t source) {
    char *program_source = NULL;
    char *code = NULL;
    hiprtcProgram program = NULL;
    hipModule_t module = NULL;
    size_t code_size = 0;
    int64_t result = 0;

    if (!rocm_loaded() || !rocm.rtc_ready) {
        rocm_set_error("libhiprtc is unavailable or incomplete");
        return 0;
    }
    program_source = rocm_text_copy(source);
    if (!program_source) return 0;
    if (rocm.rtc_create_program(&program, program_source, "simple_rocm_kernel.cu",
                                0, NULL, NULL) != 0) {
        rocm_set_error("hiprtcCreateProgram failed");
        goto done;
    }
    if (rocm.rtc_compile_program(program, 0, NULL) != 0) {
        size_t log_size = 0;
        if (rocm.rtc_get_log_size(program, &log_size) == 0 && log_size > 0) {
            char *log = malloc(log_size);
            if (log && rocm.rtc_get_log(program, log) == 0) rocm_set_error(log);
            else rocm_set_error("hiprtcCompileProgram failed");
            free(log);
        } else {
            rocm_set_error("hiprtcCompileProgram failed");
        }
        goto done;
    }
    if (rocm.rtc_get_code_size(program, &code_size) != 0 || code_size == 0) {
        rocm_set_error("hiprtcGetCodeSize failed");
        goto done;
    }
    code = malloc(code_size);
    if (!code) { rocm_set_error("out of memory"); goto done; }
    if (rocm.rtc_get_code(program, code) != 0) {
        rocm_set_error("hiprtcGetCode failed");
        goto done;
    }
    if (!rocm_hip_ok("hipModuleLoadData", rocm.module_load_data(&module, code))) goto done;
    result = rocm_pointer_handle(module);

done:
    if (program) rocm.rtc_destroy_program(&program);
    free(code);
    free(program_source);
    return result;
}

int64_t rt_rocm_get_function(int64_t module, int64_t name) {
    void *module_pointer;
    char *kernel_name;
    hipFunction_t function = NULL;
    int64_t result = 0;
    if (!rocm_loaded() || !rocm_handle(module, &module_pointer)) return 0;
    kernel_name = rocm_text_copy(name);
    if (!kernel_name) return 0;
    if (rocm_hip_ok("hipModuleGetFunction",
                    rocm.module_get_function(&function, module_pointer, kernel_name)))
        result = rocm_pointer_handle(function);
    free(kernel_name);
    return result;
}

bool rt_rocm_launch_kernel(int64_t function, int64_t grid_x, int64_t grid_y,
                           int64_t grid_z, int64_t block_x, int64_t block_y,
                           int64_t block_z, int64_t shared_mem, int64_t args) {
    void *function_pointer;
    int64_t count;
    int64_t *values = NULL;
    void **parameters = NULL;
    int ok = 0;
    if (!rocm_loaded() || !rocm_handle(function, &function_pointer) ||
        grid_x <= 0 || grid_x > UINT_MAX || grid_y <= 0 || grid_y > UINT_MAX ||
        grid_z <= 0 || grid_z > UINT_MAX || block_x <= 0 || block_x > UINT_MAX ||
        block_y <= 0 || block_y > UINT_MAX || block_z <= 0 || block_z > UINT_MAX ||
        shared_mem < 0 || shared_mem > UINT_MAX) {
        rocm_set_error("invalid ROCm kernel launch dimensions");
        return false;
    }
    count = rt_array_len_safe(args);
    if (count < 0 || (uint64_t)count > SIZE_MAX / sizeof(*values) ||
        (uint64_t)count > SIZE_MAX / sizeof(*parameters)) {
        rocm_set_error("invalid ROCm kernel argument array");
        return false;
    }
    if (count > 0) {
        values = malloc((size_t)count * sizeof(*values));
        parameters = malloc((size_t)count * sizeof(*parameters));
        if (!values || !parameters) { rocm_set_error("out of memory"); goto done; }
        for (int64_t i = 0; i < count; i++) {
            values[i] = rt_typed_words_u64_at((SplArray *)(uintptr_t)args, i);
            parameters[i] = &values[i];
        }
    }
    ok = rocm_hip_ok("hipModuleLaunchKernel",
        rocm.module_launch_kernel(function_pointer,
            (unsigned int)grid_x, (unsigned int)grid_y, (unsigned int)grid_z,
            (unsigned int)block_x, (unsigned int)block_y, (unsigned int)block_z,
            (unsigned int)shared_mem, NULL, parameters, NULL));
done:
    free(parameters);
    free(values);
    return ok;
}

bool rt_rocm_unload_module(int64_t module) {
    void *pointer;
    return rocm_loaded() && rocm_handle(module, &pointer) &&
           rocm_hip_ok("hipModuleUnload", rocm.module_unload(pointer));
}

bool rt_rocm_synchronize(void) {
    return rocm_loaded() && rocm_hip_ok("hipDeviceSynchronize", rocm.device_synchronize());
}

int64_t rt_rocm_create_stream(void) {
    hipStream_t stream = NULL;
    if (!rocm_loaded() || !rocm_hip_ok("hipStreamCreate", rocm.stream_create(&stream))) return 0;
    return rocm_pointer_handle(stream);
}

bool rt_rocm_destroy_stream(int64_t stream) {
    void *pointer;
    return rocm_loaded() && rocm_handle(stream, &pointer) &&
           rocm_hip_ok("hipStreamDestroy", rocm.stream_destroy(pointer));
}

bool rt_rocm_stream_synchronize(int64_t stream) {
    void *pointer;
    return rocm_loaded() && rocm_handle(stream, &pointer) &&
           rocm_hip_ok("hipStreamSynchronize", rocm.stream_synchronize(pointer));
}

int64_t rt_rocm_get_last_error(void) {
    if (rocm_loaded()) {
        hipError_t error = rocm.get_last_error();
        if (error != HIP_SUCCESS) rocm_set_hip_error("HIP", error);
    }
    return rt_string_new((const uint8_t *)rocm_error, strlen(rocm_error));
}

static int64_t rocm_engine2d_copy_to_device(int64_t dst, int64_t pixels, int64_t count) {
    void *destination;
    uint32_t *copy;
    size_t bytes;
    if (!rocm_loaded() || !rocm_handle(dst, &destination) || count < 0 ||
        !rocm_array_has(pixels, count) || (uint64_t)count > SIZE_MAX / sizeof(*copy)) return -3;
    bytes = (size_t)count * sizeof(*copy);
    if (bytes == 0) return 0;
    copy = malloc(bytes);
    if (!copy) { rocm_set_error("out of memory"); return -3; }
    for (int64_t i = 0; i < count; i++)
        copy[i] = (uint32_t)rt_typed_words_u32_at((SplArray *)(uintptr_t)pixels, i);
    int ok = rocm_hip_ok("hipMemcpy(Engine2D H2D)",
                         rocm.memcpy(destination, copy, bytes, HIP_MEMCPY_HOST_TO_DEVICE));
    free(copy);
    return ok ? 0 : -3;
}

int64_t rt_engine2d_rocm_upload_pixels(int64_t dst, int64_t pixels, int64_t count) {
    return rocm_engine2d_copy_to_device(dst, pixels, count);
}

int64_t rt_engine2d_rocm_upload_host_buf(int64_t dst, int64_t host_buf, int64_t byte_size) {
    if (byte_size < 0 || byte_size % (int64_t)sizeof(uint32_t) != 0) return -3;
    return rocm_engine2d_copy_to_device(dst, host_buf, byte_size / (int64_t)sizeof(uint32_t));
}

int64_t rt_engine2d_rocm_download_pixels(int64_t src, int64_t pixels, int64_t byte_size) {
    void *source;
    uint32_t *copy;
    int64_t count;
    size_t bytes;
    if (!rocm_loaded() || !rocm_handle(src, &source) || byte_size < 0 ||
        byte_size % (int64_t)sizeof(uint32_t) != 0 ||
        !rocm_size(byte_size, &bytes)) return -3;
    count = byte_size / (int64_t)sizeof(uint32_t);
    if (!rocm_array_has(pixels, count)) return -3;
    if (bytes == 0) return 0;
    copy = malloc(bytes);
    if (!copy) { rocm_set_error("out of memory"); return -3; }
    int ok = rocm_hip_ok("hipMemcpy(Engine2D D2H)",
                         rocm.memcpy(copy, source, bytes, HIP_MEMCPY_DEVICE_TO_HOST));
    if (ok) for (int64_t i = 0; i < count; i++)
        rt_typed_words_u32_set((SplArray *)(uintptr_t)pixels, i, copy[i]);
    free(copy);
    return ok ? 0 : -3;
}

/* Compatibility names used by the older Engine2D SFFI surface. */
int64_t rt_rocm_mem_alloc(int64_t size) { return rt_rocm_malloc(size); }
bool rt_rocm_mem_free(int64_t ptr) { return rt_rocm_free(ptr); }
bool rt_rocm_memcpy_htod(int64_t dst, int64_t src, int64_t size) {
    return rt_rocm_memcpy_h2d(dst, src, size);
}
bool rt_rocm_memcpy_dtoh(int64_t dst, int64_t src, int64_t size) {
    return rt_rocm_memcpy_d2h(dst, src, size);
}
int64_t rt_rocm_module_load(int64_t source) { return rt_rocm_compile_hsaco(source); }
int64_t rt_rocm_kernel_get(int64_t module, int64_t name) {
    return rt_rocm_get_function(module, name);
}

#else

/* Hosted ROCm is supported only on Linux; every other target fails closed. */
bool rt_rocm_init(void) { return false; }
bool rt_rocm_shutdown(void) { return true; }
bool rt_rocm_is_available(void) { return false; }
int64_t rt_rocm_device_count(void) { return 0; }
int64_t rt_rocm_device_get(int64_t id) { (void)id; return -1; }
int64_t rt_rocm_device_name(int64_t device) { (void)device; return rt_string_new(NULL, 0); }
int64_t rt_rocm_device_memory(int64_t device) { (void)device; return 0; }
int64_t rt_rocm_device_identity(int64_t device) { (void)device; return 0; }
bool rt_rocm_set_device(int64_t device) { (void)device; return false; }
int64_t rt_rocm_get_device(void) { return -1; }
int64_t rt_rocm_malloc(int64_t size) { (void)size; return 0; }
bool rt_rocm_free(int64_t ptr) { (void)ptr; return false; }
bool rt_rocm_memcpy_h2d(int64_t dst, int64_t src, int64_t size) { (void)dst; (void)src; (void)size; return false; }
bool rt_rocm_memcpy_d2h(int64_t dst, int64_t src, int64_t size) { (void)dst; (void)src; (void)size; return false; }
bool rt_rocm_memcpy_d2d(int64_t dst, int64_t src, int64_t size) { (void)dst; (void)src; (void)size; return false; }
bool rt_rocm_memset(int64_t ptr, int64_t value, int64_t size) { (void)ptr; (void)value; (void)size; return false; }
int64_t rt_rocm_compile_hsaco(int64_t source) { (void)source; return 0; }
int64_t rt_rocm_get_function(int64_t module, int64_t name) { (void)module; (void)name; return 0; }
bool rt_rocm_launch_kernel(int64_t function, int64_t gx, int64_t gy, int64_t gz, int64_t bx, int64_t by, int64_t bz, int64_t shared, int64_t args) { (void)function; (void)gx; (void)gy; (void)gz; (void)bx; (void)by; (void)bz; (void)shared; (void)args; return false; }
bool rt_rocm_unload_module(int64_t module) { (void)module; return false; }
bool rt_rocm_synchronize(void) { return false; }
int64_t rt_rocm_create_stream(void) { return 0; }
bool rt_rocm_destroy_stream(int64_t stream) { (void)stream; return false; }
bool rt_rocm_stream_synchronize(int64_t stream) { (void)stream; return false; }
int64_t rt_rocm_get_last_error(void) { static const uint8_t message[] = "ROCm/HIP is unavailable"; return rt_string_new(message, sizeof(message) - 1); }
int64_t rt_engine2d_rocm_upload_pixels(int64_t dst, int64_t pixels, int64_t count) { (void)dst; (void)pixels; (void)count; return -3; }
int64_t rt_engine2d_rocm_download_pixels(int64_t src, int64_t pixels, int64_t bytes) { (void)src; (void)pixels; (void)bytes; return -3; }
int64_t rt_engine2d_rocm_upload_host_buf(int64_t dst, int64_t pixels, int64_t bytes) { (void)dst; (void)pixels; (void)bytes; return -3; }
int64_t rt_rocm_mem_alloc(int64_t size) { return rt_rocm_malloc(size); }
bool rt_rocm_mem_free(int64_t ptr) { return rt_rocm_free(ptr); }
bool rt_rocm_memcpy_htod(int64_t dst, int64_t src, int64_t size) { return rt_rocm_memcpy_h2d(dst, src, size); }
bool rt_rocm_memcpy_dtoh(int64_t dst, int64_t src, int64_t size) { return rt_rocm_memcpy_d2h(dst, src, size); }
int64_t rt_rocm_module_load(int64_t source) { return rt_rocm_compile_hsaco(source); }
int64_t rt_rocm_kernel_get(int64_t module, int64_t name) { return rt_rocm_get_function(module, name); }

#endif
