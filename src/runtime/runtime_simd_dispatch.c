/*
 * SIMD Dispatch — compilation unit for dispatch table support.
 * The text dispatch table (g_simd_text) and init are in runtime_simd_utf8.c.
 * The crypto dispatch table (g_simd_crypto) is defined here with scalar stubs.
 */
#include "runtime_simd_dispatch.h"
#include "runtime.h"
#include "runtime_value.h"

#include <stdatomic.h>
#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
#  include <windows.h>
#  if defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86))
#    include <intrin.h>
#  endif
#else
#  include <pthread.h>
#endif

#if defined(__linux__) && defined(__riscv)
#  include <sys/auxv.h>
#endif

#if !defined(_WIN32)
#  include <dlfcn.h>
#endif

#if !defined(SIMPLE_RUNTIME_OPENCL_ONLY)

#if defined(__x86_64__) || defined(_M_X64)
#  include <immintrin.h>
#endif

/* GCC/Clang can isolate AVX2 instructions in runtime-dispatched functions.
 * MSVC has no GNU target attribute; its x64 build keeps the same CPUID guard
 * and emits these intrinsic bodies according to the translation-unit flags. */
#if (defined(__GNUC__) || defined(__clang__)) && !defined(_MSC_VER)
#  define SIMPLE_RUNTIME_TARGET_AVX2 __attribute__((target("avx2")))
#else
#  define SIMPLE_RUNTIME_TARGET_AVX2
#endif

#if defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86))
static bool rt_msvc_x86_os_avx_enabled(void) {
    int regs[4];
    __cpuid(regs, 1);
    if ((regs[2] & (1 << 27)) == 0 || (regs[2] & (1 << 28)) == 0) return false;
    return (_xgetbv(0) & 0x6) == 0x6;
}
#endif

bool rt_simd_has_sse(void) {
#if (defined(__x86_64__) || defined(__i386__)) && (defined(__GNUC__) || defined(__clang__))
    __builtin_cpu_init();
    return __builtin_cpu_supports("sse") != 0;
#elif defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86))
    int regs[4];
    __cpuid(regs, 1);
    return (regs[3] & (1 << 25)) != 0;
#else
    return false;
#endif
}

bool rt_simd_has_avx(void) {
#if (defined(__x86_64__) || defined(__i386__)) && (defined(__GNUC__) || defined(__clang__))
    __builtin_cpu_init();
    return __builtin_cpu_supports("avx") != 0;
#elif defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86))
    return rt_msvc_x86_os_avx_enabled();
#else
    return false;
#endif
}

bool rt_simd_has_avx2(void) {
#if (defined(__x86_64__) || defined(__i386__)) && (defined(__GNUC__) || defined(__clang__))
    __builtin_cpu_init();
    return __builtin_cpu_supports("avx2") != 0;
#elif defined(_MSC_VER) && (defined(_M_X64) || defined(_M_IX86))
    int regs[4];
    if (!rt_msvc_x86_os_avx_enabled()) return false;
    __cpuidex(regs, 7, 0);
    return (regs[1] & (1 << 5)) != 0;
#else
    return false;
#endif
}

bool rt_simd_has_neon(void) {
#if defined(__aarch64__) || defined(_M_ARM64) || defined(__ARM_NEON)
    return true;
#else
    return false;
#endif
}

bool rt_simd_has_rvv(void) {
#if defined(__linux__) && defined(__riscv)
    return (getauxval(16) & (1UL << ('V' - 'A'))) != 0;
#else
    return false;
#endif
}

#endif

typedef intptr_t rt_opencl_context_property;
typedef uint64_t rt_opencl_device_type;

#define RT_OPENCL_SUCCESS 0
#define RT_OPENCL_DEVICE_TYPE_GPU (1ULL << 2)
#define RT_OPENCL_DEVICE_TYPE_ACCELERATOR (1ULL << 3)
#define RT_OPENCL_CONTEXT_PLATFORM 0x1084
#define RT_OPENCL_CONTEXT_MAGIC 0x534f4343U
#define RT_OPENCL_QUEUE_MAGIC 0x534f4349U
#define RT_OPENCL_PROGRAM_MAGIC 0x534f4350U
#define RT_OPENCL_KERNEL_MAGIC 0x534f434bU
#define RT_OPENCL_BUFFER_MAGIC 0x534f4342U
#define RT_OPENCL_TRUE 1
#define RT_OPENCL_MEM_READ_WRITE (1ULL << 0)

typedef int (*rt_opencl_get_platform_ids_fn)(uint32_t, void*, uint32_t*);
typedef int (*rt_opencl_get_device_ids_fn)(void*, rt_opencl_device_type, uint32_t, void**, uint32_t*);
typedef void* (*rt_opencl_create_context_fn)(const rt_opencl_context_property*, uint32_t, void* const*, void*, void*, int*);
typedef void* (*rt_opencl_create_command_queue_fn)(void*, void*, uint64_t, int*);
typedef void* (*rt_opencl_create_command_queue_with_properties_fn)(void*, void*, const rt_opencl_context_property*, int*);
typedef void* (*rt_opencl_create_program_with_source_fn)(void*, uint32_t, const char**, const size_t*, int*);
typedef int (*rt_opencl_build_program_fn)(void*, uint32_t, void* const*, const char*, void*, void*);
typedef void* (*rt_opencl_create_kernel_fn)(void*, const char*, int*);
typedef int (*rt_opencl_set_kernel_arg_fn)(void*, uint32_t, size_t, const void*);
typedef void* (*rt_opencl_create_buffer_fn)(void*, uint64_t, size_t, void*, int*);
typedef int (*rt_opencl_enqueue_write_buffer_fn)(void*, void*, uint32_t, size_t, size_t, const void*, uint32_t, const void**, void*);
typedef int (*rt_opencl_enqueue_read_buffer_fn)(void*, void*, uint32_t, size_t, size_t, void*, uint32_t, const void**, void*);
typedef int (*rt_opencl_enqueue_ndrange_kernel_fn)(void*, void*, uint32_t, const size_t*, const size_t*, const size_t*, uint32_t, const void**, void*);
typedef int (*rt_opencl_finish_fn)(void*);
typedef int (*rt_opencl_release_context_fn)(void*);
typedef int (*rt_opencl_release_command_queue_fn)(void*);
typedef int (*rt_opencl_release_program_fn)(void*);
typedef int (*rt_opencl_release_kernel_fn)(void*);
typedef int (*rt_opencl_release_mem_object_fn)(void*);

typedef struct RtOpenClFns {
    rt_opencl_get_platform_ids_fn get_platform_ids;
    rt_opencl_get_device_ids_fn get_device_ids;
    rt_opencl_create_context_fn create_context;
    rt_opencl_create_command_queue_fn create_command_queue;
    rt_opencl_create_command_queue_with_properties_fn create_command_queue_with_properties;
    rt_opencl_create_program_with_source_fn create_program_with_source;
    rt_opencl_build_program_fn build_program;
    rt_opencl_create_kernel_fn create_kernel;
    rt_opencl_set_kernel_arg_fn set_kernel_arg;
    rt_opencl_create_buffer_fn create_buffer;
    rt_opencl_enqueue_write_buffer_fn enqueue_write_buffer;
    rt_opencl_enqueue_read_buffer_fn enqueue_read_buffer;
    rt_opencl_enqueue_ndrange_kernel_fn enqueue_ndrange_kernel;
    rt_opencl_finish_fn finish;
    rt_opencl_release_context_fn release_context;
    rt_opencl_release_command_queue_fn release_command_queue;
    rt_opencl_release_program_fn release_program;
    rt_opencl_release_kernel_fn release_kernel;
    rt_opencl_release_mem_object_fn release_mem_object;
} RtOpenClFns;

typedef struct RtOpenClContext {
    uint32_t magic;
    void* platform;
    void* device;
    void* context;
} RtOpenClContext;

typedef struct RtOpenClQueue {
    uint32_t magic;
    RtOpenClContext* owner;
    void* queue;
} RtOpenClQueue;

typedef struct RtOpenClProgram {
    uint32_t magic;
    RtOpenClContext* owner;
    void* program;
} RtOpenClProgram;

typedef struct RtOpenClKernel {
    uint32_t magic;
    RtOpenClProgram* owner;
    void* kernel;
} RtOpenClKernel;

typedef struct RtOpenClBuffer {
    uint32_t magic;
    RtOpenClContext* owner;
    void* mem;
    size_t size;
} RtOpenClBuffer;

static RtOpenClFns* rt_opencl_load_symbols(void) {
#if defined(_WIN32)
    return NULL;
#else
    static void* opencl_handle = NULL;
    static RtOpenClFns fns;
    static int attempted = 0;
    if (attempted) return fns.get_platform_ids ? &fns : NULL;
    attempted = 1;
    opencl_handle = dlopen("libOpenCL.so.1", RTLD_LAZY | RTLD_LOCAL);
    if (!opencl_handle) {
        opencl_handle = dlopen("libOpenCL.so", RTLD_LAZY | RTLD_LOCAL);
    }
    if (!opencl_handle) return NULL;
    fns.get_platform_ids = (rt_opencl_get_platform_ids_fn)dlsym(opencl_handle, "clGetPlatformIDs");
    fns.get_device_ids = (rt_opencl_get_device_ids_fn)dlsym(opencl_handle, "clGetDeviceIDs");
    fns.create_context = (rt_opencl_create_context_fn)dlsym(opencl_handle, "clCreateContext");
    fns.create_command_queue = (rt_opencl_create_command_queue_fn)dlsym(opencl_handle, "clCreateCommandQueue");
    fns.create_command_queue_with_properties = (rt_opencl_create_command_queue_with_properties_fn)dlsym(opencl_handle, "clCreateCommandQueueWithProperties");
    fns.create_program_with_source = (rt_opencl_create_program_with_source_fn)dlsym(opencl_handle, "clCreateProgramWithSource");
    fns.build_program = (rt_opencl_build_program_fn)dlsym(opencl_handle, "clBuildProgram");
    fns.create_kernel = (rt_opencl_create_kernel_fn)dlsym(opencl_handle, "clCreateKernel");
    fns.set_kernel_arg = (rt_opencl_set_kernel_arg_fn)dlsym(opencl_handle, "clSetKernelArg");
    fns.create_buffer = (rt_opencl_create_buffer_fn)dlsym(opencl_handle, "clCreateBuffer");
    fns.enqueue_write_buffer = (rt_opencl_enqueue_write_buffer_fn)dlsym(opencl_handle, "clEnqueueWriteBuffer");
    fns.enqueue_read_buffer = (rt_opencl_enqueue_read_buffer_fn)dlsym(opencl_handle, "clEnqueueReadBuffer");
    fns.enqueue_ndrange_kernel = (rt_opencl_enqueue_ndrange_kernel_fn)dlsym(opencl_handle, "clEnqueueNDRangeKernel");
    fns.finish = (rt_opencl_finish_fn)dlsym(opencl_handle, "clFinish");
    fns.release_context = (rt_opencl_release_context_fn)dlsym(opencl_handle, "clReleaseContext");
    fns.release_command_queue = (rt_opencl_release_command_queue_fn)dlsym(opencl_handle, "clReleaseCommandQueue");
    fns.release_program = (rt_opencl_release_program_fn)dlsym(opencl_handle, "clReleaseProgram");
    fns.release_kernel = (rt_opencl_release_kernel_fn)dlsym(opencl_handle, "clReleaseKernel");
    fns.release_mem_object = (rt_opencl_release_mem_object_fn)dlsym(opencl_handle, "clReleaseMemObject");
    if (!fns.get_platform_ids || !fns.get_device_ids || !fns.create_context ||
        (!fns.create_command_queue && !fns.create_command_queue_with_properties) ||
        !fns.create_program_with_source || !fns.build_program || !fns.create_kernel ||
        !fns.set_kernel_arg || !fns.create_buffer || !fns.enqueue_write_buffer ||
        !fns.enqueue_read_buffer || !fns.enqueue_ndrange_kernel || !fns.finish ||
        !fns.release_mem_object) {
        return NULL;
    }
    return &fns;
#endif
}

static bool rt_opencl_handle_is_plausible(int64_t handle) {
    return handle >= 4096;
}

static int rt_opencl_platform_at(RtOpenClFns* fns, int64_t platform_index, void** out_platform) {
    if (!fns || !out_platform) return 0;
    uint32_t count = 0;
    if (fns->get_platform_ids(0, NULL, &count) != RT_OPENCL_SUCCESS || count == 0) return 0;
    void** platforms = (void**)calloc(count, sizeof(void*));
    if (!platforms) return 0;
    int ok = fns->get_platform_ids(count, platforms, NULL) == RT_OPENCL_SUCCESS;
    uint32_t index = platform_index <= 1 ? 0 : (uint32_t)(platform_index - 1);
    if (!ok || index >= count || !platforms[index]) {
        free(platforms);
        return 0;
    }
    *out_platform = platforms[index];
    free(platforms);
    return 1;
}

static int rt_opencl_first_non_cpu_device(RtOpenClFns* fns, void* platform, void** out_device) {
    if (!fns || !platform || !out_device) return 0;
    rt_opencl_device_type types[2] = {
        RT_OPENCL_DEVICE_TYPE_GPU,
        RT_OPENCL_DEVICE_TYPE_ACCELERATOR
    };
    for (size_t i = 0; i < 2; i++) {
        uint32_t count = 0;
        if (fns->get_device_ids(platform, types[i], 0, NULL, &count) != RT_OPENCL_SUCCESS || count == 0) {
            continue;
        }
        void* device = NULL;
        if (fns->get_device_ids(platform, types[i], 1, &device, NULL) == RT_OPENCL_SUCCESS && device) {
            *out_device = device;
            return 1;
        }
    }
    return 0;
}

int64_t rt_opencl_platform_count(void) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    if (!fns) return 0;
    uint32_t count = 0;
    int status = fns->get_platform_ids(0, NULL, &count);
    if (status != 0) return 0;
    return (int64_t)count;
}

bool rt_opencl_is_available(void) {
    return rt_opencl_platform_count() > 0;
}

/* Honesty probe (lane N3, doc/03_plan/runtime/native_binding/dlopen_conversion_lanes.md):
 * walks the same dlopen -> platform -> device -> context sequence as
 * rt_opencl_create_context, but returns a DISTINCT stage code at each honest
 * outcome instead of collapsing every failure to 0. Passing
 * RT_OPENCL_PROBE_FORCE_CONTEXT_FAIL deliberately calls clCreateContext with
 * an empty device list, so the CONTEXT_FAILED branch (with a real CL status
 * code retrievable via rt_opencl_probe_last_status) is exercisable on any
 * host, not only one whose ICD happens to reject context creation. */
#define RT_OPENCL_PROBE_LIB_ABSENT 0
#define RT_OPENCL_PROBE_NO_PLATFORM 1
#define RT_OPENCL_PROBE_NO_DEVICE 2
#define RT_OPENCL_PROBE_CONTEXT_FAILED 3
#define RT_OPENCL_PROBE_CONTEXT_OK 4
#define RT_OPENCL_PROBE_FORCE_CONTEXT_FAIL (-999)

static int rt_opencl_probe_last_status_g = 0;

int64_t rt_opencl_probe_stage(int64_t platform_index) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    if (!fns) return RT_OPENCL_PROBE_LIB_ABSENT;

    if (platform_index == RT_OPENCL_PROBE_FORCE_CONTEXT_FAIL) {
        rt_opencl_context_property properties[] = { 0 };
        int status = 0;
        void* context = fns->create_context(properties, 0, NULL, NULL, NULL, &status);
        if (context && fns->release_context) fns->release_context(context);
        rt_opencl_probe_last_status_g = status;
        return RT_OPENCL_PROBE_CONTEXT_FAILED;
    }

    void* platform_handle = NULL;
    if (!rt_opencl_platform_at(fns, platform_index, &platform_handle)) return RT_OPENCL_PROBE_NO_PLATFORM;
    void* device = NULL;
    if (!rt_opencl_first_non_cpu_device(fns, platform_handle, &device)) return RT_OPENCL_PROBE_NO_DEVICE;

    rt_opencl_context_property properties[] = {
        RT_OPENCL_CONTEXT_PLATFORM, (rt_opencl_context_property)platform_handle, 0
    };
    int status = 0;
    void* context = fns->create_context(properties, 1, &device, NULL, NULL, &status);
    rt_opencl_probe_last_status_g = status;
    if (status != RT_OPENCL_SUCCESS || !context) return RT_OPENCL_PROBE_CONTEXT_FAILED;
    if (fns->release_context) fns->release_context(context);
    return RT_OPENCL_PROBE_CONTEXT_OK;
}

int64_t rt_opencl_probe_last_status(void) {
    return (int64_t)rt_opencl_probe_last_status_g;
}

int64_t rt_opencl_create_context(int64_t platform) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    void* platform_handle = NULL;
    void* device = NULL;
    if (!rt_opencl_platform_at(fns, platform, &platform_handle)) return 0;
    if (!rt_opencl_first_non_cpu_device(fns, platform_handle, &device)) return 0;
    rt_opencl_context_property properties[] = {
        RT_OPENCL_CONTEXT_PLATFORM, (rt_opencl_context_property)platform_handle, 0
    };
    int status = 0;
    void* context = fns->create_context(properties, 1, &device, NULL, NULL, &status);
    if (status != RT_OPENCL_SUCCESS || !context) return 0;
    RtOpenClContext* wrapped = (RtOpenClContext*)calloc(1, sizeof(RtOpenClContext));
    if (!wrapped) {
        if (fns->release_context) fns->release_context(context);
        return 0;
    }
    wrapped->magic = RT_OPENCL_CONTEXT_MAGIC;
    wrapped->platform = platform_handle;
    wrapped->device = device;
    wrapped->context = context;
    return (int64_t)(intptr_t)wrapped;
}

int64_t rt_opencl_create_queue(int64_t context) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClContext* wrapped_context = (RtOpenClContext*)(intptr_t)context;
    if (!fns || !rt_opencl_handle_is_plausible(context) || !wrapped_context || wrapped_context->magic != RT_OPENCL_CONTEXT_MAGIC) return 0;
    int status = 0;
    void* queue = NULL;
    if (fns->create_command_queue_with_properties) {
        queue = fns->create_command_queue_with_properties(wrapped_context->context, wrapped_context->device, NULL, &status);
    } else {
        queue = fns->create_command_queue(wrapped_context->context, wrapped_context->device, 0, &status);
    }
    if (status != RT_OPENCL_SUCCESS || !queue) return 0;
    RtOpenClQueue* wrapped = (RtOpenClQueue*)calloc(1, sizeof(RtOpenClQueue));
    if (!wrapped) {
        if (fns->release_command_queue) fns->release_command_queue(queue);
        return 0;
    }
    wrapped->magic = RT_OPENCL_QUEUE_MAGIC;
    wrapped->owner = wrapped_context;
    wrapped->queue = queue;
    return (int64_t)(intptr_t)wrapped;
}

int64_t rt_opencl_create_program(int64_t context, const char* source) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClContext* wrapped_context = (RtOpenClContext*)(intptr_t)context;
    if (!fns || !rt_opencl_handle_is_plausible(context) || !wrapped_context || wrapped_context->magic != RT_OPENCL_CONTEXT_MAGIC || !source || source[0] == '\0') {
        return 0;
    }
    const char* sources[] = { source };
    size_t lengths[] = { strlen(source) };
    int status = 0;
    void* program = fns->create_program_with_source(wrapped_context->context, 1, sources, lengths, &status);
    if (status != RT_OPENCL_SUCCESS || !program) return 0;
    RtOpenClProgram* wrapped = (RtOpenClProgram*)calloc(1, sizeof(RtOpenClProgram));
    if (!wrapped) {
        if (fns->release_program) fns->release_program(program);
        return 0;
    }
    wrapped->magic = RT_OPENCL_PROGRAM_MAGIC;
    wrapped->owner = wrapped_context;
    wrapped->program = program;
    return (int64_t)(intptr_t)wrapped;
}

bool rt_opencl_build_program(int64_t program) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClProgram* wrapped_program = (RtOpenClProgram*)(intptr_t)program;
    if (!fns || !rt_opencl_handle_is_plausible(program) || !wrapped_program || wrapped_program->magic != RT_OPENCL_PROGRAM_MAGIC || !wrapped_program->owner) {
        return false;
    }
    return fns->build_program(
        wrapped_program->program,
        1,
        &wrapped_program->owner->device,
        NULL,
        NULL,
        NULL
    ) == RT_OPENCL_SUCCESS;
}

int64_t rt_opencl_create_kernel(int64_t program, const char* name) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClProgram* wrapped_program = (RtOpenClProgram*)(intptr_t)program;
    if (!fns || !rt_opencl_handle_is_plausible(program) || !wrapped_program || wrapped_program->magic != RT_OPENCL_PROGRAM_MAGIC || !name || name[0] == '\0') {
        return 0;
    }
    int status = 0;
    void* kernel = fns->create_kernel(wrapped_program->program, name, &status);
    if (status != RT_OPENCL_SUCCESS || !kernel) return 0;
    RtOpenClKernel* wrapped = (RtOpenClKernel*)calloc(1, sizeof(RtOpenClKernel));
    if (!wrapped) {
        if (fns->release_kernel) fns->release_kernel(kernel);
        return 0;
    }
    wrapped->magic = RT_OPENCL_KERNEL_MAGIC;
    wrapped->owner = wrapped_program;
    wrapped->kernel = kernel;
    return (int64_t)(intptr_t)wrapped;
}

int64_t rt_opencl_mem_alloc(int64_t context, int64_t size) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClContext* wrapped_context = (RtOpenClContext*)(intptr_t)context;
    if (!fns || !rt_opencl_handle_is_plausible(context) || !wrapped_context ||
        wrapped_context->magic != RT_OPENCL_CONTEXT_MAGIC || size <= 0) {
        return 0;
    }
    int status = 0;
    void* mem = fns->create_buffer(wrapped_context->context, RT_OPENCL_MEM_READ_WRITE, (size_t)size, NULL, &status);
    if (status != RT_OPENCL_SUCCESS || !mem) return 0;
    RtOpenClBuffer* wrapped = (RtOpenClBuffer*)calloc(1, sizeof(RtOpenClBuffer));
    if (!wrapped) {
        fns->release_mem_object(mem);
        return 0;
    }
    wrapped->magic = RT_OPENCL_BUFFER_MAGIC;
    wrapped->owner = wrapped_context;
    wrapped->mem = mem;
    wrapped->size = (size_t)size;
    return (int64_t)(intptr_t)wrapped;
}

bool rt_opencl_mem_free(int64_t buffer) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClBuffer* wrapped_buffer = (RtOpenClBuffer*)(intptr_t)buffer;
    if (!fns || !rt_opencl_handle_is_plausible(buffer) || !wrapped_buffer ||
        wrapped_buffer->magic != RT_OPENCL_BUFFER_MAGIC) {
        return false;
    }
    int status = fns->release_mem_object(wrapped_buffer->mem);
    wrapped_buffer->magic = 0;
    free(wrapped_buffer);
    return status == RT_OPENCL_SUCCESS;
}

bool rt_opencl_write_buffer_at(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size, int64_t offset) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClQueue* wrapped_queue = (RtOpenClQueue*)(intptr_t)queue;
    RtOpenClBuffer* wrapped_buffer = (RtOpenClBuffer*)(intptr_t)buffer;
    if (!fns || !rt_opencl_handle_is_plausible(queue) || !rt_opencl_handle_is_plausible(buffer) ||
        !wrapped_queue || !wrapped_buffer || host_ptr == 0 || size <= 0 || offset < 0 ||
        wrapped_queue->magic != RT_OPENCL_QUEUE_MAGIC ||
        wrapped_buffer->magic != RT_OPENCL_BUFFER_MAGIC ||
        (uint64_t)offset > wrapped_buffer->size ||
        (uint64_t)size > wrapped_buffer->size - (size_t)offset) {
        return false;
    }
    return fns->enqueue_write_buffer(
        wrapped_queue->queue,
        wrapped_buffer->mem,
        RT_OPENCL_TRUE,
        (size_t)offset,
        (size_t)size,
        (const void*)(intptr_t)host_ptr,
        0,
        NULL,
        NULL
    ) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_write_buffer(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size) {
    return rt_opencl_write_buffer_at(queue, buffer, host_ptr, size, 0);
}

bool rt_opencl_read_buffer(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClQueue* wrapped_queue = (RtOpenClQueue*)(intptr_t)queue;
    RtOpenClBuffer* wrapped_buffer = (RtOpenClBuffer*)(intptr_t)buffer;
    if (!fns || !rt_opencl_handle_is_plausible(queue) || !rt_opencl_handle_is_plausible(buffer) ||
        !wrapped_queue || !wrapped_buffer || host_ptr == 0 || size <= 0 ||
        wrapped_queue->magic != RT_OPENCL_QUEUE_MAGIC ||
        wrapped_buffer->magic != RT_OPENCL_BUFFER_MAGIC ||
        (size_t)size > wrapped_buffer->size) {
        return false;
    }
    return fns->enqueue_read_buffer(
        wrapped_queue->queue,
        wrapped_buffer->mem,
        RT_OPENCL_TRUE,
        0,
        (size_t)size,
        (void*)(intptr_t)host_ptr,
        0,
        NULL,
        NULL
    ) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_set_kernel_arg_i64(int64_t kernel, int64_t index, int64_t value) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClKernel* wrapped_kernel = (RtOpenClKernel*)(intptr_t)kernel;
    if (!fns || !rt_opencl_handle_is_plausible(kernel) || !wrapped_kernel ||
        wrapped_kernel->magic != RT_OPENCL_KERNEL_MAGIC || index < 0) {
        return false;
    }
    int64_t arg = value;
    return fns->set_kernel_arg(wrapped_kernel->kernel, (uint32_t)index, sizeof(arg), &arg) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_set_kernel_arg_buffer(int64_t kernel, int64_t index, int64_t buffer) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClKernel* wrapped_kernel = (RtOpenClKernel*)(intptr_t)kernel;
    RtOpenClBuffer* wrapped_buffer = (RtOpenClBuffer*)(intptr_t)buffer;
    if (!fns || !rt_opencl_handle_is_plausible(kernel) || !rt_opencl_handle_is_plausible(buffer) ||
        !wrapped_kernel || !wrapped_buffer || index < 0 ||
        wrapped_kernel->magic != RT_OPENCL_KERNEL_MAGIC ||
        wrapped_buffer->magic != RT_OPENCL_BUFFER_MAGIC) {
        return false;
    }
    void* mem = wrapped_buffer->mem;
    return fns->set_kernel_arg(wrapped_kernel->kernel, (uint32_t)index, sizeof(mem), &mem) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_enqueue_ndrange(int64_t queue, int64_t kernel, int64_t gx, int64_t gy, int64_t gz, int64_t lx, int64_t ly, int64_t lz) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClQueue* wrapped_queue = (RtOpenClQueue*)(intptr_t)queue;
    RtOpenClKernel* wrapped_kernel = (RtOpenClKernel*)(intptr_t)kernel;
    if (!fns || !rt_opencl_handle_is_plausible(queue) || !rt_opencl_handle_is_plausible(kernel) ||
        !wrapped_queue || !wrapped_kernel ||
        wrapped_queue->magic != RT_OPENCL_QUEUE_MAGIC ||
        wrapped_kernel->magic != RT_OPENCL_KERNEL_MAGIC ||
        gx <= 0 || gy <= 0 || gz <= 0) {
        return false;
    }
    size_t global[3] = { (size_t)gx, (size_t)gy, (size_t)gz };
    size_t local[3] = { (size_t)lx, (size_t)ly, (size_t)lz };
    const size_t* local_ptr = (lx > 0 && ly > 0 && lz > 0) ? local : NULL;
    return fns->enqueue_ndrange_kernel(
        wrapped_queue->queue,
        wrapped_kernel->kernel,
        3,
        NULL,
        global,
        local_ptr,
        0,
        NULL,
        NULL
    ) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_finish(int64_t queue) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClQueue* wrapped_queue = (RtOpenClQueue*)(intptr_t)queue;
    if (!fns || !rt_opencl_handle_is_plausible(queue) || !wrapped_queue || wrapped_queue->magic != RT_OPENCL_QUEUE_MAGIC) return false;
    return fns->finish(wrapped_queue->queue) == RT_OPENCL_SUCCESS;
}

bool rt_opencl_release_kernel(int64_t kernel) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClKernel* wrapped_kernel = (RtOpenClKernel*)(intptr_t)kernel;
    if (!fns || !fns->release_kernel || !rt_opencl_handle_is_plausible(kernel) || !wrapped_kernel || wrapped_kernel->magic != RT_OPENCL_KERNEL_MAGIC) return false;
    int status = fns->release_kernel(wrapped_kernel->kernel);
    wrapped_kernel->magic = 0;
    free(wrapped_kernel);
    return status == RT_OPENCL_SUCCESS;
}

bool rt_opencl_release_program(int64_t program) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClProgram* wrapped_program = (RtOpenClProgram*)(intptr_t)program;
    if (!fns || !fns->release_program || !rt_opencl_handle_is_plausible(program) || !wrapped_program || wrapped_program->magic != RT_OPENCL_PROGRAM_MAGIC) return false;
    int status = fns->release_program(wrapped_program->program);
    wrapped_program->magic = 0;
    free(wrapped_program);
    return status == RT_OPENCL_SUCCESS;
}

bool rt_opencl_release_queue(int64_t queue) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClQueue* wrapped_queue = (RtOpenClQueue*)(intptr_t)queue;
    if (!fns || !fns->release_command_queue || !rt_opencl_handle_is_plausible(queue) || !wrapped_queue || wrapped_queue->magic != RT_OPENCL_QUEUE_MAGIC) return false;
    int status = fns->release_command_queue(wrapped_queue->queue);
    wrapped_queue->magic = 0;
    free(wrapped_queue);
    return status == RT_OPENCL_SUCCESS;
}

bool rt_opencl_release_context(int64_t context) {
    RtOpenClFns* fns = rt_opencl_load_symbols();
    RtOpenClContext* wrapped_context = (RtOpenClContext*)(intptr_t)context;
    if (!fns || !fns->release_context || !rt_opencl_handle_is_plausible(context) || !wrapped_context || wrapped_context->magic != RT_OPENCL_CONTEXT_MAGIC) return false;
    int status = fns->release_context(wrapped_context->context);
    wrapped_context->magic = 0;
    free(wrapped_context);
    return status == RT_OPENCL_SUCCESS;
}

#if !defined(SIMPLE_RUNTIME_OPENCL_ONLY)

static int engine2d_span_bounds(SplArray* array, int64_t offset, int64_t count,
                                int64_t* out_offset, int64_t* out_count) {
    if (!array || !out_offset || !out_count) return 0;
    int64_t len = rt_array_len(array);
    if (offset < 0 || count <= 0 || offset >= len) return 0;
    if (count > len - offset) count = len - offset;
    *out_offset = offset;
    *out_count = count;
    return count > 0;
}

#if defined(__aarch64__) || defined(_M_ARM64)
#  include <arm_neon.h>
#endif

#if defined(__riscv) && defined(__riscv_vector)
#  include <riscv_vector.h>
#endif

static atomic_uint_fast64_t g_engine2d_simd_row_hits;

static inline int64_t engine2d_box_pixel(uint32_t pixel) {
    return (int64_t)((uint64_t)pixel << 3);
}

static inline uint32_t engine2d_unbox_pixel(int64_t value) {
    return (uint32_t)((uint64_t)value >> 3);
}

static inline void engine2d_record_simd_row_hit(void) {
    atomic_fetch_add_explicit(&g_engine2d_simd_row_hits, 1, memory_order_relaxed);
}

int64_t rt_simd_engine2d_neon_hits(void) {
    return (int64_t)atomic_load_explicit(&g_engine2d_simd_row_hits, memory_order_relaxed);
}

int64_t rt_simd_engine2d_neon_reset(void) {
    atomic_store_explicit(&g_engine2d_simd_row_hits, 0, memory_order_relaxed);
    return 0;
}

/* MLKEM_SIMD_BEGIN
 * ML-KEM native SIMD NTT/INTT.
 *
 * The Simple boundary is a flat [i64] containing one or more 256-coefficient
 * polynomials. Values are unboxed once, transformed in an int32 work buffer,
 * and boxed into a fresh array. AVX2, NEON, and RVV vectorize butterfly
 * arithmetic plus exact canonical reciprocal reduction; scalar code handles
 * only sub-vector stage tails and unsupported backends.
 * ---------------------------------------------------------------------- */

#if defined(_MSC_VER)
#define MLKEM_THREAD_LOCAL __declspec(thread)
#else
#define MLKEM_THREAD_LOCAL _Thread_local
#endif

/* Synchronous operation receipt. ML-KEM candidate entry points reset, execute,
 * and read this value without yielding. Thread-local ownership prevents one
 * native request from resetting or claiming another request's SIMD work. */
static MLKEM_THREAD_LOCAL uint64_t g_mlkem_ntt_simd_hits;
static MLKEM_THREAD_LOCAL uint64_t g_mlkem_ntt_simd_observed_rvv_vlen_bits;

static SplArray* mlkem_new_i64_array(int64_t count) {
    if (count < 0) count = 0;
    SplArray* result = rt_array_new_uninit(count);
    if (!result) return NULL;
    rt_array_set_len_known(rt_array_header_ptr(result), count);
    return result;
}

static const int32_t g_mlkem_ntt_zetas[128] = {
       1, 1729, 2580, 3289, 2642,  630, 1897,  848,
    1062, 1919,  193,  797, 2786, 3260,  569, 1746,
     296, 2447, 1339, 1476, 3046,   56, 2240, 1333,
    1426, 2094,  535, 2882, 2393, 2879, 1974,  821,
     289,  331, 3253, 1756, 1197, 2304, 2277, 2055,
     650, 1977, 2513,  632, 2865,   33, 1320, 1915,
    2319, 1435,  807,  452, 1438, 2868, 1534, 2402,
    2647, 2617, 1481,  648, 2474, 3110, 1227,  910,
      17, 2761,  583, 2649, 1637,  723, 2288, 1100,
    1409, 2662, 3281,  233,  756, 2156, 3015, 3050,
    1703, 1651, 2789, 1789, 1847,  952, 1461, 2687,
     939, 2308, 2437, 2388,  733, 2337,  268,  641,
    1584, 2298, 2037, 3220,  375, 2549, 2090, 1645,
    1063,  319, 2773,  757, 2099,  561, 2466, 2594,
    2804, 1092,  403, 1026, 1143, 2150, 2775,  886,
    1722, 1212, 1874, 1029, 2110, 2935,  885, 2154
};

static inline int32_t mlkem_modq_i64(int64_t value) {
    int64_t reduced = value % 3329;
    return (int32_t)(reduced < 0 ? reduced + 3329 : reduced);
}

#if defined(__x86_64__) || defined(_M_X64)
/* Exact q=3329 reduction for the reachable NTT butterfly interval.
 *
 * Butterfly inputs are canonical [0,q), so every pre-reduction value lies in
 * [-11,078,912, 11,078,912]. Adding 4096*q makes it positive without changing
 * its residue.  floor(2^32/q) underestimates the quotient by at most one in
 * this interval; the final conditional subtract therefore canonicalizes the
 * exact residue without division or floating point.
 */
SIMPLE_RUNTIME_TARGET_AVX2
static inline __m256i mlkem_reduce8_avx2(__m256i value) {
    const __m256i bias = _mm256_set1_epi32(13635584); /* 4096 * 3329 */
    const __m256i reciprocal = _mm256_set1_epi32(1290167); /* floor(2^32/q) */
    const __m256i modulus = _mm256_set1_epi32(3329);
    __m256i positive = _mm256_add_epi32(value, bias);
    __m256i even_product = _mm256_mul_epu32(positive, reciprocal);
    __m256i odd_values = _mm256_srli_epi64(positive, 32);
    __m256i odd_product = _mm256_mul_epu32(odd_values, reciprocal);
    __m256i even_quotient = _mm256_srli_epi64(even_product, 32);
    __m256i odd_quotient = _mm256_slli_epi64(
        _mm256_srli_epi64(odd_product, 32), 32);
    __m256i quotient = _mm256_or_si256(even_quotient, odd_quotient);
    __m256i residue = _mm256_sub_epi32(
        positive, _mm256_mullo_epi32(quotient, modulus));
    __m256i subtract_mask = _mm256_cmpgt_epi32(
        residue, _mm256_set1_epi32(3328));
    return _mm256_sub_epi32(
        residue, _mm256_and_si256(subtract_mask, modulus));
}

SIMPLE_RUNTIME_TARGET_AVX2
static void mlkem_butterfly8_avx2(int32_t* lower, int32_t* upper,
                                  int32_t zeta, bool inverse) {
    __m256i lo = _mm256_loadu_si256((const __m256i*)(const void*)lower);
    __m256i hi = _mm256_loadu_si256((const __m256i*)(const void*)upper);
    __m256i zv = _mm256_set1_epi32(zeta);
    __m256i sum;
    __m256i product;
    if (inverse) {
        sum = _mm256_add_epi32(lo, hi);
        product = _mm256_mullo_epi32(_mm256_sub_epi32(hi, lo), zv);
    } else {
        product = _mm256_mullo_epi32(hi, zv);
        sum = _mm256_add_epi32(lo, product);
        product = _mm256_sub_epi32(lo, product);
    }
    _mm256_storeu_si256((__m256i*)(void*)lower, mlkem_reduce8_avx2(sum));
    _mm256_storeu_si256((__m256i*)(void*)upper, mlkem_reduce8_avx2(product));
}

SIMPLE_RUNTIME_TARGET_AVX2
static void mlkem_inverse_scale_avx2(int32_t* coefficients) {
    const __m256i scale = _mm256_set1_epi32(3303);
    for (int i = 0; i < 256; i += 8) {
        __m256i values = _mm256_loadu_si256(
            (const __m256i*)(const void*)(coefficients + i));
        __m256i products = _mm256_mullo_epi32(values, scale);
        _mm256_storeu_si256(
            (__m256i*)(void*)(coefficients + i),
            mlkem_reduce8_avx2(products));
    }
}

SIMPLE_RUNTIME_TARGET_AVX2
int64_t rt_mlkem_modq_avx2_selfcheck(void) {
    if (!simd_detect_avx2()) return -1;
    const int32_t limit = 11078912;
    int32_t input[8];
    int32_t output[8];
    int64_t mismatches = 0;
    for (int32_t base = -limit; base <= limit; base += 8) {
        for (int lane = 0; lane < 8; lane++) input[lane] = base + lane;
        __m256i values = _mm256_loadu_si256((const __m256i*)(const void*)input);
        _mm256_storeu_si256((__m256i*)(void*)output, mlkem_reduce8_avx2(values));
        for (int lane = 0; lane < 8 && input[lane] <= limit; lane++) {
            if (output[lane] != mlkem_modq_i64(input[lane])) mismatches++;
        }
    }
    return mismatches;
}
#else
int64_t rt_mlkem_modq_avx2_selfcheck(void) { return -1; }
#endif

#if defined(__aarch64__) || defined(_M_ARM64)
static inline int32x4_t mlkem_reduce4_neon(int32x4_t value) {
    const uint32x4_t positive = vreinterpretq_u32_s32(
        vaddq_s32(value, vdupq_n_s32(13635584)));
    const uint32x2_t reciprocal = vdup_n_u32(1290167);
    const uint64x2_t low_product = vmull_u32(
        vget_low_u32(positive), reciprocal);
    const uint64x2_t high_product = vmull_u32(
        vget_high_u32(positive), reciprocal);
    const uint32x4_t quotient = vcombine_u32(
        vmovn_u64(vshrq_n_u64(low_product, 32)),
        vmovn_u64(vshrq_n_u64(high_product, 32)));
    const uint32x4_t modulus = vdupq_n_u32(3329);
    uint32x4_t residue = vsubq_u32(
        positive, vmulq_u32(quotient, modulus));
    const uint32x4_t subtract_mask = vcgeq_u32(residue, modulus);
    residue = vsubq_u32(residue, vandq_u32(subtract_mask, modulus));
    return vreinterpretq_s32_u32(residue);
}

static void mlkem_butterfly4_neon(int32_t* lower, int32_t* upper,
                                  int32_t zeta, bool inverse) {
    int32x4_t lo = vld1q_s32(lower);
    int32x4_t hi = vld1q_s32(upper);
    int32x4_t zv = vdupq_n_s32(zeta);
    int32x4_t sum;
    int32x4_t product;
    if (inverse) {
        sum = vaddq_s32(lo, hi);
        product = vmulq_s32(vsubq_s32(hi, lo), zv);
    } else {
        product = vmulq_s32(hi, zv);
        sum = vaddq_s32(lo, product);
        product = vsubq_s32(lo, product);
    }
    vst1q_s32(lower, mlkem_reduce4_neon(sum));
    vst1q_s32(upper, mlkem_reduce4_neon(product));
}

static void mlkem_inverse_scale_neon(int32_t* coefficients) {
    const int32x4_t scale = vdupq_n_s32(3303);
    for (int i = 0; i < 256; i += 4) {
        const int32x4_t values = vld1q_s32(coefficients + i);
        vst1q_s32(coefficients + i,
            mlkem_reduce4_neon(vmulq_s32(values, scale)));
    }
}
#endif

#if defined(__riscv) && defined(__riscv_vector)
static vint32m1_t mlkem_reduce_rvv(vint32m1_t value, size_t vl) {
    const vint32m1_t positive = __riscv_vadd_vx_i32m1(
        value, 13635584, vl);
    const vint64m2_t product = __riscv_vwmul_vx_i64m2(
        positive, 1290167, vl);
    const vint32m1_t quotient = __riscv_vnsra_wx_i32m1(
        product, 32, vl);
    vint32m1_t residue = __riscv_vsub_vv_i32m1(
        positive, __riscv_vmul_vx_i32m1(quotient, 3329, vl), vl);
    const vint32m1_t reduced = __riscv_vsub_vx_i32m1(
        residue, 3329, vl);
    const vbool32_t subtract = __riscv_vmsge_vx_i32m1_b32(
        residue, 3329, vl);
    return __riscv_vmerge_vvm_i32m1(residue, reduced, subtract, vl);
}

static size_t mlkem_butterfly_rvv(int32_t* lower, int32_t* upper,
                                  size_t count, int32_t zeta, bool inverse,
                                  uint64_t* chunk_count) {
    size_t done = 0;
    uint64_t chunks = 0;
    while (done < count) {
        size_t vl = __riscv_vsetvl_e32m1(count - done);
        vint32m1_t lo = __riscv_vle32_v_i32m1(lower + done, vl);
        vint32m1_t hi = __riscv_vle32_v_i32m1(upper + done, vl);
        vint32m1_t sum;
        vint32m1_t product;
        if (inverse) {
            sum = __riscv_vadd_vv_i32m1(lo, hi, vl);
            product = __riscv_vmul_vx_i32m1(
                __riscv_vsub_vv_i32m1(hi, lo, vl), zeta, vl);
        } else {
            product = __riscv_vmul_vx_i32m1(hi, zeta, vl);
            sum = __riscv_vadd_vv_i32m1(lo, product, vl);
            product = __riscv_vsub_vv_i32m1(lo, product, vl);
        }
        __riscv_vse32_v_i32m1(
            lower + done, mlkem_reduce_rvv(sum, vl), vl);
        __riscv_vse32_v_i32m1(
            upper + done, mlkem_reduce_rvv(product, vl), vl);
        done += vl;
        chunks++;
    }
    if (chunk_count) *chunk_count = chunks;
    return done;
}

static void mlkem_inverse_scale_rvv(int32_t* coefficients) {
    size_t done = 0;
    while (done < 256) {
        const size_t vl = __riscv_vsetvl_e32m1(256 - done);
        const vint32m1_t values = __riscv_vle32_v_i32m1(
            coefficients + done, vl);
        const vint32m1_t products = __riscv_vmul_vx_i32m1(
            values, 3303, vl);
        __riscv_vse32_v_i32m1(
            coefficients + done, mlkem_reduce_rvv(products, vl), vl);
        done += vl;
    }
}
#endif

int64_t rt_mlkem_ntt_simd_backend(void) {
#if defined(__x86_64__) || defined(_M_X64)
    return simd_detect_avx2() ? 1 : 0;
#elif defined(__aarch64__) || defined(_M_ARM64)
    return 2;
#elif defined(__riscv) && defined(__riscv_vector)
    return rt_simd_has_rvv() ? 3 : 0;
#else
    return 0;
#endif
}

int64_t rt_mlkem_ntt_simd_hits(void) {
    return g_mlkem_ntt_simd_hits > (uint64_t)INT64_MAX
        ? INT64_MAX : (int64_t)g_mlkem_ntt_simd_hits;
}

int64_t rt_mlkem_ntt_simd_observed_rvv_vlen_bits(void) {
    return g_mlkem_ntt_simd_observed_rvv_vlen_bits > (uint64_t)INT64_MAX
        ? INT64_MAX : (int64_t)g_mlkem_ntt_simd_observed_rvv_vlen_bits;
}

int64_t rt_mlkem_ntt_simd_reset(void) {
    g_mlkem_ntt_simd_hits = 0;
    g_mlkem_ntt_simd_observed_rvv_vlen_bits = 0;
    return 0;
}

static uint64_t mlkem_ntt_one(int32_t* f, bool inverse, int64_t backend) {
    uint64_t hits = 0;
    int k = inverse ? 127 : 1;
    int len = inverse ? 2 : 128;
    while (inverse ? len <= 128 : len >= 2) {
        for (int start = 0; start < 256; start += 2 * len) {
            int32_t zeta = g_mlkem_ntt_zetas[k];
            k += inverse ? -1 : 1;
            int j = start;
            const int end = start + len;
            while (j < end) {
                uint64_t executed_chunks = 0;
#if defined(__x86_64__) || defined(_M_X64)
                if (backend == 1) {
                while (j + 8 <= end) {
                    mlkem_butterfly8_avx2(
                        f + j, f + j + len, zeta, inverse);
                    j += 8;
                    hits += 1;
                }
                }
#elif defined(__aarch64__) || defined(_M_ARM64)
                if (backend == 2) {
                while (j + 4 <= end) {
                    mlkem_butterfly4_neon(
                        f + j, f + j + len, zeta, inverse);
                    j += 4;
                    hits += 1;
                }
                }
#elif defined(__riscv) && defined(__riscv_vector)
                if (backend == 3 && j < end) {
                    j += (int)mlkem_butterfly_rvv(
                        f + j, f + j + len, (size_t)(end - j), zeta, inverse,
                        &executed_chunks);
                    hits += executed_chunks;
                    continue;
                }
#endif
                /* AVX2/NEON may consume the whole butterfly group above.
                 * Do not execute a scalar butterfly at j == end: that would
                 * overwrite the first lane of the next group. */
                if (j >= end) continue;
                int32_t lo = f[j];
                int32_t hi = f[j + len];
                if (inverse) {
                    f[j] = mlkem_modq_i64((int64_t)lo + hi);
                    f[j + len] = mlkem_modq_i64(
                        (int64_t)zeta * mlkem_modq_i64((int64_t)hi - lo));
                } else {
                    int32_t product = mlkem_modq_i64((int64_t)zeta * hi);
                    f[j] = mlkem_modq_i64((int64_t)lo + product);
                    f[j + len] = mlkem_modq_i64((int64_t)lo - product);
                }
                j++;
            }
        }
        len = inverse ? len * 2 : len / 2;
    }
    if (inverse) {
#if defined(__x86_64__) || defined(_M_X64)
        if (backend == 1) {
            mlkem_inverse_scale_avx2(f);
        } else
#elif defined(__aarch64__) || defined(_M_ARM64)
        if (backend == 2) {
            mlkem_inverse_scale_neon(f);
        } else
#elif defined(__riscv) && defined(__riscv_vector)
        if (backend == 3) {
            mlkem_inverse_scale_rvv(f);
        } else
#endif
        {
            for (int i = 0; i < 256; i++)
                f[i] = mlkem_modq_i64((int64_t)f[i] * 3303);
        }
    }
    return hits;
}

SplArray* rt_mlkem_ntt_simd_batch(SplArray* coefficients, bool inverse) {
    if (!coefficients) return mlkem_new_i64_array(0);
    int64_t count = rt_array_len(coefficients);
    if (count < 0 || count % 256 != 0)
        return mlkem_new_i64_array(0);
    if (count == 0) return mlkem_new_i64_array(0);
    const int64_t* input = (const int64_t*)(uintptr_t)
        rt_array_data_ptr(coefficients);
    if (!input) return mlkem_new_i64_array(0);
    SplArray* result = mlkem_new_i64_array(count);
    if (!result) return NULL;
    int64_t* output = (int64_t*)(uintptr_t)rt_array_data_ptr(result);
    if (!output) return result;
    int64_t backend = rt_mlkem_ntt_simd_backend();
    uint64_t hits = 0;
    for (int64_t offset = 0; offset < count; offset += 256) {
        int32_t work[256];
        for (int64_t i = 0; i < 256; i++)
            work[i] = mlkem_modq_i64(
                rv_to_int((RuntimeValue)input[offset + i]));
        hits += mlkem_ntt_one(work, inverse, backend);
        for (int64_t i = 0; i < 256; i++)
            output[offset + i] = (int64_t)rv_from_int(work[i]);
        /* Coefficients can contain secret material. A volatile wipe prevents
         * the compiler from deleting cleanup of this bounded stack scratch. */
        volatile int32_t* wipe = work;
        for (int64_t i = 0; i < 256; i++) wipe[i] = 0;
    }
    if (hits > 0) {
#if defined(__riscv) && defined(__riscv_vector)
        if (backend == 3) {
            g_mlkem_ntt_simd_observed_rvv_vlen_bits =
                (uint64_t)__riscv_vsetvlmax_e32m1() * 32u;
        }
#endif
        if (UINT64_MAX - g_mlkem_ntt_simd_hits < hits)
            g_mlkem_ntt_simd_hits = UINT64_MAX;
        else
            g_mlkem_ntt_simd_hits += hits;
    }
    return result;
}

/* MLKEM_SIMD_END */

#if defined(__x86_64__) || defined(_M_X64)
static void engine2d_fill_u32_sse2(int64_t* data, int64_t count, int64_t color);
SIMPLE_RUNTIME_TARGET_AVX2
static void engine2d_fill_u32_avx2(int64_t* data, int64_t count, int64_t color);
static void engine2d_blend_into_sse2(int64_t* out, const int64_t* dst,
                                     const int64_t* src, int64_t n);
SIMPLE_RUNTIME_TARGET_AVX2
static void engine2d_blend_into_avx2(int64_t* out, const int64_t* dst,
                                     const int64_t* src, int64_t n);
#endif

#if defined(__riscv) && defined(__riscv_vector)
static void engine2d_fill_u32_rvv(int64_t* data, int64_t count, int64_t color);
static void engine2d_copy_u32_rvv(int64_t* dst, const int64_t* src, int64_t count);
#endif

/* ----------------------------------------------------------------------
 * engine2d row kernels (RETURN-style) — build and return a NEW array.
 *
 * The pure math uses raw packed int64_t lanes whose low 32 bits are ARGB
 * 0xAARRGGBB. SplArray entry points box those values for Simple's tagged-int
 * element storage. The static raw-buffer helpers
 * operate on int64_t* so they can be NEON-vectorized and unit-tested
 * directly; the SplArray entry points just allocate and delegate.
 * -------------------------------------------------------------------- */

static void engine2d_fill_into(int64_t* out, int64_t n, int64_t color) {
    int64_t color_word = color;
    int64_t i = 0;
#if defined(__aarch64__) || defined(_M_ARM64)
    uint64x2_t v = vdupq_n_u64((uint64_t)color_word);
    if (n >= 2) engine2d_record_simd_row_hit();
    for (; i + 2 <= n; i += 2) {
        vst1q_u64((uint64_t*)(void*)(out + i), v);
    }
#elif defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_fill_u32_avx2(out, n, color_word);
        return;
    }
    engine2d_fill_u32_sse2(out, n, color_word);
    return;
#elif defined(__riscv) && defined(__riscv_vector)
    engine2d_fill_u32_rvv(out, n, color_word);
    return;
#endif
    for (; i < n; i++) {
        out[i] = color_word;
    }
}

static void engine2d_copy_into(int64_t* out, const int64_t* src, int64_t n) {
    int64_t i = 0;
#if defined(__aarch64__) || defined(_M_ARM64)
    if (n >= 2) engine2d_record_simd_row_hit();
    for (; i + 2 <= n; i += 2) {
        uint64x2_t v = vld1q_u64((const uint64_t*)(const void*)(src + i));
        vst1q_u64((uint64_t*)(void*)(out + i), v);
    }
#elif defined(__x86_64__) || defined(_M_X64)
    memmove(out, src, (size_t)n * sizeof(int64_t));
    return;
#elif defined(__riscv) && defined(__riscv_vector)
    engine2d_copy_u32_rvv(out, src, n);
    return;
#endif
    for (; i < n; i++) {
        out[i] = src[i];
    }
}

/* src-over blend of a single packed pixel, exact integer floor formula. */
static inline int64_t engine2d_blend_pixel(int64_t s, int64_t d) {
    uint32_t sp = (uint32_t)(uint64_t)s;
    uint32_t dp = (uint32_t)(uint64_t)d;
    uint32_t sa = (sp >> 24) & 0xFFu;
    if (sa == 255u) return (int64_t)(uint64_t)sp;
    if (sa == 0u) return (int64_t)(uint64_t)dp;
    uint32_t da = (dp >> 24) & 0xFFu;
    uint32_t inv = 255u - sa;
    uint32_t dst_weight = (da * inv) / 255u;
    uint32_t out_a = sa + dst_weight;
    uint32_t r = (((sp >> 16) & 0xFFu) * sa + ((dp >> 16) & 0xFFu) * dst_weight) / out_a;
    uint32_t g = (((sp >> 8) & 0xFFu) * sa + ((dp >> 8) & 0xFFu) * dst_weight) / out_a;
    uint32_t b = ((sp & 0xFFu) * sa + (dp & 0xFFu) * dst_weight) / out_a;
    uint32_t out = (out_a << 24) | (r << 16) | (g << 8) | b;
    return (int64_t)(uint64_t)out;
}

#if defined(__x86_64__) || defined(_M_X64)
static uint32_t engine2d_blend_sse2_pixel(uint32_t s, uint32_t d) {
    uint32_t sa = (s >> 24) & 0xFFu;
    uint32_t da = (d >> 24) & 0xFFu;
    uint32_t dw = (da * (255u - sa)) / 255u;
    uint32_t oa = sa + dw;
    uint32_t denom = oa == 0u ? 1u : oa;
    __m128i channels = _mm_set_epi16(0, 0,
        (short)(d & 0xFFu), (short)(s & 0xFFu),
        (short)((d >> 8) & 0xFFu), (short)((s >> 8) & 0xFFu),
        (short)((d >> 16) & 0xFFu), (short)((s >> 16) & 0xFFu));
    __m128i weights = _mm_set_epi16(0, 0,
        (short)dw, (short)sa, (short)dw, (short)sa, (short)dw, (short)sa);
    uint32_t acc[4];
    _mm_storeu_si128((__m128i*)(void*)acc, _mm_madd_epi16(channels, weights));
    uint32_t out = (oa << 24) | ((acc[0] / denom) << 16) |
        ((acc[1] / denom) << 8) | (acc[2] / denom);
    if (sa == 255u) return s;
    if (sa == 0u) return d;
    return out;
}

static void engine2d_blend_into_sse2(int64_t* out, const int64_t* dst,
                                     const int64_t* src, int64_t n) {
    for (int64_t i = 0; i < n; i++) {
        uint32_t s = (uint32_t)(uint64_t)src[i];
        uint32_t d = (uint32_t)(uint64_t)dst[i];
        out[i] = (int64_t)(uint64_t)engine2d_blend_sse2_pixel(s, d);
    }
}

SIMPLE_RUNTIME_TARGET_AVX2
static void engine2d_blend_into_avx2(int64_t* out, const int64_t* dst,
                                     const int64_t* src, int64_t n) {
    int64_t i = 0;
    for (; i + 2 <= n; i += 2) {
        uint32_t s0 = (uint32_t)(uint64_t)src[i];
        uint32_t d0 = (uint32_t)(uint64_t)dst[i];
        uint32_t s1 = (uint32_t)(uint64_t)src[i + 1];
        uint32_t d1 = (uint32_t)(uint64_t)dst[i + 1];
        uint32_t sa0 = (s0 >> 24) & 0xFFu;
        uint32_t sa1 = (s1 >> 24) & 0xFFu;
        uint32_t dw0 = (((d0 >> 24) & 0xFFu) * (255u - sa0)) / 255u;
        uint32_t dw1 = (((d1 >> 24) & 0xFFu) * (255u - sa1)) / 255u;
        uint32_t oa0 = sa0 + dw0;
        uint32_t oa1 = sa1 + dw1;
        uint32_t denom0 = oa0 == 0u ? 1u : oa0;
        uint32_t denom1 = oa1 == 0u ? 1u : oa1;
        __m256i channels = _mm256_set_epi16(0, 0,
            (short)(d1 & 0xFFu), (short)(s1 & 0xFFu),
            (short)((d1 >> 8) & 0xFFu), (short)((s1 >> 8) & 0xFFu),
            (short)((d1 >> 16) & 0xFFu), (short)((s1 >> 16) & 0xFFu),
            0, 0,
            (short)(d0 & 0xFFu), (short)(s0 & 0xFFu),
            (short)((d0 >> 8) & 0xFFu), (short)((s0 >> 8) & 0xFFu),
            (short)((d0 >> 16) & 0xFFu), (short)((s0 >> 16) & 0xFFu));
        __m256i weights = _mm256_set_epi16(0, 0,
            (short)dw1, (short)sa1, (short)dw1, (short)sa1, (short)dw1, (short)sa1,
            0, 0,
            (short)dw0, (short)sa0, (short)dw0, (short)sa0, (short)dw0, (short)sa0);
        uint32_t acc[8];
        _mm256_storeu_si256((__m256i*)(void*)acc, _mm256_madd_epi16(channels, weights));
        uint32_t o0 = (oa0 << 24) | ((acc[0] / denom0) << 16) |
            ((acc[1] / denom0) << 8) | (acc[2] / denom0);
        uint32_t o1 = (oa1 << 24) | ((acc[4] / denom1) << 16) |
            ((acc[5] / denom1) << 8) | (acc[6] / denom1);
        out[i] = (int64_t)(uint64_t)(sa0 == 255u ? s0 : (sa0 == 0u ? d0 : o0));
        out[i + 1] = (int64_t)(uint64_t)(sa1 == 255u ? s1 : (sa1 == 0u ? d1 : o1));
    }
    for (; i < n; i++) {
        uint32_t s = (uint32_t)(uint64_t)src[i];
        uint32_t d = (uint32_t)(uint64_t)dst[i];
        out[i] = (int64_t)(uint64_t)engine2d_blend_sse2_pixel(s, d);
    }
}
#endif

static void engine2d_blend_into(int64_t* out, const int64_t* dst,
                                const int64_t* src, int64_t n) {
#if defined(__aarch64__) || defined(_M_ARM64)
    int64_t i = 0;
    if (n >= 2) engine2d_record_simd_row_hit();
    for (; i + 2 <= n; i += 2) {
        /* Vectorize the per-channel multiply-accumulate for both pixels.
           u32 lanes suffice: max accumulator is 255*255*2 = 130050 < 2^32.
           The destination-alpha weight and final unpremultiply are scalar to
           stay bit-exact with C truncating division. The sa==0 / sa==255 lanes are patched
           afterward (sa==0 must return dst's FULL pixel incl. its alpha). */
        uint32_t s0 = (uint32_t)(uint64_t)src[i];
        uint32_t d0 = (uint32_t)(uint64_t)dst[i];
        uint32_t s1 = (uint32_t)(uint64_t)src[i + 1];
        uint32_t d1 = (uint32_t)(uint64_t)dst[i + 1];
        uint32_t sa0 = (s0 >> 24) & 0xFFu;
        uint32_t sa1 = (s1 >> 24) & 0xFFu;
        uint32_t da0 = (d0 >> 24) & 0xFFu;
        uint32_t da1 = (d1 >> 24) & 0xFFu;
        uint32_t dw0 = (da0 * (255u - sa0)) / 255u;
        uint32_t dw1 = (da1 * (255u - sa1)) / 255u;
        uint32_t oa0 = sa0 + dw0;
        uint32_t oa1 = sa1 + dw1;
        uint32_t denom0 = oa0 == 0u ? 1u : oa0;
        uint32_t denom1 = oa1 == 0u ? 1u : oa1;

        /* lane-0 channels in low half, lane-1 in high half: [r0 g0 b0 r1 g1 b1] */
        /* src channels (R,G,B) for both pixels */
        uint32x4_t src_rgb0 = { (s0 >> 16) & 0xFFu, (s0 >> 8) & 0xFFu, s0 & 0xFFu, 0 };
        uint32x4_t dst_rgb0 = { (d0 >> 16) & 0xFFu, (d0 >> 8) & 0xFFu, d0 & 0xFFu, 0 };
        uint32x4_t src_rgb1 = { (s1 >> 16) & 0xFFu, (s1 >> 8) & 0xFFu, s1 & 0xFFu, 0 };
        uint32x4_t dst_rgb1 = { (d1 >> 16) & 0xFFu, (d1 >> 8) & 0xFFu, d1 & 0xFFu, 0 };

        uint32x4_t sav0 = vdupq_n_u32(sa0);
        uint32x4_t invv0 = vdupq_n_u32(dw0);
        uint32x4_t sav1 = vdupq_n_u32(sa1);
        uint32x4_t invv1 = vdupq_n_u32(dw1);

        uint32x4_t acc0 = vmlaq_u32(vmulq_u32(src_rgb0, sav0), dst_rgb0, invv0);
        uint32x4_t acc1 = vmlaq_u32(vmulq_u32(src_rgb1, sav1), dst_rgb1, invv1);

        uint32_t a0[4], a1[4];
        vst1q_u32(a0, acc0);
        vst1q_u32(a1, acc1);

        uint32_t r0 = a0[0] / denom0, g0 = a0[1] / denom0, b0 = a0[2] / denom0;
        uint32_t r1 = a1[0] / denom1, g1 = a1[1] / denom1, b1 = a1[2] / denom1;
        uint32_t o0 = (oa0 << 24) | (r0 << 16) | (g0 << 8) | b0;
        uint32_t o1 = (oa1 << 24) | (r1 << 16) | (g1 << 8) | b1;
        if (sa0 == 255u) o0 = s0; else if (sa0 == 0u) o0 = d0;
        if (sa1 == 255u) o1 = s1; else if (sa1 == 0u) o1 = d1;
        out[i] = (int64_t)(uint64_t)o0;
        out[i + 1] = (int64_t)(uint64_t)o1;
    }
    for (; i < n; i++) {
        out[i] = engine2d_blend_pixel(src[i], dst[i]);
    }
#elif defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        if (n > 0) engine2d_record_simd_row_hit();
        engine2d_blend_into_avx2(out, dst, src, n);
        return;
    }
    if (n > 0) engine2d_record_simd_row_hit();
    engine2d_blend_into_sse2(out, dst, src, n);
    return;
#else
    for (int64_t i = 0; i < n; i++) {
        out[i] = engine2d_blend_pixel(src[i], dst[i]);
    }
#endif
}

static SplArray* engine2d_new_pixel_array(int64_t n) {
    if (n < 0) n = 0;
    SplArray* a = rt_array_new_uninit(n);
    if (!a) return NULL;
    rt_array_set_len_known(rt_array_header_ptr(a), n);
    return a;
}

typedef struct Engine2dFillChunk {
    int64_t* out;
    int64_t width;
    int64_t begin_row;
    int64_t end_row;
    int64_t color;
} Engine2dFillChunk;

static void engine2d_partition_rows(int64_t rows, int64_t workers, int64_t index,
                                    int64_t* begin, int64_t* end) {
    int64_t quotient = rows / workers;
    int64_t remainder = rows % workers;
    *begin = index * quotient + (index < remainder ? index : remainder);
    *end = *begin + quotient + (index < remainder ? 1 : 0);
}

static void engine2d_fill_chunk(const Engine2dFillChunk* chunk) {
    int64_t offset = chunk->begin_row * chunk->width;
    int64_t count = (chunk->end_row - chunk->begin_row) * chunk->width;
    engine2d_fill_into(chunk->out + offset, count, chunk->color);
}

#if defined(_WIN32) || defined(_WIN64)
static DWORD WINAPI engine2d_fill_worker(LPVOID arg) {
    engine2d_fill_chunk((const Engine2dFillChunk*)arg);
    return 0;
}
#else
static void* engine2d_fill_worker(void* arg) {
    engine2d_fill_chunk((const Engine2dFillChunk*)arg);
    return NULL;
}
#endif

SplArray* rt_engine2d_simd_fill_row_u32(int64_t count, int64_t color) {
    int64_t n = count;
    int64_t color_word = engine2d_box_pixel((uint32_t)color);
    SplArray* a = engine2d_new_pixel_array(n);
    if (!a) return NULL;
    if (n <= 0) return a;
    int64_t* out = (int64_t*)(uintptr_t)rt_array_data_ptr(a);
    if (!out) return a;
    engine2d_fill_into(out, n, color_word);
    return a;
}

SplArray* rt_engine2d_simd_fill_rows_u32(int64_t width, int64_t height,
                                         int64_t color, int64_t worker_limit) {
    if (width <= 0 || height <= 0) return engine2d_new_pixel_array(0);
    if (width > INT64_MAX / height) return NULL;

    int64_t total = width * height;
    SplArray* a = engine2d_new_pixel_array(total);
    if (!a) return NULL;

    int64_t* out = (int64_t*)(uintptr_t)rt_array_data_ptr(a);
    if (!out) return a;

    int64_t workers = worker_limit < 1 ? 1 : worker_limit;
    if (workers > height) workers = height;
    if (workers > 8) workers = 8;

    Engine2dFillChunk chunks[8];
    for (int64_t i = 0; i < workers; i++) {
        chunks[i].out = out;
        chunks[i].width = width;
        chunks[i].color = engine2d_box_pixel((uint32_t)color);
        engine2d_partition_rows(height, workers, i,
                                &chunks[i].begin_row, &chunks[i].end_row);
    }

    int64_t thread_count = workers - 1;
    unsigned char created[7] = {0};
#if defined(_WIN32) || defined(_WIN64)
    HANDLE threads[7];
#else
    pthread_t threads[7];
#endif
    for (int64_t i = 1; i < workers; i++) {
#if defined(_WIN32) || defined(_WIN64)
        threads[i - 1] = CreateThread(NULL, 0, engine2d_fill_worker,
                                      &chunks[i], 0, NULL);
        if (threads[i - 1]) {
            created[i - 1] = 1;
        } else {
            engine2d_fill_chunk(&chunks[i]);
        }
#else
        if (pthread_create(&threads[i - 1], NULL, engine2d_fill_worker,
                           &chunks[i]) == 0) {
            created[i - 1] = 1;
        } else {
            engine2d_fill_chunk(&chunks[i]);
        }
#endif
    }

    engine2d_fill_chunk(&chunks[0]);

    for (int64_t i = 0; i < thread_count; i++) {
        if (!created[i]) continue;
#if defined(_WIN32) || defined(_WIN64)
        if (WaitForSingleObject(threads[i], INFINITE) != WAIT_OBJECT_0) abort();
        CloseHandle(threads[i]);
#else
        if (pthread_join(threads[i], NULL) != 0) abort();
#endif
    }
    return a;
}

SplArray* rt_engine2d_simd_copy_row_u32(SplArray* src) {
    int64_t n = rt_array_len(src);
    SplArray* a = engine2d_new_pixel_array(n);
    if (!a) return NULL;
    if (n <= 0) return a;
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    int64_t* out = (int64_t*)(uintptr_t)rt_array_data_ptr(a);
    if (!out || !src_data) return a;
    engine2d_copy_into(out, src_data, n);
    return a;
}

SplArray* rt_engine2d_simd_blend_row_u32(SplArray* dst, SplArray* src) {
    int64_t dn = rt_array_len(dst);
    int64_t sn = rt_array_len(src);
    int64_t n = dn < sn ? dn : sn;
    SplArray* a = engine2d_new_pixel_array(n);
    if (!a) return NULL;
    if (n <= 0) return a;
    const int64_t* dst_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    int64_t* out = (int64_t*)(uintptr_t)rt_array_data_ptr(a);
    if (!out || !dst_data || !src_data) return a;
    if ((uint64_t)n <= SIZE_MAX / sizeof(int64_t)) {
        int64_t* raw_dst = (int64_t*)malloc((size_t)n * sizeof(int64_t));
        int64_t* raw_src = (int64_t*)malloc((size_t)n * sizeof(int64_t));
        if (raw_dst && raw_src) {
            for (int64_t i = 0; i < n; i++) {
                raw_dst[i] = engine2d_unbox_pixel(dst_data[i]);
                raw_src[i] = engine2d_unbox_pixel(src_data[i]);
            }
            engine2d_blend_into(raw_dst, raw_dst, raw_src, n);
            for (int64_t i = 0; i < n; i++) {
                out[i] = engine2d_box_pixel((uint32_t)raw_dst[i]);
            }
            free(raw_src);
            free(raw_dst);
            return a;
        }
        free(raw_src);
        free(raw_dst);
    }
    for (int64_t i = 0; i < n; i++) {
        uint32_t dst_pixel = engine2d_unbox_pixel(dst_data[i]);
        uint32_t src_pixel = engine2d_unbox_pixel(src_data[i]);
        out[i] = engine2d_box_pixel((uint32_t)engine2d_blend_pixel(src_pixel, dst_pixel));
    }
    return a;
}

#if defined(__x86_64__) || defined(_M_X64)
static void engine2d_fill_u32_sse2(int64_t* data, int64_t count, int64_t color) {
    __m128i v = _mm_set_epi64x(color, color);
    int64_t i = 0;
    if (count >= 2) engine2d_record_simd_row_hit();
    for (; i + 2 <= count; i += 2) {
        _mm_storeu_si128((__m128i*)(void*)(data + i), v);
    }
    for (; i < count; i++) {
        data[i] = color;
    }
}

SIMPLE_RUNTIME_TARGET_AVX2
static void engine2d_fill_u32_avx2(int64_t* data, int64_t count, int64_t color) {
    __m256i v = _mm256_set1_epi64x(color);
    int64_t i = 0;
    if (count >= 4) engine2d_record_simd_row_hit();
    for (; i + 4 <= count; i += 4) {
        _mm256_storeu_si256((__m256i*)(void*)(data + i), v);
    }
    for (; i < count; i++) {
        data[i] = color;
    }
}

#endif

#if defined(__riscv) && defined(__riscv_vector)
static void engine2d_fill_u32_rvv(int64_t* data, int64_t count, int64_t color) {
    engine2d_record_simd_row_hit();
    int64_t i = 0;
    while (i < count) {
        size_t vl = __riscv_vsetvl_e64m1((size_t)(count - i));
        vint64m1_t v = __riscv_vmv_v_x_i64m1(color, vl);
        __riscv_vse64_v_i64m1(data + i, v, vl);
        i += (int64_t)vl;
    }
}

static void engine2d_copy_u32_rvv(int64_t* dst, const int64_t* src, int64_t count) {
    engine2d_record_simd_row_hit();
    int64_t i = 0;
    while (i < count) {
        size_t vl = __riscv_vsetvl_e64m1((size_t)(count - i));
        vint64m1_t v = __riscv_vle64_v_i64m1(src + i, vl);
        __riscv_vse64_v_i64m1(dst + i, v, vl);
        i += (int64_t)vl;
    }
}
#endif

int64_t rt_engine2d_simd_fill_u32(SplArray* dst, int64_t offset, int64_t count, int64_t color) {
    int64_t off = 0;
    int64_t n = 0;
    if (!engine2d_span_bounds(dst, offset, count, &off, &n)) return 0;

    int64_t* data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    if (!data) return 0;
    int64_t color_word = engine2d_box_pixel((uint32_t)color);

#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_fill_u32_avx2(data + off, n, color_word);
        return n;
    }
    engine2d_fill_u32_sse2(data + off, n, color_word);
    return n;
#elif defined(__riscv) && defined(__riscv_vector)
    engine2d_fill_u32_rvv(data + off, n, color_word);
    return n;
#elif defined(__aarch64__) || defined(_M_ARM64)
    engine2d_fill_into(data + off, n, color_word);
    return n;
#endif

    for (int64_t i = 0; i < n; i++) {
        data[off + i] = color_word;
    }
    return n;
}

SplArray* rt_engine2d_simd_fill_span_u32(SplArray* dst, int64_t offset,
                                         int64_t count, int64_t color) {
    rt_engine2d_simd_fill_u32(dst, offset, count, color);
    return dst;
}

int64_t rt_engine2d_simd_copy_u32(SplArray* dst, int64_t dst_off, SplArray* src,
                                  int64_t src_off, int64_t count) {
    int64_t d_off = 0;
    int64_t n = 0;
    if (!engine2d_span_bounds(dst, dst_off, count, &d_off, &n)) return 0;

    int64_t s_off = 0;
    int64_t src_n = 0;
    if (!engine2d_span_bounds(src, src_off, n, &s_off, &src_n)) return 0;
    if (src_n < n) n = src_n;

    int64_t* dst_data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    if (!dst_data || !src_data || n <= 0) return 0;

    const int64_t* src_start = src_data + s_off;
    int64_t* dst_start = dst_data + d_off;
    if (dst_data == src_data && dst_start < src_start + n && src_start < dst_start + n) {
        memmove(dst_start, src_start, (size_t)n * sizeof(int64_t));
        return n;
    }

#if defined(__x86_64__) || defined(_M_X64)
    memmove(dst_start, src_start, (size_t)n * sizeof(int64_t));
    return n;
#elif defined(__riscv) && defined(__riscv_vector)
    engine2d_copy_u32_rvv(dst_start, src_start, n);
    return n;
#elif defined(__aarch64__) || defined(_M_ARM64)
    engine2d_copy_into(dst_start, src_start, n);
    return n;
#endif

    memmove(dst_start, src_start, (size_t)n * sizeof(int64_t));
    return n;
}

SplArray* rt_engine2d_simd_copy_span_u32(SplArray* dst, int64_t dst_off,
                                         SplArray* src, int64_t src_off,
                                         int64_t count) {
    rt_engine2d_simd_copy_u32(dst, dst_off, src, src_off, count);
    return dst;
}

/* Classify four boxed pixels and copy an opaque block in the same vector load.
 * Return 1 for copied opaque, 2 for transparent no-op, 0 for mixed alpha. */
#if defined(__x86_64__) || defined(_M_X64)
static int engine2d_classify_copy_block4_sse2(int64_t* dst,
                                               const int64_t* src) {
    const uint64_t alpha_mask = 0x7F8000000ull;
    const uint64_t a0 = (uint64_t)src[0] & alpha_mask;
    const uint64_t a1 = (uint64_t)src[1] & alpha_mask;
    const uint64_t a2 = (uint64_t)src[2] & alpha_mask;
    const uint64_t a3 = (uint64_t)src[3] & alpha_mask;
    __m128i lo = _mm_loadu_si128((const __m128i*)(const void*)src);
    __m128i hi = _mm_loadu_si128((const __m128i*)(const void*)(src + 2));
    if (a0 == alpha_mask && a1 == alpha_mask &&
        a2 == alpha_mask && a3 == alpha_mask) {
        _mm_storeu_si128((__m128i*)(void*)dst, lo);
        _mm_storeu_si128((__m128i*)(void*)(dst + 2), hi);
        return 1;
    }
    if ((a0 | a1 | a2 | a3) == 0)
        return 2;
    return 0;
}

SIMPLE_RUNTIME_TARGET_AVX2
static int engine2d_classify_copy_block4_avx2(int64_t* dst,
                                               const int64_t* src) {
    const __m256i alpha_mask = _mm256_set1_epi64x((int64_t)0x7F8000000ull);
    __m256i pixels = _mm256_loadu_si256((const __m256i*)(const void*)src);
    __m256i alpha = _mm256_and_si256(pixels, alpha_mask);
    if (_mm256_movemask_pd(_mm256_castsi256_pd(
            _mm256_cmpeq_epi64(alpha, alpha_mask))) == 0xF) {
        _mm256_storeu_si256((__m256i*)(void*)dst, pixels);
        return 1;
    }
    if (_mm256_movemask_pd(_mm256_castsi256_pd(
            _mm256_cmpeq_epi64(alpha, _mm256_setzero_si256()))) == 0xF)
        return 2;
    return 0;
}
#endif

static int engine2d_classify_copy_block4(int64_t* dst, const int64_t* src,
                                         int x86_use_avx2) {
#if defined(__x86_64__) || defined(_M_X64)
    return x86_use_avx2 ?
        engine2d_classify_copy_block4_avx2(dst, src) :
        engine2d_classify_copy_block4_sse2(dst, src);
#elif defined(__aarch64__) || defined(_M_ARM64)
    uint64x2_t lo = vld1q_u64((const uint64_t*)(const void*)src);
    uint64x2_t hi = vld1q_u64((const uint64_t*)(const void*)(src + 2));
    uint64x2_t mask = vdupq_n_u64(0x7F8000000ull);
    uint64x2_t alo = vandq_u64(lo, mask);
    uint64x2_t ahi = vandq_u64(hi, mask);
    uint64x2_t olo = vceqq_u64(alo, mask);
    uint64x2_t ohi = vceqq_u64(ahi, mask);
    if (vgetq_lane_u64(olo, 0) == UINT64_MAX &&
        vgetq_lane_u64(olo, 1) == UINT64_MAX &&
        vgetq_lane_u64(ohi, 0) == UINT64_MAX &&
        vgetq_lane_u64(ohi, 1) == UINT64_MAX) {
        vst1q_u64((uint64_t*)(void*)dst, lo);
        vst1q_u64((uint64_t*)(void*)(dst + 2), hi);
        return 1;
    }
    if ((vgetq_lane_u64(alo, 0) | vgetq_lane_u64(alo, 1) |
         vgetq_lane_u64(ahi, 0) | vgetq_lane_u64(ahi, 1)) == 0)
        return 2;
#elif defined(__riscv) && defined(__riscv_vector)
    uint32_t a0 = engine2d_unbox_pixel(src[0]) >> 24;
    uint32_t a1 = engine2d_unbox_pixel(src[1]) >> 24;
    uint32_t a2 = engine2d_unbox_pixel(src[2]) >> 24;
    uint32_t a3 = engine2d_unbox_pixel(src[3]) >> 24;
    if ((a0 & a1 & a2 & a3) == 255u) {
        int64_t copied = 0;
        while (copied < 4) {
            size_t vl = __riscv_vsetvl_e64m1((size_t)(4 - copied));
            if (vl == 0) return 0;
            vint64m1_t pixels = __riscv_vle64_v_i64m1(src + copied, vl);
            __riscv_vse64_v_i64m1(dst + copied, pixels, vl);
            copied += (int64_t)vl;
        }
        return 1;
    }
#endif
    (void)dst;
    (void)src;
    return 0;
}

/* The public span ABI stores tagged pixels. Constant-colour blocks can still
 * amortize unbox/re-box overhead, but the equivalent mixed-source bridge is
 * intentionally absent: the current four-pixel scratch route measures slower
 * than the exact scalar body and therefore does not earn production dispatch. */
#if defined(__x86_64__) || defined(_M_X64)
static void engine2d_blend_boxed_const_block4_x86(int64_t* dst,
                                                   uint32_t src,
                                                   int use_avx2) {
    int64_t raw_dst[4];
    const int64_t raw_src[4] = { (int64_t)src, (int64_t)src,
                                 (int64_t)src, (int64_t)src };
    for (int64_t lane = 0; lane < 4; lane++) {
        raw_dst[lane] = (int64_t)engine2d_unbox_pixel(dst[lane]);
    }
    if (use_avx2) {
        engine2d_blend_into_avx2(raw_dst, raw_dst, raw_src, 4);
    } else {
        engine2d_blend_into_sse2(raw_dst, raw_dst, raw_src, 4);
    }
    for (int64_t lane = 0; lane < 4; lane++) {
        dst[lane] = engine2d_box_pixel((uint32_t)raw_dst[lane]);
    }
}
#endif

/* Blend src[src_off..src_off+n) over dst[dst_off..dst_off+n) in place,
 * straight-alpha src-over (oracle_src_over). No malloc — matches
 * fill_span/copy_span's in-place convention, not blend_row's
 * malloc-two-scratch-buffers convention. */
SplArray* rt_engine2d_simd_blend_span_u32(SplArray* dst, int64_t dst_off,
                                          SplArray* src, int64_t src_off,
                                          int64_t count) {
    int64_t d_off = 0, n = 0;
    if (!engine2d_span_bounds(dst, dst_off, count, &d_off, &n)) return dst;
    int64_t s_off = 0, sn = 0;
    if (!engine2d_span_bounds(src, src_off, n, &s_off, &sn)) return dst;
    if (sn < n) n = sn;
    int64_t* dst_data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    const int64_t* src_data = (const int64_t*)(uintptr_t)rt_array_data_ptr(src);
    if (!dst_data || !src_data) return dst;
    int64_t* dst_start = dst_data + d_off;
    const int64_t* src_start = src_data + s_off;
    int overlaps = (dst_data == src_data && dst_start < src_start + n &&
                    src_start < dst_start + n);
    int vector_classify_available = 0;
    int x86_use_avx2 = 0;
#if defined(__x86_64__) || defined(_M_X64)
    /* x86-64 guarantees SSE2. AVX2 remains separately runtime-dispatched. */
    vector_classify_available = 1;
    x86_use_avx2 = simd_detect_avx2();
#elif defined(__aarch64__) || defined(_M_ARM64)
    vector_classify_available = 1;
#elif defined(__riscv) && defined(__riscv_vector)
    vector_classify_available = rt_simd_has_rvv();
#endif
    int64_t i = 0;
    if (!overlaps) {
        for (; i + 4 <= n; i += 4) {
            const uint64_t first_alpha =
                (uint64_t)src_start[i] & 0x7F8000000ull;
            int block_kind = (vector_classify_available &&
                              (first_alpha == 0 ||
                               first_alpha == 0x7F8000000ull)) ?
                engine2d_classify_copy_block4(
                    dst_start + i, src_start + i, x86_use_avx2) : 0;
            if (block_kind != 0) {
                engine2d_record_simd_row_hit();
                continue;
            }
            uint32_t s0 = engine2d_unbox_pixel(src_start[i]);
            uint32_t s1 = engine2d_unbox_pixel(src_start[i + 1]);
            uint32_t s2 = engine2d_unbox_pixel(src_start[i + 2]);
            uint32_t s3 = engine2d_unbox_pixel(src_start[i + 3]);
            uint32_t d0 = engine2d_unbox_pixel(dst_start[i]);
            uint32_t d1 = engine2d_unbox_pixel(dst_start[i + 1]);
            uint32_t d2 = engine2d_unbox_pixel(dst_start[i + 2]);
            uint32_t d3 = engine2d_unbox_pixel(dst_start[i + 3]);
            dst_start[i] = engine2d_box_pixel(
                (uint32_t)engine2d_blend_pixel((int64_t)s0, (int64_t)d0));
            dst_start[i + 1] = engine2d_box_pixel(
                (uint32_t)engine2d_blend_pixel((int64_t)s1, (int64_t)d1));
            dst_start[i + 2] = engine2d_box_pixel(
                (uint32_t)engine2d_blend_pixel((int64_t)s2, (int64_t)d2));
            dst_start[i + 3] = engine2d_box_pixel(
                (uint32_t)engine2d_blend_pixel((int64_t)s3, (int64_t)d3));
        }
    }
    for (; i < n; i++) {
        uint32_t s = engine2d_unbox_pixel(src_data[s_off + i]);
        uint32_t d = engine2d_unbox_pixel(dst_data[d_off + i]);
        dst_data[d_off + i] = engine2d_box_pixel((uint32_t)engine2d_blend_pixel((int64_t)s, (int64_t)d));
    }
    return dst;
}

/* Blend one constant colour over dst[offset..offset+count) in place,
 * straight-alpha src-over (oracle_src_over_const). No src array, no malloc. */
SplArray* rt_engine2d_simd_blend_const_span_u32(SplArray* dst, int64_t offset,
                                                int64_t count, int64_t const_color) {
    int64_t off = 0, n = 0;
    if (!engine2d_span_bounds(dst, offset, count, &off, &n)) return dst;
    int64_t* dst_data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    if (!dst_data) return dst;
    uint32_t s = (uint32_t)(uint64_t)const_color;
    uint32_t sa = (s >> 24) & 0xFFu;
    if (sa == 0u) return dst;
    if (sa == 255u) {
        rt_engine2d_simd_fill_u32(dst, offset, n, const_color);
        return dst;
    }
    int64_t i = 0;
#if defined(__x86_64__) || defined(_M_X64)
    const int use_avx2 = simd_detect_avx2();
    int used_vector_blend = 0;
    for (; i + 4 <= n; i += 4) {
        engine2d_blend_boxed_const_block4_x86(dst_data + off + i, s,
                                               use_avx2);
        used_vector_blend = 1;
    }
    if (used_vector_blend) engine2d_record_simd_row_hit();
#endif
    for (; i < n; i++) {
        uint32_t d = engine2d_unbox_pixel(dst_data[off + i]);
        dst_data[off + i] = engine2d_box_pixel((uint32_t)engine2d_blend_pixel((int64_t)s, (int64_t)d));
    }
    return dst;
}

/* Scalar fallback stubs — no-op placeholders until pure Simple or
   hardware-accelerated implementations are wired in. */

static void scalar_aes_encrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_aes_decrypt_block(const uint8_t* in, uint8_t* out,
                                     const uint8_t* round_keys, int rounds) {
    (void)in; (void)out; (void)round_keys; (void)rounds;
}

static void scalar_sha256_compress(uint32_t state[8], const uint8_t* block) {
    (void)state; (void)block;
}

static void scalar_chacha20_block(uint32_t out[16], const uint32_t in[16]) {
    (void)out; (void)in;
}

static uint32_t scalar_crc32_update(uint32_t crc, const uint8_t* data, uint64_t len) {
    (void)data; (void)len;
    return crc;
}

static void scalar_ghash_multiply(uint8_t* result, const uint8_t* h, const uint8_t* x) {
    (void)result; (void)h; (void)x;
}

SimdCryptoDispatch g_simd_crypto = {
    .aes_encrypt_block = scalar_aes_encrypt_block,
    .aes_decrypt_block = scalar_aes_decrypt_block,
    .sha256_compress   = scalar_sha256_compress,
    .chacha20_block    = scalar_chacha20_block,
    .crc32_update      = scalar_crc32_update,
    .ghash_multiply    = scalar_ghash_multiply,
};

void simd_crypto_init(void) {
    /* Detect hardware crypto extensions and upgrade function pointers.
       AES-NI, SHA-NI, and PCLMULQDQ implementations will be added as
       separate TUs (runtime_simd_aesni.c, runtime_simd_shani.c, etc.)
       and wired in here when available. */
}

#endif
