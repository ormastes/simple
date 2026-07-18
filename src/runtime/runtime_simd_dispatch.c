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

#if defined(__x86_64__) || defined(_M_X64)
#  include <immintrin.h>
#endif

#if !defined(_WIN32)
#  include <dlfcn.h>
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

#if defined(__x86_64__) || defined(_M_X64)
static void engine2d_fill_u32_sse2(int64_t* data, int64_t count, int64_t color);
__attribute__((target("avx2")))
static void engine2d_fill_u32_avx2(int64_t* data, int64_t count, int64_t color);
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

static void engine2d_blend_into(int64_t* out, const int64_t* dst,
                                const int64_t* src, int64_t n) {
#if defined(__aarch64__) || defined(_M_ARM64)
    int64_t i = 0;
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

__attribute__((target("avx2")))
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
