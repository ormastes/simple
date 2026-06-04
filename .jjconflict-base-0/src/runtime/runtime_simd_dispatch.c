/*
 * SIMD Dispatch — compilation unit for dispatch table support.
 * The text dispatch table (g_simd_text) and init are in runtime_simd_utf8.c.
 * The crypto dispatch table (g_simd_crypto) is defined here with scalar stubs.
 */
#include "runtime_simd_dispatch.h"
#include "runtime.h"

#include <stdlib.h>

#if defined(__x86_64__) || defined(_M_X64)
#  include <immintrin.h>
#endif

#if !defined(_WIN32)
#  include <dlfcn.h>
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

bool rt_opencl_write_buffer(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size) {
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
    return fns->enqueue_write_buffer(
        wrapped_queue->queue,
        wrapped_buffer->mem,
        RT_OPENCL_TRUE,
        0,
        (size_t)size,
        (const void*)(intptr_t)host_ptr,
        0,
        NULL,
        NULL
    ) == RT_OPENCL_SUCCESS;
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

static inline int64_t engine2d_numeric_arg(int64_t value) {
    uint64_t raw = (uint64_t)value;
    if ((raw & RT_VALUE_TAG_MASK_SIMD) == 0 && raw >= 8) {
        return (int64_t)(raw >> 3);
    }
    return value;
}

static int engine2d_span_bounds(SplArray* array, int64_t offset, int64_t count,
                                int64_t* out_offset, int64_t* out_count) {
    if (!array || !out_offset || !out_count) return 0;
    int64_t len = rt_array_len(array);
    offset = engine2d_numeric_arg(offset);
    count = engine2d_numeric_arg(count);
    if (offset < 0 || count <= 0 || offset >= len) return 0;
    if (count > len - offset) count = len - offset;
    *out_offset = offset;
    *out_count = count;
    return count > 0;
}

#if defined(__x86_64__) || defined(_M_X64)
__attribute__((target("avx2")))
static void engine2d_fill_u32_avx2(int64_t* data, int64_t count, int64_t color) {
    __m256i v = _mm256_set1_epi64x(color);
    int64_t i = 0;
    for (; i + 4 <= count; i += 4) {
        _mm256_storeu_si256((__m256i*)(void*)(data + i), v);
    }
    for (; i < count; i++) {
        data[i] = color;
    }
}

__attribute__((target("avx2")))
static void engine2d_copy_u32_avx2(int64_t* dst, const int64_t* src, int64_t count) {
    int64_t i = 0;
    for (; i + 4 <= count; i += 4) {
        __m256i v = _mm256_loadu_si256((const __m256i*)(const void*)(src + i));
        _mm256_storeu_si256((__m256i*)(void*)(dst + i), v);
    }
    for (; i < count; i++) {
        dst[i] = src[i];
    }
}
#endif

int64_t rt_engine2d_simd_fill_u32(SplArray* dst, int64_t offset, int64_t count, int64_t color) {
    int64_t off = 0;
    int64_t n = 0;
    if (!engine2d_span_bounds(dst, offset, count, &off, &n)) return 0;

    int64_t* data = (int64_t*)(uintptr_t)rt_array_data_ptr(dst);
    if (!data) return 0;
    int64_t color_word = engine2d_numeric_arg(color) & 0xffffffffLL;

#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_fill_u32_avx2(data + off, n, color_word);
        return n;
    }
#endif

    for (int64_t i = 0; i < n; i++) {
        data[off + i] = color_word;
    }
    return n;
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

#if defined(__x86_64__) || defined(_M_X64)
    if (simd_detect_avx2()) {
        engine2d_copy_u32_avx2(dst_data + d_off, src_data + s_off, n);
        return n;
    }
#endif

    memmove(dst_data + d_off, src_data + s_off, (size_t)n * sizeof(int64_t));
    return n;
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
