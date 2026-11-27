#ifndef _WIN32
#define _POSIX_C_SOURCE 200809L
#endif
#include "simple_gpu_provider_abi_v1.h"
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <dlfcn.h>
#endif
#include <limits.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* CUDA Driver API boundary; no SDK, constructors, or driver activity in
 * query(). Format 1: LE u32 count, LE u32 reserved=0, count left u32 words,
 * count right u32 words. Count 1..16384; resource size must be exactly count*4.
 * Empty bitmaps belong to the caller's empty-result path, without submission.
 * One session/resource/completion at a time. Handles never repeat during the
 * loaded provider lifetime; the host registry supplies the unload generation. */
#define ID UINT64_C(0x43554441414e4431)
#define MAX_BYTES 65536u
#define OK SIMPLE_GPU_STATUS_OK
#define INVALID SIMPLE_GPU_STATUS_INVALID
#define BUSY SIMPLE_GPU_STATUS_BUSY
#define REJECTED SIMPLE_GPU_STATUS_REJECTED
#define UNCERTAIN SIMPLE_GPU_STATUS_UNCERTAIN
typedef uint64_t DevPtr;
struct driver_table {
    void *lib;
    int (*Init)(unsigned); int (*DeviceGetCount)(int *); int (*DeviceGet)(int *,int);
    int (*DeviceGetAttribute)(int *,int,int);
    int (*CtxCreate)(void **,unsigned,int); int (*CtxDestroy)(void *);
    int (*CtxPushCurrent)(void *); int (*CtxPopCurrent)(void **);
    int (*CtxSynchronize)(void);
    int (*ModuleLoadData)(void **,const void *); int (*ModuleUnload)(void *);
    int (*ModuleGetFunction)(void **,void *,const char *);
    int (*MemAlloc)(DevPtr *,size_t); int (*MemFree)(DevPtr);
    int (*MemcpyHtoD)(DevPtr,const void *,size_t);
    int (*MemcpyDtoH)(void *,DevPtr,size_t);
    int (*LaunchKernel)(void *,unsigned,unsigned,unsigned,unsigned,unsigned,unsigned,
                        unsigned,void *,void **,void **);
    int (*EventCreate)(void **,unsigned); int (*EventRecord)(void *,void *);
    int (*EventQuery)(void *); int (*EventElapsedTime)(float *,void *,void *);
    int (*EventDestroy)(void *);
};

/* Driver library candidates mirror cuda_driver_library_candidates() in
 * src/lib/gc_async_mut/cuda/driver_loader.spl. */
#ifdef _WIN32
#define CUDA_DRIVER_PRIMARY "nvcuda.dll"
static const char *const cuda_driver_candidates[] = {"nvcuda.dll"};
/* System32 only: never resolve the driver from the CWD or PATH (DLL planting). */
static void *lib_open(const char *path) {
    return (void *)LoadLibraryExA(path, NULL, LOAD_LIBRARY_SEARCH_SYSTEM32);
}
static void *lib_symbol(void *lib, const char *name) {
    return (void *)(uintptr_t)GetProcAddress((HMODULE)lib, name);
}
static int lib_close(void *lib) { return FreeLibrary((HMODULE)lib) ? 0 : 1; }
#else
#define CUDA_DRIVER_PRIMARY "libcuda.so.1"
static const char *const cuda_driver_candidates[] = {"libcuda.so.1", "libcuda.so"};
static void *lib_open(const char *path) { return dlopen(path, RTLD_NOW | RTLD_LOCAL); }
static void *lib_symbol(void *lib, const char *name) { return dlsym(lib, name); }
static int lib_close(void *lib) { return dlclose(lib); }
#endif

/* Resolved once and published locklessly: the first complete table wins the
 * CAS; a losing loader closes its own library handle and frees its table.
 * Until a table is published, `driver` names an empty table (no library). */
static _Atomic(struct driver_table *) driver_published;
static struct driver_table driver_unloaded;
static struct driver_table *published_driver(void) {
    return atomic_load_explicit(&driver_published, memory_order_acquire);
}
static struct driver_table *driver_view(void) {
    struct driver_table *table = published_driver();
    return table ? table : &driver_unloaded;
}
#define driver (*driver_view())

/* Named fail-closed errors (CUDA-E001/CUDA-E002), same text as the Simple
 * loader. Thread-local so concurrent loaders never share a buffer. */
static _Thread_local char driver_last_error[512];

/* Resolve every required symbol from `path`; NULL plus a named error in `err`
 * when the library or any symbol is missing (nothing is partially published). */
static struct driver_table *load_driver_table(const char *path, char *err, size_t err_size) {
    void *lib = lib_open(path);
    if (!lib) {
        snprintf(err, err_size, "CUDA-E001: CUDA driver not available: could not load any of [%s] "
                 "(install the NVIDIA driver, or run without GPU features)", path);
        return NULL;
    }
    struct driver_table *t = calloc(1, sizeof(*t));
    if (!t) {
        lib_close(lib);
        snprintf(err, err_size, "CUDA-E001: CUDA driver not available: out of memory loading %s", path);
        return NULL;
    }
    t->lib = lib;
    const char *missing = NULL;
#define LOAD(field,symbol) do { if (!missing) { *(void **)(&t->field) = lib_symbol(lib,symbol); \
        if (!t->field) missing = symbol; } } while (0)
    LOAD(Init,"cuInit"); LOAD(DeviceGetCount,"cuDeviceGetCount"); LOAD(DeviceGet,"cuDeviceGet");
    LOAD(DeviceGetAttribute,"cuDeviceGetAttribute");
    LOAD(CtxCreate,"cuCtxCreate_v2"); LOAD(CtxDestroy,"cuCtxDestroy_v2");
    LOAD(CtxPushCurrent,"cuCtxPushCurrent_v2"); LOAD(CtxPopCurrent,"cuCtxPopCurrent_v2");
    LOAD(CtxSynchronize,"cuCtxSynchronize"); LOAD(ModuleLoadData,"cuModuleLoadData");
    LOAD(ModuleUnload,"cuModuleUnload"); LOAD(ModuleGetFunction,"cuModuleGetFunction");
    LOAD(MemAlloc,"cuMemAlloc_v2"); LOAD(MemFree,"cuMemFree_v2");
    LOAD(MemcpyHtoD,"cuMemcpyHtoD_v2"); LOAD(MemcpyDtoH,"cuMemcpyDtoH_v2");
    LOAD(LaunchKernel,"cuLaunchKernel"); LOAD(EventCreate,"cuEventCreate");
    LOAD(EventRecord,"cuEventRecord"); LOAD(EventQuery,"cuEventQuery");
    LOAD(EventElapsedTime,"cuEventElapsedTime"); LOAD(EventDestroy,"cuEventDestroy_v2");
#undef LOAD
    if (missing) {
        snprintf(err, err_size, "CUDA-E002: CUDA driver %s is missing required symbol %s "
                 "(driver older than the CUDA API this build uses; update the NVIDIA driver)", path, missing);
        lib_close(lib); free(t);
        return NULL;
    }
    return t;
}

/* Named error from the last failed load on this thread; "" after success. */
__attribute__((visibility("default")))
const char *simple_cuda_provider_last_error_v1(void) { return driver_last_error; }
static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static uint64_t next_handle = 1;
static struct {
    uint64_t handle, device, resource, completion, correlation, elapsed, checksum;
    void *context, *module, *function, *start, *end;
    DevPtr output, left, right;
    uint8_t *host_output, *input;
    size_t bytes;
    int ready, submitted, context_fault;
} state;
/* The kernel uses only sm_20-level instructions. The JIT rejects a .target
 * above the device's compute capability (CUDA_ERROR_INVALID_PTX, "SM version
 * specified by .target is higher than default SM version"), and newer drivers
 * drop the oldest targets, so pick the highest tier the device supports. */
static const struct { int cc; const char *header; } ptx_tiers[] = {
    {61, ".version 6.0\n.target sm_61\n"}, {50, ".version 4.0\n.target sm_50\n"},
    {30, ".version 3.0\n.target sm_30\n"}, {20, ".version 3.0\n.target sm_20\n"},
};
static const char *ptx_header(int major, int minor) {
    int cc = major * 10 + minor;
    for (size_t i = 0; i < sizeof(ptx_tiers) / sizeof(ptx_tiers[0]); i++)
        if (cc >= ptx_tiers[i].cc) return ptx_tiers[i].header;
    return NULL;
}
static const char ptx_body[] =
".address_size 64\n.visible .entry bitmap_and(.param .u64 a,.param .u64 b,.param .u64 o,.param .u32 n) {\n.reg .pred %p; .reg .b32 %r<7>; .reg .b64 %d<8>;\nld.param.u64 %d0,[a]; ld.param.u64 %d1,[b]; ld.param.u64 %d2,[o]; ld.param.u32 %r0,[n];\nmov.u32 %r1,%ctaid.x; mov.u32 %r2,%ntid.x; mov.u32 %r3,%tid.x; mad.lo.u32 %r4,%r1,%r2,%r3; setp.ge.u32 %p,%r4,%r0; @%p bra done;\nmul.wide.u32 %d3,%r4,4; add.u64 %d4,%d0,%d3; add.u64 %d5,%d1,%d3; add.u64 %d6,%d2,%d3; ld.global.u32 %r5,[%d4]; ld.global.u32 %r6,[%d5]; and.b32 %r5,%r5,%r6; st.global.u32 [%d6],%r5;\ndone: ret; }\n";

static uint64_t new_handle(void) {
    uint64_t result = next_handle;
    if (result) next_handle = result == INT64_MAX ? 0 : result + 1;
    return result;
}
static int load_driver(void) {
    if (published_driver()) { driver_last_error[0] = '\0'; return 1; }
    char tried[256] = "";
    size_t n = sizeof(cuda_driver_candidates) / sizeof(cuda_driver_candidates[0]);
    for (size_t i = 0; i < n; i++) {
        struct driver_table *t = load_driver_table(cuda_driver_candidates[i], driver_last_error,
                                                   sizeof(driver_last_error));
        if (!t) {
            if (strncmp(driver_last_error, "CUDA-E002:", 10) == 0) return 0;
            size_t used = strlen(tried);
            snprintf(tried + used, sizeof(tried) - used, "%s%s", used ? ", " : "", cuda_driver_candidates[i]);
            continue;
        }
        struct driver_table *expected = NULL;
        if (!atomic_compare_exchange_strong_explicit(&driver_published, &expected, t,
                                                     memory_order_acq_rel, memory_order_acquire)) {
            lib_close(t->lib); free(t); /* another loader published first */
        }
        driver_last_error[0] = '\0';
        return 1;
    }
    snprintf(driver_last_error, sizeof(driver_last_error),
             "CUDA-E001: CUDA driver not available: could not load any of [%s] "
             "(install the NVIDIA driver, or run without GPU features)", tried);
    return 0;
}
static int owns_session(uint64_t session) { return session && session==state.handle; }
static int owns(uint64_t session,uint64_t handle,uint64_t current) {
    return owns_session(session) && handle && handle==current;
}
static int enter(void) {
    return !state.context_fault && !driver.CtxPushCurrent(state.context);
}
static int leave(int status) {
    void *popped = NULL;
    if (driver.CtxPopCurrent(&popped) || popped != state.context) {
        state.context_fault = 1; return UNCERTAIN;
    }
    return status;
}
/* Called only while our context is current. Never free potentially in-flight
 * storage when a drain fails. Each successful destruction clears its owner. */
static int drain_completion(void) {
    if (!state.completion) return OK;
    if (driver.CtxSynchronize()) return UNCERTAIN;
    if (state.start) { if (driver.EventDestroy(state.start)) return UNCERTAIN; state.start=NULL; }
    if (state.end) { if (driver.EventDestroy(state.end)) return UNCERTAIN; state.end=NULL; }
    if (state.left) { if (driver.MemFree(state.left)) return UNCERTAIN; state.left=0; }
    if (state.right) { if (driver.MemFree(state.right)) return UNCERTAIN; state.right=0; }
    free(state.input); state.input=NULL; state.completion=0; state.submitted=0;
    return OK;
}
static int free_resource(void) {
    if (state.output) { if (driver.MemFree(state.output)) return UNCERTAIN; state.output=0; }
    free(state.host_output); state.host_output=NULL; state.resource=0; state.bytes=0; state.ready=0;
    return OK;
}
static int close_locked(void) {
    if (!enter()) return UNCERTAIN;
    int result = drain_completion();
    if (!result) result=free_resource();
    if (!result && state.module) {
        if (driver.ModuleUnload(state.module)) result=UNCERTAIN;
        else { state.module=NULL; state.function=NULL; }
    }
    result=leave(result);
    if (result) return result;
    if (driver.CtxDestroy(state.context)) return UNCERTAIN;
    memset(&state,0,sizeof(state)); return OK;
}
/* Called with the new context current: JIT the kernel for device `dev`. */
static int load_module(int dev) {
    int major = 0, minor = 0;
    if (driver.DeviceGetAttribute(&major, 75, dev) || driver.DeviceGetAttribute(&minor, 76, dev))
        return 1; /* CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR/_MINOR */
    const char *header = ptx_header(major, minor);
    if (!header) return 1;
    char text[sizeof(ptx_body) + 64];
    snprintf(text, sizeof(text), "%s%s", header, ptx_body);
    return driver.ModuleLoadData(&state.module, text);
}
static int32_t session_open(uint64_t backend,uint64_t device,uint64_t *out) {
    if (!out) return REJECTED;
    *out=0; pthread_mutex_lock(&mutex);
    int result=REJECTED, count=0, dev=0;
    if (state.handle) goto done;
    if (backend!=SIMPLE_GPU_BACKEND_CUDA || device>INT_MAX || !next_handle) goto done;
    if (!load_driver() || driver.Init(0) || driver.DeviceGetCount(&count) ||
        device>=(uint64_t)count || driver.DeviceGet(&dev,(int)device)) goto done;
    state.handle=new_handle(); state.device=device;
    if (driver.CtxCreate(&state.context,0,dev)) {
        /* CUDA failed creation with no returned object is a definitive reject. */
        if (!state.context) { memset(&state,0,sizeof(state)); goto done; }
        *out=state.handle; result=UNCERTAIN; goto done;
    }
    *out=state.handle;
    result = load_module(dev) ||
             driver.ModuleGetFunction(&state.function,state.module,"bitmap_and") ? UNCERTAIN : OK;
    result=leave(result); /* cuCtxCreate made our context current. */
    if (result && !state.context_fault && close_locked()==OK) { *out=0; result=REJECTED; }
done:
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t with_context(int (*fn)(void)) { return enter() ? leave(fn()) : UNCERTAIN; }
static int32_t session_close(uint64_t session) {
    pthread_mutex_lock(&mutex);
    int result = !owns_session(session) ? INVALID : close_locked();
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t resource_alloc(uint64_t session,const SimpleGpuResourceDescV1 *desc,uint64_t *out) {
    if (!out) return REJECTED;
    *out=0; pthread_mutex_lock(&mutex); int result=REJECTED;
    if (!owns_session(session) || !desc || desc->struct_size!=sizeof(*desc) ||
        desc->flags || desc->usage_bits!=1 || !desc->size_bytes || desc->size_bytes>MAX_BYTES ||
        desc->size_bytes%4 || !next_handle) goto done;
    if (state.resource) goto done;
    if (!enter()) { result=UNCERTAIN; goto done; }
    state.resource=new_handle(); *out=state.resource; state.bytes=(size_t)desc->size_bytes;
    state.host_output=malloc(state.bytes);
    result=!state.host_output || driver.MemAlloc(&state.output,state.bytes) ? UNCERTAIN : OK;
    if (result && free_resource()==OK) { *out=0; result=REJECTED; }
    result=leave(result);
done:
    pthread_mutex_unlock(&mutex); return result;
}
static uint32_t load32(const uint8_t *p) {
    return (uint32_t)p[0] | (uint32_t)p[1]<<8 | (uint32_t)p[2]<<16 | (uint32_t)p[3]<<24;
}
static int32_t submit(uint64_t session,const SimpleGpuSubmitV1 *desc,uint64_t *out) {
    if (!out) return REJECTED;
    *out=0; pthread_mutex_lock(&mutex); int result=REJECTED;
    if (!owns_session(session) || !desc || desc->struct_size!=sizeof(*desc) ||
        desc->format!=1 || !desc->data || desc->length<8 || !desc->correlation_id ||
        !state.resource || desc->output_resource!=state.resource || !next_handle) goto done;
    uint32_t words=load32(desc->data);
    if (!words || words>MAX_BYTES/4 || load32(desc->data+4) ||
        desc->length!=8+(uint64_t)words*8 || state.bytes!=(size_t)words*4) goto done;
    if (state.completion) goto done;
    if (!enter()) { result=UNCERTAIN; goto done; }
    state.completion=new_handle(); *out=state.completion;
    state.ready=0; state.correlation=desc->correlation_id;
    state.input=malloc(state.bytes*2);
    result=UNCERTAIN;
    if (!state.input) goto finish;
    memcpy(state.input,desc->data+8,state.bytes*2);
    if (driver.MemAlloc(&state.left,state.bytes) || driver.MemAlloc(&state.right,state.bytes) ||
        driver.MemcpyHtoD(state.left,state.input,state.bytes) ||
        driver.MemcpyHtoD(state.right,state.input+state.bytes,state.bytes) ||
        driver.EventCreate(&state.start,0) || driver.EventCreate(&state.end,0) ||
        driver.EventRecord(state.start,NULL)) goto finish;
    void *args[]={&state.left,&state.right,&state.output,&words};
    if (driver.LaunchKernel(state.function,(words+127)/128,1,1,128,1,1,0,NULL,args,NULL) ||
        driver.EventRecord(state.end,NULL)) goto finish;
    state.submitted=1; result=OK;
finish:
    /* Even an early error owns a completion: host can synchronously drain it. */
    result=leave(result);
done:
    pthread_mutex_unlock(&mutex); return result;
}
static uint64_t now_ns(void) {
    struct timespec t; if (clock_gettime(CLOCK_MONOTONIC,&t)) return 0;
    return (uint64_t)t.tv_sec*UINT64_C(1000000000)+(uint64_t)t.tv_nsec;
}
static int32_t wait_completion(uint64_t session,uint64_t completion,uint64_t timeout,SimpleGpuReceiptV1 *receipt) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (!owns(session,completion,state.completion) ||
        !state.submitted || !timeout || !receipt || receipt->struct_size!=sizeof(*receipt)) goto done;
    if (!enter()) { result=UNCERTAIN; goto done; }
    uint64_t start=now_ns(); int rc;
    if (!start) { result=UNCERTAIN; goto finish; }
    while ((rc=driver.EventQuery(state.end))==600) {
        uint64_t now=now_ns();
        if (!now) { result=UNCERTAIN; goto finish; }
        if (now-start>=timeout) { result=SIMPLE_GPU_STATUS_TIMEOUT; goto finish; }
        struct timespec delay={0,100000}; nanosleep(&delay,NULL);
    }
    float ms=0;
    if (rc || driver.EventElapsedTime(&ms,state.start,state.end) || !(ms>0) ||
        ms>=18446744073709.0f || driver.MemcpyDtoH(state.host_output,state.output,state.bytes)) {
        result=UNCERTAIN; goto finish;
    }
    state.elapsed=(uint64_t)((double)ms*1000000.0);
    if (!state.elapsed) { result=UNCERTAIN; goto finish; }
    state.checksum=UINT64_C(14695981039346656037);
    for (size_t i=0;i<state.bytes;i++) { state.checksum^=state.host_output[i]; state.checksum*=UINT64_C(1099511628211); }
    state.ready=1;
    *receipt=(SimpleGpuReceiptV1){sizeof(*receipt),OK,state.correlation,ID,state.device,
                                 state.resource,state.checksum,state.elapsed};
    result=OK;
finish:
    result=leave(result);
done:
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t readback(uint64_t session,uint64_t resource,SimpleGpuBytesV1 *bytes) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (owns(session,resource,state.resource) &&
        state.ready && !state.context_fault && bytes && bytes->struct_size==sizeof(*bytes) &&
        !bytes->reserved && bytes->data && bytes->length>=state.bytes) {
        memcpy(bytes->data,state.host_output,state.bytes); bytes->length=state.bytes; result=OK;
    }
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t completion_release(uint64_t session,uint64_t completion) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (owns(session,completion,state.completion)) result=with_context(drain_completion);
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t resource_release(uint64_t session,uint64_t resource) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (owns(session,resource,state.resource))
        result=state.completion ? BUSY : with_context(free_resource);
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t shutdown_provider(void) {
    pthread_mutex_lock(&mutex); int result=BUSY;
    if (!state.handle) {
        result=OK;
        struct driver_table *table = atomic_exchange_explicit(&driver_published, NULL, memory_order_acq_rel);
        if (table) {
            if (table->lib && lib_close(table->lib)) result=SIMPLE_GPU_STATUS_FAILED;
            free(table);
        }
    }
    pthread_mutex_unlock(&mutex); return result;
}
/* Discovery operation reports the only accepted submission format. */
static int64_t bitmap_and_format(void) { return 1; }
static const SimpleGpuOperationV1 operations[]={bitmap_and_format};
static const SimpleGpuProviderAbiV1 api={sizeof(api),1,0,SIMPLE_GPU_BACKEND_CUDA,
    SIMPLE_GPU_CAP_DEVICE_READBACK|SIMPLE_GPU_CAP_ASYNC_COMPLETION,ID,1,0,operations,
    shutdown_provider,session_open,session_close,submit,wait_completion,readback,
    resource_alloc,resource_release,completion_release};
__attribute__((visibility("default")))
const SimpleGpuProviderAbiV1 *simple_gpu_provider_query_v1(void) { return &api; }
