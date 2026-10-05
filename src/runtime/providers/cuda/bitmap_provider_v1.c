#define _POSIX_C_SOURCE 200809L
#include "simple_gpu_provider_abi_v1.h"
#include <dlfcn.h>
#include <limits.h>
#include <pthread.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Linux CUDA Driver API boundary; no SDK, constructors, or driver activity in
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
static struct {
    void *lib;
    int (*Init)(unsigned); int (*DeviceGetCount)(int *); int (*DeviceGet)(int *,int);
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
} driver;
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
static const char ptx[] =
".version 6.0\n.target sm_61\n.address_size 64\n.visible .entry bitmap_and(.param .u64 a,.param .u64 b,.param .u64 o,.param .u32 n) {\n.reg .pred %p; .reg .b32 %r<7>; .reg .b64 %d<8>;\nld.param.u64 %d0,[a]; ld.param.u64 %d1,[b]; ld.param.u64 %d2,[o]; ld.param.u32 %r0,[n];\nmov.u32 %r1,%ctaid.x; mov.u32 %r2,%ntid.x; mov.u32 %r3,%tid.x; mad.lo.u32 %r4,%r1,%r2,%r3; setp.ge.u32 %p,%r4,%r0; @%p bra done;\nmul.wide.u32 %d3,%r4,4; add.u64 %d4,%d0,%d3; add.u64 %d5,%d1,%d3; add.u64 %d6,%d2,%d3; ld.global.u32 %r5,[%d4]; ld.global.u32 %r6,[%d5]; and.b32 %r5,%r5,%r6; st.global.u32 [%d6],%r5;\ndone: ret; }\n";

static uint64_t new_handle(void) {
    uint64_t result = next_handle;
    if (result) next_handle = result == INT64_MAX ? 0 : result + 1;
    return result;
}
static int load_driver(void) {
    if (driver.lib) return 1;
    driver.lib = dlopen("libcuda.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!driver.lib) return 0;
#define LOAD(field,symbol) do { *(void **)(&driver.field) = dlsym(driver.lib,symbol); if (!driver.field) goto fail; } while (0)
    LOAD(Init,"cuInit"); LOAD(DeviceGetCount,"cuDeviceGetCount"); LOAD(DeviceGet,"cuDeviceGet");
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
    return 1;
fail:
    dlclose(driver.lib); memset(&driver,0,sizeof(driver)); return 0;
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
    result = driver.ModuleLoadData(&state.module,ptx) ||
             driver.ModuleGetFunction(&state.function,state.module,"bitmap_and") ? UNCERTAIN : OK;
    result=leave(result); /* cuCtxCreate made our context current. */
    if (result && !state.context_fault && close_locked()==OK) { *out=0; result=REJECTED; }
done:
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t session_close(uint64_t session) {
    pthread_mutex_lock(&mutex);
    int result = !session || session!=state.handle ? INVALID : close_locked();
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t resource_alloc(uint64_t session,const SimpleGpuResourceDescV1 *desc,uint64_t *out) {
    if (!out) return REJECTED;
    *out=0; pthread_mutex_lock(&mutex); int result=REJECTED;
    if (!session || session!=state.handle || !desc || desc->struct_size!=sizeof(*desc) ||
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
    if (!session || session!=state.handle || !desc || desc->struct_size!=sizeof(*desc) ||
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
    if (!session || session!=state.handle || !completion || completion!=state.completion ||
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
    if (session && session==state.handle && resource && resource==state.resource &&
        state.ready && !state.context_fault && bytes && bytes->struct_size==sizeof(*bytes) &&
        !bytes->reserved && bytes->data && bytes->length>=state.bytes) {
        memcpy(bytes->data,state.host_output,state.bytes); bytes->length=state.bytes; result=OK;
    }
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t completion_release(uint64_t session,uint64_t completion) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (session && session==state.handle && completion && completion==state.completion)
        result=enter() ? leave(drain_completion()) : UNCERTAIN;
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t resource_release(uint64_t session,uint64_t resource) {
    pthread_mutex_lock(&mutex); int result=INVALID;
    if (session && session==state.handle && resource && resource==state.resource)
        result=state.completion ? BUSY : (enter() ? leave(free_resource()) : UNCERTAIN);
    pthread_mutex_unlock(&mutex); return result;
}
static int32_t shutdown_provider(void) {
    pthread_mutex_lock(&mutex); int result=BUSY;
    if (!state.handle) {
        result=OK;
        if (driver.lib && dlclose(driver.lib)) result=SIMPLE_GPU_STATUS_FAILED;
        if (!result) memset(&driver,0,sizeof(driver));
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
