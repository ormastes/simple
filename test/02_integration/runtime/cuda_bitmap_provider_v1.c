#define _POSIX_C_SOURCE 200809L
#include "simple_gpu_provider_abi_v1.h"
#include <dlfcn.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int64_t rt_gpu_provider_loaded(int64_t),rt_gpu_provider_identity(int64_t);
int64_t rt_gpu_provider_capability_bits(int64_t),rt_gpu_provider_generation(int64_t);
int64_t rt_gpu_provider_session_open(int64_t,int64_t),rt_gpu_provider_session_close(int64_t,int64_t);
int64_t rt_gpu_provider_resource_alloc(int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_resource_release(int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_submit_raw(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_wait_raw(int64_t,int64_t,int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_readback_raw(int64_t,int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_completion_release(int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_device_image_authority_word(int64_t,int64_t,int64_t,int64_t);
int64_t rt_gpu_provider_unload(int64_t);
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"FAIL line=%d expression=%s\n",__LINE__,#x); return 1; } } while (0)
static int (*get_current)(void **);
static void *caller_context;
static int context_preserved(void) { void *now=NULL; return !get_current(&now) && now==caller_context; }
static uint32_t oracle(uint32_t a,uint32_t b) {
    uint32_t value=0,bit=1;
    for (unsigned i=0;i<32;i++) { if (a%2 && b%2) value+=bit; a/=2; b/=2; bit<<=1; }
    return value;
}
static void store32(uint8_t *p,uint32_t v) { for (unsigned i=0;i<4;i++) p[i]=(uint8_t)(v>>(i*8)); }
static uint64_t checksum(const uint8_t *p,size_t n) {
    uint64_t v=UINT64_C(14695981039346656037);
    for (size_t i=0;i<n;i++) { v^=p[i]; v*=UINT64_C(1099511628211); } return v;
}
struct WaitJob { int64_t session,completion,result; int contexts_ok; SimpleGpuReceiptV1 receipt; };
static void *wait_thread(void *arg) {
    struct WaitJob *job=arg; void *before=NULL,*after=NULL;
    int rc=get_current(&before);
    job->result=rt_gpu_provider_wait_raw(1,job->session,job->completion,UINT64_C(2000000000),(int64_t)(uintptr_t)&job->receipt);
    job->contexts_ok=!rc && !get_current(&after) && before==NULL && after==before;
    return NULL;
}
int main(int argc,char **argv) {
    CHECK(argc==3 || argc==4);
    CHECK(!setenv("SIMPLE_CUDA_PROVIDER_PATH",argv[1],1));
    CHECK(!setenv("SIMPLE_CUDA_PROVIDER_SHA256",argv[2],1));
    int maximum_only=argc==4 && !strcmp(argv[3],"--maximum-only");
    if (argc==4 && !maximum_only) {
        CHECK(!strcmp(argv[3],"denied"));
        CHECK(!rt_gpu_provider_loaded(1));
        CHECK(!dlopen("libcuda.so.1",RTLD_NOW|RTLD_NOLOAD));
        puts("cuda_provider_bad_digest=pass driver_unloaded=true"); return 0;
    }
    CHECK(!dlopen("libcuda.so.1",RTLD_NOW|RTLD_NOLOAD));
    CHECK(rt_gpu_provider_loaded(1));
    CHECK(rt_gpu_provider_identity(1)==INT64_C(0x43554441414e4431));
    CHECK(rt_gpu_provider_capability_bits(1)==3 && rt_gpu_provider_generation(1)>0);
    CHECK(!dlopen("libcuda.so.1",RTLD_NOW|RTLD_NOLOAD));
    void *driver=dlopen("libcuda.so.1",RTLD_NOW|RTLD_LOCAL);
    if (!driver) { puts("UNSUPPORTED libcuda unavailable"); return 77; }
    int (*init)(unsigned)=dlsym(driver,"cuInit");
    int (*count)(int *)=dlsym(driver,"cuDeviceGetCount");
    int (*create)(void **,unsigned,int)=dlsym(driver,"cuCtxCreate_v2");
    int (*destroy)(void *)=dlsym(driver,"cuCtxDestroy_v2");
    *(void **)(&get_current)=dlsym(driver,"cuCtxGetCurrent");
    CHECK(init && count && create && destroy && get_current);
    int devices=0,rc=init(0);
    if (rc || count(&devices) || devices<1) { printf("UNSUPPORTED init=%d devices=%d\n",rc,devices); return 77; }
    CHECK(!create(&caller_context,0,0)); CHECK(context_preserved());
    int64_t session=rt_gpu_provider_session_open(1,0);
    CHECK(session>0 && context_preserved());
    CHECK(!rt_gpu_provider_device_image_authority_word(1,session,1,0));
    CHECK(!rt_gpu_provider_session_open(1,0)); CHECK(context_preserved());
    CHECK(!rt_gpu_provider_resource_alloc(1,session,0,0,1));
    CHECK(!rt_gpu_provider_resource_alloc(1,session,65540,0,1));
    unsigned lengths[]={1,31,32,33,127,128,129,1025,16384};
    uint8_t wire[8+16384*8],expected[16384*4],output[16384*4+16];
    uint64_t total_ns=0; unsigned total_words=0;
    int64_t last_resource=0,last_completion=0;
    unsigned first=maximum_only?8:0, end=maximum_only?9:8;
    for (unsigned k=first;k<end;k++) {
        uint32_t n=lengths[k]; size_t bytes=(size_t)n*4;
        store32(wire,n); store32(wire+4,0);
        for (uint32_t i=0;i<n;i++) {
            uint32_t a=i%3==0?UINT32_MAX:i%3==1?0x80000000u:i*104729u;
            uint32_t b=0xa5a55a5au^(i*17011u);
            store32(wire+8+i*4,a); store32(wire+8+bytes+i*4,b);
            store32(expected+i*4,oracle(a,b));
        }
        int64_t resource=rt_gpu_provider_resource_alloc(1,session,bytes,0,1);
        CHECK(resource>0 && resource!=last_resource && context_preserved());
        CHECK(!rt_gpu_provider_resource_alloc(1,session,bytes,0,1));
        CHECK(!rt_gpu_provider_submit_raw(1,session,resource,2,(int64_t)(uintptr_t)wire,8+bytes*2,100+k));
        CHECK(!rt_gpu_provider_submit_raw(1,session,resource,1,(int64_t)(uintptr_t)wire,7+bytes*2,100+k));
        store32(wire,0);
        CHECK(!rt_gpu_provider_submit_raw(1,session,resource,1,(int64_t)(uintptr_t)wire,8,100+k));
        if (maximum_only) {
            store32(wire,16385);
            CHECK(!rt_gpu_provider_submit_raw(1,session,resource,1,(int64_t)(uintptr_t)wire,8+16385*8,100+k));
            store32(wire,UINT32_MAX);
            CHECK(!rt_gpu_provider_submit_raw(1,session,resource,1,(int64_t)(uintptr_t)wire,INT64_MAX,100+k));
        }
        store32(wire,n);
        int64_t completion=rt_gpu_provider_submit_raw(1,session,resource,1,(int64_t)(uintptr_t)wire,8+bytes*2,100+k);
        CHECK(completion>0 && completion!=last_completion && context_preserved());
        memset(wire,0xcc,sizeof(wire)); /* Borrowed input lifetime ended at submit. */
        CHECK(rt_gpu_provider_resource_release(1,session,resource)==SIMPLE_GPU_STATUS_BUSY);
        CHECK(!rt_gpu_provider_unload(1));
        struct WaitJob job={session,completion,-99,0,{.struct_size=sizeof(job.receipt)}};
        pthread_t thread; CHECK(!pthread_create(&thread,NULL,wait_thread,&job)); CHECK(!pthread_join(thread,NULL));
        CHECK(job.result==0 && job.contexts_ok && context_preserved());
        CHECK(job.receipt.correlation_id==100+k && job.receipt.resource==(uint64_t)resource);
        CHECK(job.receipt.provider_identity==UINT64_C(0x43554441414e4431) && job.receipt.device_identity==0);
        CHECK(job.receipt.checksum==checksum(expected,bytes) && job.receipt.device_elapsed_ns>0);
        CHECK(rt_gpu_provider_wait_raw(1,session,completion,1000000,(int64_t)(uintptr_t)&job.receipt)==SIMPLE_GPU_STATUS_INVALID);
        memset(output,0xd7,sizeof(output));
        SimpleGpuBytesV1 out={sizeof(out),0,output+8,bytes};
        CHECK(!rt_gpu_provider_readback_raw(1,session,resource,(int64_t)(uintptr_t)&out));
        CHECK(out.length==bytes && !memcmp(output+8,expected,bytes));
        for (size_t i=0;i<8;i++) CHECK(output[i]==0xd7 && output[8+bytes+i]==0xd7);
        CHECK(!rt_gpu_provider_completion_release(1,session,completion));
        CHECK(rt_gpu_provider_completion_release(1,session,completion)==SIMPLE_GPU_STATUS_INVALID);
        CHECK(!rt_gpu_provider_resource_release(1,session,resource));
        CHECK(context_preserved());
        total_words+=n; total_ns+=job.receipt.device_elapsed_ns;
        last_resource=resource; last_completion=completion;
    }
    CHECK(!rt_gpu_provider_session_close(1,session)); CHECK(context_preserved());
    int64_t next_session=rt_gpu_provider_session_open(1,0);
    CHECK(next_session>0 && next_session!=session && context_preserved());
    CHECK(rt_gpu_provider_session_close(1,session)==SIMPLE_GPU_STATUS_INVALID);
    CHECK(!rt_gpu_provider_session_close(1,next_session)); CHECK(context_preserved());
    CHECK(rt_gpu_provider_unload(1)); CHECK(context_preserved());
    CHECK(!destroy(caller_context)); CHECK(!dlclose(driver));
    printf("cuda_bitmap_provider_v1=pass authenticated=true launches=%u words=%u contexts=threads+caller canaries=%u copied_input=true maximum_only=%d elapsed_ns=%llu image_authority=none\n",end-first,total_words,(end-first)*16,maximum_only,(unsigned long long)total_ns);
    return 0;
}
