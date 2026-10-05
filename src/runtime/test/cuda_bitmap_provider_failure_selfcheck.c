/* Deterministic failure-policy unit test of the actual provider owner.
 * Mocked Driver API calls here are NOT CUDA device execution evidence. */
#include "../providers/cuda/bitmap_provider_v1.c"
#include <stdio.h>
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"FAIL line=%d %s\n",__LINE__,#x); return 1; } } while (0)
static int sync_error, destroy_error, push_error, pop_error;
static unsigned frees, event_destroys, context_destroys;
static int fake_push(void *ctx) { return ctx==state.context ? push_error : 999; }
static int fake_pop(void **ctx) { *ctx=state.context; return pop_error; }
static int fake_sync(void) { return sync_error; }
static int fake_free(DevPtr ptr) { if (ptr) frees++; return 0; }
static int fake_event_destroy(void *event) { if (event) event_destroys++; return 0; }
static int fake_context_destroy(void *ctx) { if (ctx) context_destroys++; return destroy_error; }
static int fake_not_ready(void *event) { (void)event; return 600; }
static void setup(void) {
    memset(&state,0,sizeof(state)); memset(&driver,0,sizeof(driver));
    sync_error=destroy_error=push_error=pop_error=0;
    frees=event_destroys=context_destroys=0;
    driver.CtxPushCurrent=fake_push; driver.CtxPopCurrent=fake_pop;
    driver.CtxSynchronize=fake_sync; driver.MemFree=fake_free;
    driver.EventDestroy=fake_event_destroy; driver.CtxDestroy=fake_context_destroy;
    driver.EventQuery=fake_not_ready;
    state.handle=1; state.context=(void *)(uintptr_t)100;
    state.resource=2; state.output=200; state.bytes=4;
    state.host_output=malloc(4);
    state.completion=3; state.left=300; state.right=400;
    state.input=malloc(8); state.start=(void *)(uintptr_t)500;
    state.end=(void *)(uintptr_t)600; state.submitted=1;
}
int main(void) {
    uint64_t handle=99;
    next_handle=INT64_MAX;
    CHECK(new_handle()==INT64_MAX); CHECK(new_handle()==0); CHECK(new_handle()==0);
    CHECK(session_open(1,0,&handle)==REJECTED && handle==0 && !driver.lib);
    next_handle=1; setup(); CHECK(state.host_output && state.input);
    CHECK(session_open(1,0,&handle)==REJECTED && handle==0);
    SimpleGpuResourceDescV1 desc={sizeof(desc),0,4,1};
    CHECK(resource_alloc(1,&desc,&handle)==REJECTED && handle==0);
    CHECK(shutdown_provider()==BUSY);
    SimpleGpuReceiptV1 receipt={.struct_size=sizeof(receipt)};
    CHECK(wait_completion(1,3,1,&receipt)==SIMPLE_GPU_STATUS_TIMEOUT);
    CHECK(state.completion==3 && frees==0 && event_destroys==0);
    sync_error=999;
    CHECK(completion_release(1,3)==UNCERTAIN);
    CHECK(session_close(1)==UNCERTAIN);
    CHECK(state.handle==1 && state.completion==3 && state.resource==2 && state.input);
    CHECK(frees==0 && event_destroys==0 && context_destroys==0);
    CHECK(resource_release(1,2)==BUSY);
    sync_error=0;
    CHECK(completion_release(1,3)==OK);
    CHECK(!state.completion && !state.input && frees==2 && event_destroys==2);
    CHECK(completion_release(1,3)==INVALID);
    destroy_error=999;
    CHECK(session_close(1)==UNCERTAIN);
    CHECK(state.handle==1 && state.context && !state.resource && frees==3);
    CHECK(shutdown_provider()==BUSY);
    destroy_error=0;
    CHECK(session_close(1)==OK && !state.handle && context_destroys==2);
    CHECK(shutdown_provider()==OK);
    setup(); CHECK(state.host_output && state.input);
    push_error=999;
    CHECK(completion_release(1,3)==UNCERTAIN && frees==0 && state.completion==3);
    push_error=0; pop_error=999;
    CHECK(wait_completion(1,3,1,&receipt)==UNCERTAIN && state.context_fault);
    pop_error=0;
    CHECK(session_close(1)==UNCERTAIN && frees==0 && event_destroys==0);
    CHECK(shutdown_provider()==BUSY);
    /* Unit-test-owned host allocations only; fake device objects are integers. */
    free(state.input); free(state.host_output);
    puts("cuda_provider_failure_policy=pass exhaustion=permanent timeout=retained drain_failure=quarantined destroy_failure=retained context_failure=quarantined mocked_driver=true");
    return 0;
}
