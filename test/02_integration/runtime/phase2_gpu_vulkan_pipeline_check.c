#define _POSIX_C_SOURCE 200809L
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
extern int64_t phase2_gpu_vulkan_pipeline_probe(void);
extern int64_t phase2_gpu_vulkan_pipeline_provider_counter(int64_t);
extern int64_t rt_gpu_provider_loaded(int64_t);
extern int64_t rt_gpu_provider_unload(int64_t);
extern int64_t rt_vulkan_create_compute_pipeline_raw(int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_create_compute_pipeline(int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_push_constants(int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_push_constants_array(int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_present_buffer_regions(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_destroy_swapchain(int64_t);
extern int64_t rt_vulkan_init_headless_present(int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_init_window_present(int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_init_external_window_present(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_present_buffer(int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_last_present_copy_bytes(int64_t);
extern int64_t rt_vulkan_last_present_copy_rects(int64_t);
#define CHECK(x) do { if (!(x)) { fprintf(stderr,"FAIL line=%d %s\n",__LINE__,#x); return 1; } } while(0)
int main(int argc, char **argv) {
    CHECK(argc == 3);
    __simple_runtime_init();
    CHECK(!setenv("SIMPLE_VULKAN_PROVIDER_PATH", argv[1], 1));
    /* macOS legacy symbols are un-authenticated; immutable v1 is unavailable.
     * The checker records SHA separately, never claims exact-byte admission. */
    (void)argv[2];
    unsetenv("SIMPLE_VULKAN_PROVIDER_SHA256");
    CHECK(rt_gpu_provider_loaded(2) == 1);
    int64_t native = phase2_gpu_vulkan_pipeline_probe();
    if (native) fprintf(stderr,"native_probe=%lld\n",(long long)native);
    CHECK(native == 0);
    CHECK(phase2_gpu_vulkan_pipeline_provider_counter(0) == 0);
    CHECK(phase2_gpu_vulkan_pipeline_provider_counter(2) == 1);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,(int64_t)(intptr_t)"kernel_entry",12,4)==101);
    CHECK(rt_vulkan_init_headless_present(41,42,43)==102);
    CHECK(rt_vulkan_init_window_present(44,45,46)==103);
    CHECK(rt_vulkan_init_external_window_present(51,52,53,54,55,56)==104);
    CHECK(rt_vulkan_last_present_copy_bytes(31)==4096);
    CHECK(rt_vulkan_last_present_copy_rects(31)==2);
    CHECK(rt_vulkan_destroy_swapchain(31)==1);
    int64_t before = phase2_gpu_vulkan_pipeline_provider_counter(1);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,0,12,4)==0);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,1,4097,4)==0);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,(int64_t)(intptr_t)"ker\0nel",7,4)==0);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,(int64_t)(intptr_t)"kernel_entry",12,INT64_MAX)==0);
    CHECK(rt_vulkan_push_constants(21,22,0)==0);
    CHECK(rt_vulkan_push_constants_array(21,22,0,-1)==0);
    CHECK(rt_vulkan_present_buffer_regions(31,32,640,480,33,0)==0);
    SplArray *bad = rt_array_new(4);
    CHECK(bad != NULL);
    CHECK(rt_array_push(bad, rt_value_bool(1)));
    CHECK(rt_array_push(bad, rt_value_int(2)));
    CHECK(rt_array_push(bad, rt_value_int(3)));
    CHECK(rt_array_push(bad, rt_value_int(4)));
    CHECK(rt_vulkan_push_constants(21,22,(int64_t)(intptr_t)bad)==0);
    CHECK(rt_vulkan_present_buffer_regions(31,32,640,480,33,(int64_t)(intptr_t)bad)==0);
    SplArray *bytes = rt_byte_array_new_len(4);
    CHECK(bytes != NULL);
    CHECK(rt_vulkan_present_buffer_regions(31,32,640,480,33,(int64_t)(intptr_t)bytes)==0);
    SplArray *rects = rt_array_new(4);
    CHECK(rects != NULL);
    for (int i=1;i<=4;++i) CHECK(rt_array_push(rects,rt_value_int(i)));
    CHECK(rt_vulkan_present_buffer_regions(31,32,0,480,33,(int64_t)(intptr_t)rects)==0);
    CHECK(rt_vulkan_present_buffer_regions(31,32,INT64_MAX,480,33,(int64_t)(intptr_t)rects)==0);
    CHECK(phase2_gpu_vulkan_pipeline_provider_counter(1)==before);
    /* Repeated actual native probes verify transient loans/free paths and cost. */
    clock_t start = clock();
    for (int i=0;i<1000;++i) CHECK(phase2_gpu_vulkan_pipeline_probe()==0);
    double elapsed = (double)(clock()-start)/CLOCKS_PER_SEC;
    CHECK(phase2_gpu_vulkan_pipeline_provider_counter(0)==0);
    /* Last operation retires the provider while its own pin is active. */
    CHECK(rt_vulkan_present_buffer(61,62,63,64,65)==4);
    CHECK(rt_vulkan_last_present_copy_bytes(31)==-1);
    CHECK(rt_gpu_provider_unload(2)==1);
    unsetenv("SIMPLE_VULKAN_PROVIDER_PATH");
    unsetenv("SIMPLE_VULKAN_PROVIDER_SHA256");
    CHECK(rt_vulkan_last_present_copy_bytes(31)==-1);
    CHECK(rt_vulkan_last_present_copy_rects(31)==-1);
    CHECK(rt_vulkan_init_external_window_present(51,52,53,54,55,56)==0);
    CHECK(rt_vulkan_init_headless_present(41,42,43)==0);
    CHECK(rt_vulkan_init_window_present(44,45,46)==0);
    CHECK(rt_vulkan_destroy_swapchain(31)==0);
    CHECK(rt_vulkan_present_buffer(61,62,63,64,65)==0);
    CHECK(rt_vulkan_create_compute_pipeline_raw(11,(int64_t)(intptr_t)"kernel_entry",12,4)==0);
    CHECK(rt_vulkan_push_constants(21,22,(int64_t)(intptr_t)bytes)==0);
    CHECK(rt_vulkan_push_constants_array(21,22,(int64_t)(intptr_t)bytes,2)==0);
    CHECK(rt_vulkan_present_buffer_regions(31,32,640,480,33,(int64_t)(intptr_t)rects)==0);
    printf("phase2_gpu_vulkan_pipeline=PASS native_boundary=1 lease_reentry=1 unload=1 probes=1001 cpu_seconds=%.6f\n",elapsed);
    __simple_runtime_shutdown();
    return 0;
}
