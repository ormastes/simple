#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern int64_t rt_vulkan_init(void), rt_vulkan_shutdown(void);
extern int64_t rt_vulkan_alloc_buffer(int64_t, int64_t), rt_vulkan_free_buffer(int64_t);
extern int64_t rt_vulkan_compile_spirv_raw(int64_t, int64_t), rt_vulkan_destroy_shader(int64_t);
extern int64_t rt_vulkan_create_compute_pipeline(int64_t, int64_t, int64_t), rt_vulkan_destroy_pipeline(int64_t);
extern int64_t rt_vulkan_create_descriptor_set(int64_t), rt_vulkan_bind_buffer(int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_destroy_descriptor_set(int64_t), rt_vulkan_begin_compute(void);
extern int64_t rt_vulkan_bind_pipeline(int64_t, int64_t), rt_vulkan_bind_descriptors(int64_t, int64_t);
extern int64_t rt_vulkan_dispatch(int64_t, int64_t, int64_t, int64_t), rt_vulkan_end_compute(int64_t);
extern int64_t rt_vulkan_submit_and_wait_fence(int64_t), rt_vulkan_wait_fence(int64_t, int64_t);
extern int64_t rt_vulkan_destroy_fence(int64_t);
extern int64_t rt_vulkan_copy_to_buffer_raw(int64_t, int64_t, int64_t, int64_t);
extern int64_t rt_vulkan_copy_from_buffer_raw(int64_t, int64_t, int64_t, int64_t);

typedef struct {
    uint32_t atlas_width, atlas_height, atlas_count, atlas_x, atlas_y;
    uint32_t quad_width, quad_height, dst_width, dst_height, dst_count;
    int32_t dst_x, dst_y; uint32_t color;
} FontParams;

static uint64_t now_ns(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec; }
static int cmp_u64(const void *a,const void *b){uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b;return x<y?-1:x>y;}
static unsigned char *read_file(const char *p,size_t *n){FILE*f=fopen(p,"rb");if(!f)return NULL;fseek(f,0,SEEK_END);long z=ftell(f);rewind(f);unsigned char*b=malloc((size_t)z);if(z<=0||!b||fread(b,1,(size_t)z,f)!=(size_t)z){free(b);b=NULL;}fclose(f);*n=(size_t)z;return b;}
static int upload_chunks(int64_t h,const void*p,uint64_t n){uint64_t o=0;while(o<n){uint64_t c=n-o;if(c>64ULL*1024*1024)c=64ULL*1024*1024;if(!rt_vulkan_copy_to_buffer_raw(h,(int64_t)(uintptr_t)((const unsigned char*)p+o),(int64_t)c,(int64_t)o))return 0;o+=c;}return 1;}
static int download_chunks(void*p,int64_t h,uint64_t n){uint64_t o=0;while(o<n){uint64_t c=n-o;if(c>64ULL*1024*1024)c=64ULL*1024*1024;if(!rt_vulkan_copy_from_buffer_raw((int64_t)(uintptr_t)((unsigned char*)p+o),(int64_t)c,h,(int64_t)o))return 0;o+=c;}return 1;}

int main(int argc,char**argv){
    if(argc!=4)return 2;
    uint32_t glyphs=(uint32_t)strtoul(argv[2],NULL,10),samples=(uint32_t)strtoul(argv[3],NULL,10);
    if(!glyphs||glyphs>4096||samples<3)return 2;
    const uint32_t w=7680,h=4320,gw=16,gh=16;const uint64_t pixels=(uint64_t)w*h,bytes=pixels*4;
    size_t spv_n=0;unsigned char*spv=read_file(argv[1],&spv_n);if(!spv||!rt_vulkan_init())return 3;
    int64_t fb=rt_vulkan_alloc_buffer((int64_t)bytes,0x83),atlas=rt_vulkan_alloc_buffer(gw*gh*4,0x83);
    int64_t shader=rt_vulkan_compile_spirv_raw((int64_t)(uintptr_t)spv,(int64_t)spv_n);
    int64_t pipe=rt_vulkan_create_compute_pipeline(shader,(int64_t)(uintptr_t)"main",0);
    uint32_t*seed=malloc((size_t)bytes);uint32_t mask[gw*gh];
    if(!fb||!atlas||!shader||!pipe||!seed)return 4;
    for(uint64_t i=0;i<pixels;i++)seed[i]=0xff101010u;
    for(uint32_t i=0;i<gw*gh;i++)mask[i]=0xffffffffu;
    if(!upload_chunks(fb,seed,bytes)||!upload_chunks(atlas,mask,sizeof(mask)))return 4;
    int64_t*params=calloc(glyphs,sizeof(int64_t)),*desc=calloc(glyphs,sizeof(int64_t));FontParams*host=calloc(glyphs,sizeof(FontParams));
    if(!params||!desc||!host)return 4;
    for(uint32_t i=0;i<glyphs;i++){
        params[i]=rt_vulkan_alloc_buffer(sizeof(FontParams),0x83);desc[i]=rt_vulkan_create_descriptor_set(pipe);
        host[i]=(FontParams){gw,gh,gw*gh,0,0,gw,gh,w,h,(uint32_t)pixels,(int32_t)((i%256)*20),(int32_t)((i/256)*20),0xffffffffu};
        if(!params[i]||!desc[i]||!rt_vulkan_bind_buffer(desc[i],0,atlas)||!rt_vulkan_bind_buffer(desc[i],1,fb)||!rt_vulkan_bind_buffer(desc[i],2,params[i]))return 4;
    }
    uint64_t*times=calloc(samples,sizeof(uint64_t));
    for(uint32_t s=0;s<samples+1;s++){
        uint64_t start=now_ns();int ok=1;
        for(uint32_t i=0;i<glyphs;i++)ok=ok&&rt_vulkan_copy_to_buffer_raw(params[i],(int64_t)(uintptr_t)&host[i],sizeof(FontParams),0);
        int64_t cmd=ok?rt_vulkan_begin_compute():0;ok=cmd>0&&rt_vulkan_bind_pipeline(cmd,pipe);
        for(uint32_t i=0;ok&&i<glyphs;i++)ok=rt_vulkan_bind_descriptors(cmd,desc[i])&&rt_vulkan_dispatch(cmd,4,1,1);
        ok=ok&&rt_vulkan_end_compute(cmd);int64_t fence=ok?rt_vulkan_submit_and_wait_fence(cmd):0;ok=fence>0&&rt_vulkan_wait_fence(fence,0);
        if(fence>0)ok=rt_vulkan_destroy_fence(fence)&&ok;
        if(!ok)return 5;
        if(s)times[s-1]=now_ns()-start;
    }
    qsort(times,samples,sizeof(uint64_t),cmp_u64);uint32_t p95=(95*samples+99)/100-1;if(p95>=samples)p95=samples-1;
    if(!download_chunks(seed,fb,bytes))return 6;
    uint64_t mismatch=0,changed=0;
    for(uint64_t i=0;i<pixels;i++){uint32_t x=(uint32_t)(i%w),y=(uint32_t)(i/w);uint32_t gx=x/20,gy=y/20;int ink=gx<256&&(x%20)<gw&&(y%20)<gh&&(gy*256+gx)<glyphs;uint32_t expected=ink?0xffffffffu:0xff101010u;if(seed[i]!=expected)mismatch++;if(seed[i]!=0xff101010u)changed++;}
    printf("engine2d_vulkan_font_schema=font-warm-pool-v1\nengine2d_vulkan_font_width=%u\nengine2d_vulkan_font_height=%u\n",w,h);
    printf("engine2d_vulkan_font_glyphs=%u\nengine2d_vulkan_font_samples=%u\n",glyphs,samples);
    printf("engine2d_vulkan_font_frame_p50_ns=%llu\nengine2d_vulkan_font_frame_p95_ns=%llu\n",(unsigned long long)times[(samples-1)/2],(unsigned long long)times[p95]);
    printf("engine2d_vulkan_font_within_80fps_budget=%s\n",times[p95]<=12500000?"true":"false");
    printf("engine2d_vulkan_font_timed_readback_bytes=0\nengine2d_vulkan_font_evidence_readback_bytes=%llu\n",(unsigned long long)bytes);
    printf("engine2d_vulkan_font_changed_pixels=%llu\nengine2d_vulkan_font_mismatch_count=%llu\n",(unsigned long long)changed,(unsigned long long)mismatch);
    printf("engine2d_vulkan_font_swapchain_presented=false\nengine2d_vulkan_font_dynamic_frame_80fps_proven=false\n");
    for(uint32_t i=0;i<glyphs;i++){rt_vulkan_destroy_descriptor_set(desc[i]);rt_vulkan_free_buffer(params[i]);}
    free(times);free(host);free(desc);free(params);free(seed);free(spv);rt_vulkan_destroy_pipeline(pipe);rt_vulkan_destroy_shader(shader);rt_vulkan_free_buffer(atlas);rt_vulkan_free_buffer(fb);rt_vulkan_shutdown();return mismatch?7:0;
}
