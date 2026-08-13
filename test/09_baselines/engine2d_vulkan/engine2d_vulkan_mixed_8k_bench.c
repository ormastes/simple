#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

extern int64_t rt_vulkan_init(void),rt_vulkan_shutdown(void),rt_vulkan_begin_compute(void);
extern int64_t rt_vulkan_alloc_buffer(int64_t,int64_t),rt_vulkan_free_buffer(int64_t);
extern int64_t rt_vulkan_compile_spirv_raw(int64_t,int64_t),rt_vulkan_destroy_shader(int64_t);
extern int64_t rt_vulkan_create_compute_pipeline(int64_t,int64_t,int64_t),rt_vulkan_destroy_pipeline(int64_t);
extern int64_t rt_vulkan_create_descriptor_set(int64_t),rt_vulkan_bind_buffer(int64_t,int64_t,int64_t),rt_vulkan_destroy_descriptor_set(int64_t);
extern int64_t rt_vulkan_bind_pipeline(int64_t,int64_t),rt_vulkan_bind_descriptors(int64_t,int64_t),rt_vulkan_push_constants_raw(int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_vulkan_dispatch(int64_t,int64_t,int64_t,int64_t),rt_vulkan_end_compute(int64_t),rt_vulkan_submit_and_wait_fence(int64_t);
extern int64_t rt_vulkan_wait_fence(int64_t,int64_t),rt_vulkan_destroy_fence(int64_t);
extern int64_t rt_vulkan_copy_to_buffer_raw(int64_t,int64_t,int64_t,int64_t),rt_vulkan_copy_from_buffer_raw(int64_t,int64_t,int64_t,int64_t);
extern const char *rt_vulkan_selected_device_name(void),*rt_vulkan_selected_device_type(void),*rt_vulkan_selected_device_driver_identity(void);
extern int64_t rt_vulkan_selected_device_driver_identity_hash(void);

typedef struct{int32_t x,y,w,h;uint32_t color;int32_t fw,fh,cx,cy,cw,ch,clip,res[4];}Rect;
typedef struct{int32_t x,y,w,h,fw,fh,cx,cy,cw,ch,clip,opacity,mode,sw,sh,res;}Image;
typedef struct{int64_t shader,pipe,desc;}Kernel;
static uint64_t now_ns(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return(uint64_t)t.tv_sec*1000000000ULL+t.tv_nsec;}
static int cmp(const void*a,const void*b){uint64_t x=*(const uint64_t*)a,y=*(const uint64_t*)b;return x<y?-1:x>y;}
static unsigned char*readf(const char*p,size_t*n){FILE*f=fopen(p,"rb");if(!f)return NULL;fseek(f,0,SEEK_END);long z=ftell(f);rewind(f);unsigned char*b=malloc((size_t)z);if(z<=0||!b||fread(b,1,(size_t)z,f)!=(size_t)z){free(b);b=NULL;}fclose(f);*n=(size_t)z;return b;}
static int chunks(int put,int64_t h,void*p,uint64_t n){uint64_t o=0;while(o<n){uint64_t c=n-o;if(c>64ULL<<20)c=64ULL<<20;int ok=put?rt_vulkan_copy_to_buffer_raw(h,(int64_t)(uintptr_t)((unsigned char*)p+o),(int64_t)c,(int64_t)o):rt_vulkan_copy_from_buffer_raw((int64_t)(uintptr_t)((unsigned char*)p+o),(int64_t)c,h,(int64_t)o);if(!ok)return 0;o+=c;}return 1;}
static Kernel kernel(const char*dir,const char*name,int64_t push){char path[512];snprintf(path,sizeof(path),"%s/%s.spv",dir,name);size_t n=0;unsigned char*b=readf(path,&n);Kernel k={0};if(!b)return k;k.shader=rt_vulkan_compile_spirv_raw((int64_t)(uintptr_t)b,(int64_t)n);k.pipe=rt_vulkan_create_compute_pipeline(k.shader,(int64_t)(uintptr_t)"main",push);free(b);return k;}
int main(int argc,char**argv){
 if(argc!=5)return 2;
 uint32_t samples=(uint32_t)strtoul(argv[2],0,10),glyphs=(uint32_t)strtoul(argv[3],0,10),lines=(uint32_t)strtoul(argv[4],0,10);
 if(samples<3||!glyphs||glyphs>4096||lines>64)return 2;
 const uint32_t W=7680,H=4320,GW=16,GH=16;uint64_t np=(uint64_t)W*H,nb=np*4,imgn=(uint64_t)W*50;
 if(!rt_vulkan_init())return 3;
 const char *adapter_name=rt_vulkan_selected_device_name(),*adapter_type=rt_vulkan_selected_device_type(),*adapter_identity=rt_vulkan_selected_device_driver_identity();int64_t adapter_identity_hash=rt_vulkan_selected_device_driver_identity_hash();
 if(!adapter_name)adapter_name="";
 if(!adapter_type)adapter_type="";
 if(!adapter_identity)adapter_identity="";
 int64_t fb=rt_vulkan_alloc_buffer((int64_t)nb,0x83),src=rt_vulkan_alloc_buffer((int64_t)imgn*4,0x83),atlas=rt_vulkan_alloc_buffer(GW*GH*4,0x83);
 Kernel clear=kernel(argv[1],"clear",64),rect=kernel(argv[1],"rect_filled",64),image=kernel(argv[1],"image_copy",64),font=kernel(argv[1],"font_atlas_packed",0);
 uint64_t words=8+7ULL*glyphs;int64_t fp=rt_vulkan_alloc_buffer((int64_t)words*4,0x83);uint32_t*pp=calloc((size_t)words,4),*buf=malloc((size_t)nb),*isrc=malloc((size_t)imgn*4);uint32_t mask[GW*GH];
 if(!fb||!src||!atlas||!clear.pipe||!rect.pipe||!image.pipe||!font.pipe||!fp||!pp||!buf||!isrc)return 4;
 for(uint64_t i=0;i<np;i++)buf[i]=0xff101010u;
 for(uint64_t i=0;i<imgn;i++)isrc[i]=0xff8844ccu;
 for(uint32_t i=0;i<GW*GH;i++)mask[i]=0xffffffffu;
 if(!chunks(1,fb,buf,nb)||!chunks(1,src,isrc,imgn*4)||!chunks(1,atlas,mask,sizeof(mask)))return 4;
 Kernel*kernels[]={&rect,&image,&font};for(int i=0;i<3;i++)kernels[i]->desc=rt_vulkan_create_descriptor_set(kernels[i]->pipe);
 if(!rt_vulkan_bind_buffer(rect.desc,0,fb)||!rt_vulkan_bind_buffer(image.desc,0,fb)||!rt_vulkan_bind_buffer(image.desc,1,src)||!rt_vulkan_bind_buffer(font.desc,0,atlas)||!rt_vulkan_bind_buffer(font.desc,1,fb)||!rt_vulkan_bind_buffer(font.desc,2,fp))return 4;
 pp[0]=GW;pp[1]=GH;pp[2]=GW*GH;pp[3]=W;pp[4]=H;pp[5]=(uint32_t)np;pp[6]=glyphs;pp[7]=GW*GH;for(uint32_t i=0;i<glyphs;i++){uint64_t b=8+7ULL*i;pp[b+2]=GW;pp[b+3]=GH;pp[b+4]=(i%256)*20;pp[b+5]=300+(i/256)*20;pp[b+6]=0xffffffffu;}
 uint64_t*t=calloc(samples,sizeof(uint64_t));for(uint32_t s=0;s<samples+1;s++){uint64_t st=now_ns();int ok=rt_vulkan_copy_to_buffer_raw(fp,(int64_t)(uintptr_t)pp,(int64_t)words*4,0);int64_t cmd=ok?rt_vulkan_begin_compute():0;
  ok=cmd>0&&rt_vulkan_bind_pipeline(cmd,rect.pipe)&&rt_vulkan_bind_descriptors(cmd,rect.desc);Rect rp={0,0,W,100,0xffcc2222u,W,H,0,0,W,H,1,{0}};ok=ok&&rt_vulkan_push_constants_raw(cmd,rect.pipe,(int64_t)(uintptr_t)&rp,64)&&rt_vulkan_dispatch(cmd,480,7,1);for(uint32_t l=0;ok&&l<lines;l++){Rect p={0,120+(int32_t)l*2,W,1,0xff22cc44u,W,H,0,0,W,H,1,{0}};ok=rt_vulkan_push_constants_raw(cmd,rect.pipe,(int64_t)(uintptr_t)&p,64)&&rt_vulkan_dispatch(cmd,480,1,1);}
  Image ip={0,200,W,50,W,H,0,0,W,H,1,1000,0,W,50,0};ok=ok&&rt_vulkan_bind_pipeline(cmd,image.pipe)&&rt_vulkan_bind_descriptors(cmd,image.desc)&&rt_vulkan_push_constants_raw(cmd,image.pipe,(int64_t)(uintptr_t)&ip,64)&&rt_vulkan_dispatch(cmd,480,4,1);ok=ok&&rt_vulkan_bind_pipeline(cmd,font.pipe)&&rt_vulkan_bind_descriptors(cmd,font.desc)&&rt_vulkan_dispatch(cmd,4,glyphs,1)&&rt_vulkan_end_compute(cmd);int64_t f=ok?rt_vulkan_submit_and_wait_fence(cmd):0;ok=f>0&&rt_vulkan_wait_fence(f,0);if(f>0)ok=rt_vulkan_destroy_fence(f)&&ok;if(!ok)return 5;if(s)t[s-1]=now_ns()-st;}
 qsort(t,samples,sizeof(uint64_t),cmp);uint32_t p95=(95*samples+99)/100-1;if(p95>=samples)p95=samples-1;if(!chunks(0,fb,buf,nb))return 6;uint64_t bad=0,changed=0,checksum=1469598103934665603ULL;for(uint64_t i=0;i<np;i++){uint32_t x=i%W,y=i/W,e=0xff101010u;if(y<100)e=0xffcc2222u;else if(y>=120&&y<120+lines*2&&y%2==0)e=0xff22cc44u;else if(y>=200&&y<250)e=0xff8844ccu;else if(y>=300){uint32_t gx=x/20,gy=(y-300)/20;if(gx<256&&x%20<GW&&(y-300)%20<GH&&(uint64_t)gy*256+gx<glyphs)e=0xffffffffu;}if(buf[i]!=e)bad++;if(buf[i]!=0xff101010u)changed++;checksum^=buf[i];checksum*=1099511628211ULL;}
 printf("engine2d_vulkan_mixed_schema=mixed-retained-v1\nengine2d_vulkan_mixed_width=%u\nengine2d_vulkan_mixed_height=%u\n",W,H);printf("engine2d_vulkan_mixed_adapter_name=%s\nengine2d_vulkan_mixed_adapter_type=%s\nengine2d_vulkan_mixed_adapter_identity=%s\nengine2d_vulkan_mixed_adapter_identity_hash=%lld\n",adapter_name,adapter_type,adapter_identity,(long long)adapter_identity_hash);printf("engine2d_vulkan_mixed_glyphs=%u\nengine2d_vulkan_mixed_lines=%u\n",glyphs,lines);printf("engine2d_vulkan_mixed_dispatch_count=%u\nengine2d_vulkan_mixed_submission_count=1\nengine2d_vulkan_mixed_samples=%u\n",lines+3,samples);printf("engine2d_vulkan_mixed_frame_p50_ns=%llu\nengine2d_vulkan_mixed_frame_p95_ns=%llu\nengine2d_vulkan_mixed_within_80fps_budget=%s\n",(unsigned long long)t[(samples-1)/2],(unsigned long long)t[p95],t[p95]<=12500000?"true":"false");printf("engine2d_vulkan_mixed_timed_readback_bytes=0\nengine2d_vulkan_mixed_evidence_readback_bytes=%llu\nengine2d_vulkan_mixed_changed_pixels=%llu\nengine2d_vulkan_mixed_mismatch_count=%llu\nengine2d_vulkan_mixed_checksum=%llu\nengine2d_vulkan_mixed_swapchain_presented=false\nengine2d_vulkan_mixed_dynamic_frame_80fps_proven=false\n",(unsigned long long)nb,(unsigned long long)changed,(unsigned long long)bad,(unsigned long long)checksum);
 for(int i=0;i<3;i++){rt_vulkan_destroy_descriptor_set(kernels[i]->desc);}Kernel all[]={font,image,rect,clear};for(int i=0;i<4;i++){rt_vulkan_destroy_pipeline(all[i].pipe);rt_vulkan_destroy_shader(all[i].shader);}rt_vulkan_free_buffer(fp);rt_vulkan_free_buffer(atlas);rt_vulkan_free_buffer(src);rt_vulkan_free_buffer(fb);rt_vulkan_shutdown();free(t);free(isrc);free(buf);free(pp);return bad?7:0;
}
