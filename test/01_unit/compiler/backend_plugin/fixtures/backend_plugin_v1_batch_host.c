#include "runtime.h"
#include "simple_backend_plugin_v1.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { uint8_t *data; int64_t len; } TestBytes;
int64_t rt_array_len_safe(int64_t v){return ((TestBytes *)(uintptr_t)v)->len;}
int64_t rt_array_data_ptr(SplArray *v){return (int64_t)(uintptr_t)((TestBytes *)v)->data;}
int64_t rt_bytes_from_raw(int64_t p,int64_t n){TestBytes*b=calloc(1,sizeof(*b));b->len=n;b->data=malloc(n?n:1);if(n)memcpy(b->data,(void*)(uintptr_t)p,n);return(int64_t)(uintptr_t)b;}
static TestBytes boxed(uint8_t *p,int64_t n){TestBytes b={p,n};return b;}
static int check_envelope(int64_t value,uint32_t kind,const char *payload){
 TestBytes*out=(TestBytes*)(uintptr_t)value;uint32_t status=1,actual_kind=0;uint64_t size=0;
 if(!out||out->len<32)return 0;memcpy(&status,out->data+8,4);memcpy(&actual_kind,out->data+12,4);memcpy(&size,out->data+16,8);
 return status==0&&actual_kind==kind&&size==strlen(payload)&&memcmp(out->data+32,payload,size)==0;
}
static uint32_t envelope_status(int64_t value){TestBytes*out=(TestBytes*)(uintptr_t)value;uint32_t status=0;if(!out||out->len<32)return UINT32_MAX;memcpy(&status,out->data+8,4);return status;}
int main(int argc,char**argv){
 if(argc<2||argc>3)return 2;
 uint8_t request[16]={1,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0};uint8_t mir[4]={'M','I','R','1'};
 TestBytes path=boxed((uint8_t*)argv[1],strlen(argv[1])),req=boxed(request,16),module=boxed(mir,4);
 int64_t batch=spl_backend_plugin_batch_open_v1((int64_t)(uintptr_t)&path,(int64_t)(uintptr_t)&req);
 if(batch<=0)return 3;
 if(argc==3&&strcmp(argv[2],"compile-fail")==0){
  if(envelope_status(spl_backend_plugin_batch_compile_v1(batch,(int64_t)(uintptr_t)&module))!=32)return 8;
  return spl_backend_plugin_batch_close_v1(batch)==0?0:9;
 }
 if(argc==3&&strcmp(argv[2],"finalize-fail")==0){
  if(!check_envelope(spl_backend_plugin_batch_compile_v1(batch,(int64_t)(uintptr_t)&module),1,"module-ok"))return 10;
  if(envelope_status(spl_backend_plugin_batch_finalize_v1(batch))!=33)return 11;
  return spl_backend_plugin_batch_close_v1(batch)==0?0:12;
 }
 if(!check_envelope(spl_backend_plugin_batch_compile_v1(batch,(int64_t)(uintptr_t)&module),1,"module-ok"))return 4;
 if(!check_envelope(spl_backend_plugin_batch_compile_v1(batch,(int64_t)(uintptr_t)&module),1,"module-ok"))return 5;
 if(!check_envelope(spl_backend_plugin_batch_finalize_v1(batch),2,"object-ok"))return 6;
 if(spl_backend_plugin_batch_close_v1(batch)!=0)return 7;
 puts("PASS backend-plugin-v1 retained batch");return 0;
}
