#include "runtime.h"
#include "simple_backend_plugin_v1.h"
#ifndef _WIN32
#include <dlfcn.h>
#endif
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef struct { uint8_t *data; int64_t len; } TestBytes;
int64_t rt_array_len_safe(int64_t v){return ((TestBytes *)(uintptr_t)v)->len;}
int64_t rt_array_data_ptr(SplArray *v){return (int64_t)(uintptr_t)((TestBytes *)v)->data;}
int64_t rt_bytes_from_raw(int64_t p,int64_t n){TestBytes*b=calloc(1,sizeof(*b));b->len=n;b->data=malloc(n?n:1);if(n)memcpy(b->data,(void*)(uintptr_t)p,n);return(int64_t)(uintptr_t)b;}
static TestBytes boxed(uint8_t *p,int64_t n){TestBytes b={p,n};return b;}
int main(int argc,char**argv){
 if(argc<3)return 2;
 int expected=atoi(argv[2]);
 uint8_t request[16]={1,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0};
 uint8_t mir[4]={'M','I','R','1'};
 int64_t request_len=(argc>3&&strcmp(argv[3],"bad-request")==0)?8:16;
 int64_t mir_len=(argc>3&&strcmp(argv[3],"bad-mir")==0)?0:4;
 uint8_t provider_wire[SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_SIZE_V1]={0};
 TestBytes provider=boxed((uint8_t*)argv[1],strlen(argv[1])),req=boxed(request,request_len),m=boxed(mir,mir_len);
 void *admitted=NULL;
 const char *expected_payload="object-ok";
 if(argc>3&&strcmp(argv[3],"admitted-substitution")==0){
#ifdef _WIN32
  return 8;
#else
  if(argc<5)return 9;
  admitted=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);if(!admitted)return 10;
  if(rename(argv[4],argv[1])!=0){dlclose(admitted);return 11;}
  uint32_t magic=SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1,version=SIMPLE_BACKEND_BRIDGE_VERSION_V1;
  uint64_t handle=(uint64_t)(uintptr_t)admitted;
  memcpy(provider_wire,&magic,4);memcpy(provider_wire+4,&version,4);memcpy(provider_wire+8,&handle,8);
  provider=boxed(provider_wire,sizeof(provider_wire));expected_payload="admitted-object";
#endif
 }else if(argc>3&&strcmp(argv[3],"bad-handle")==0){
  uint32_t magic=SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1;
  memcpy(provider_wire,&magic,4);provider=boxed(provider_wire,4);
 }
 TestBytes*out=(TestBytes*)(uintptr_t)spl_backend_plugin_run_v1((int64_t)(uintptr_t)&provider,(int64_t)(uintptr_t)&req,(int64_t)(uintptr_t)&m);
#ifndef _WIN32
 if(admitted)dlclose(admitted);
#endif
 if(!out||out->len<32)return 3;
 uint32_t magic=0,status=1,kind=0;uint64_t pn=0,dn=0;
 memcpy(&magic,out->data,4);memcpy(&status,out->data+8,4);memcpy(&kind,out->data+12,4);memcpy(&pn,out->data+16,8);memcpy(&dn,out->data+24,8);
 if(magic!=SIMPLE_BACKEND_BRIDGE_MAGIC_V1||status!=(uint32_t)expected)return 4;
 size_t expected_payload_len=strlen(expected_payload);
 if(expected==0&&(kind!=2||pn!=expected_payload_len||dn!=18||memcmp(out->data+32,expected_payload,expected_payload_len)||memcmp(out->data+32+expected_payload_len,"fixture-diagnostic",18)))return 5;
 puts("PASS backend-plugin-v1 native bridge");return 0;
}
