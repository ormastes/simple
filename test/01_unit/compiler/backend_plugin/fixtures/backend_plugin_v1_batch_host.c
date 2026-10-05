#ifdef _WIN32
#define _CRT_SECURE_NO_WARNINGS
#endif
#include "runtime.h"
#include "simple_backend_plugin_v1.h"
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#endif
typedef struct { uint8_t *data; int64_t len; } TestBytes;
int64_t rt_array_len_safe(int64_t v){return ((TestBytes *)(uintptr_t)v)->len;}
int64_t rt_array_data_ptr(SplArray *v){return (int64_t)(uintptr_t)((TestBytes *)v)->data;}
int64_t rt_bytes_from_raw(int64_t p,int64_t n){TestBytes*b=calloc(1,sizeof(*b));b->len=n;b->data=malloc(n?n:1);if(n)memcpy(b->data,(void*)(uintptr_t)p,n);return(int64_t)(uintptr_t)b;}
static TestBytes boxed(uint8_t *p,int64_t n){TestBytes b={p,n};return b;}
static int check_envelope(int64_t value,uint32_t kind,const char *payload){
 TestBytes*out=(TestBytes*)(uintptr_t)value;uint32_t status=1,actual_kind=0;uint64_t size=0;
 if(!out||out->len<32)return 0;memcpy(&status,out->data+8,4);memcpy(&actual_kind,out->data+12,4);memcpy(&size,out->data+16,8);
 int ok=status==0&&actual_kind==kind&&size==strlen(payload)&&memcmp(out->data+32,payload,size)==0;
 free(out->data);free(out);return ok;
}
static uint32_t envelope_status(int64_t value){TestBytes*out=(TestBytes*)(uintptr_t)value;uint32_t status=0;if(!out||out->len<32)return UINT32_MAX;memcpy(&status,out->data+8,4);free(out->data);free(out);return status;}
int main(int argc,char**argv){
 if(argc<2||argc>3)return 2;
 uint8_t request[16]={1,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0};uint8_t mir[4]={'M','I','R','1'};
 TestBytes path=boxed((uint8_t*)argv[1],strlen(argv[1])),req=boxed(request,16),module=boxed(mir,4);
#ifdef _WIN32
 HMODULE library=NULL;
 uint8_t handle_packet[SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_SIZE_V1]={0};
 if(getenv("SBP_TEST_RETAINED_HANDLE")){
  library=LoadLibraryA(argv[1]);if(!library)return 13;
  uint32_t tag=SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1,version=SIMPLE_BACKEND_BRIDGE_VERSION_V1;
  uint64_t handle=(uint64_t)(uintptr_t)library;
  memcpy(handle_packet,&tag,4);memcpy(handle_packet+4,&version,4);memcpy(handle_packet+8,&handle,8);
  path=boxed(handle_packet,sizeof(handle_packet));
 }
#endif
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
 if(envelope_status(spl_backend_plugin_batch_compile_v1(batch,(int64_t)(uintptr_t)&module))!=108)return 16;
 if(envelope_status(spl_backend_plugin_batch_finalize_v1(batch))!=108)return 17;
 if(spl_backend_plugin_batch_close_v1(batch)!=0)return 7;
#ifdef _WIN32
 if(library){
  if(!GetProcAddress(library,SIMPLE_BACKEND_PLUGIN_ENTRY_V1))return 14;
  const char*marker=getenv("SBP_FIXTURE_UNLOAD_MARKER");
  if(marker&&GetFileAttributesA(marker)!=INVALID_FILE_ATTRIBUTES)return 15;
  if(!FreeLibrary(library))return 18;
 }
#endif
 puts("PASS backend-plugin-v1 retained batch");return 0;
}
