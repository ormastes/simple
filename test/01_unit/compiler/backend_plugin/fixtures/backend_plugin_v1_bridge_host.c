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
#include "backend_plugin_v1_request_wire.h"
int main(int argc,char**argv){
 if(argc<3)return 2;
 int expected=atoi(argv[2]);
 uint8_t request[512];
 uint8_t mir[4]={'M','I','R','1'};
 int64_t request_len=(int64_t)fixture_request_mutate(request,fixture_request(request),argc>3?argv[3]:NULL);
 if(argc>3&&strcmp(argv[3],"bad-request")==0)request_len=8;
 int64_t mir_len=(argc>3&&strcmp(argv[3],"bad-mir")==0)?0:4;
 TestBytes path=boxed((uint8_t*)argv[1],strlen(argv[1])),req=boxed(request,request_len),m=boxed(mir,mir_len);
#ifdef _WIN32
 HMODULE library=NULL;
 uint8_t handle_packet[SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_SIZE_V1]={0};
 if(getenv("SBP_TEST_RETAINED_HANDLE")){
  library=LoadLibraryA(argv[1]);if(!library)return 6;
  uint32_t tag=SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1,version=SIMPLE_BACKEND_BRIDGE_VERSION_V1;
  uint64_t handle=(uint64_t)(uintptr_t)library;
  memcpy(handle_packet,&tag,4);memcpy(handle_packet+4,&version,4);memcpy(handle_packet+8,&handle,8);
  path=boxed(handle_packet,sizeof(handle_packet));
 }
#endif
 TestBytes*out=(TestBytes*)(uintptr_t)spl_backend_plugin_run_v1((int64_t)(uintptr_t)&path,(int64_t)(uintptr_t)&req,(int64_t)(uintptr_t)&m);
 if(!out||out->len<32)return 3;
 uint32_t magic=0,status=1,kind=0;uint64_t pn=0,dn=0;
 memcpy(&magic,out->data,4);memcpy(&status,out->data+8,4);memcpy(&kind,out->data+12,4);memcpy(&pn,out->data+16,8);memcpy(&dn,out->data+24,8);
 if(magic!=SIMPLE_BACKEND_BRIDGE_MAGIC_V1||status!=(uint32_t)expected)return 4;
 if(expected==0&&(kind!=2||pn!=9||dn!=18||memcmp(out->data+32,"object-ok",9)||memcmp(out->data+41,"fixture-diagnostic",18)))return 5;
 free(out->data);free(out);
#ifdef _WIN32
 if(library){
  if(!GetProcAddress(library,SIMPLE_BACKEND_PLUGIN_ENTRY_V1))return 7;
  const char*marker=getenv("SBP_FIXTURE_UNLOAD_MARKER");
  if(marker&&GetFileAttributesA(marker)!=INVALID_FILE_ATTRIBUTES)return 8;
  if(!FreeLibrary(library))return 9;
 }
#endif
 puts("PASS backend-plugin-v1 native bridge");return 0;
}
