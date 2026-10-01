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
int main(int argc,char**argv){
 if(argc<3)return 2;
 int expected=atoi(argv[2]);
 uint8_t request[16]={1,0,0,0,2,0,0,0,2,0,0,0,0,0,0,0};
 uint8_t mir[4]={'M','I','R','1'};
 int64_t request_len=(argc>3&&strcmp(argv[3],"bad-request")==0)?8:16;
 int64_t mir_len=(argc>3&&strcmp(argv[3],"bad-mir")==0)?0:4;
 TestBytes path=boxed((uint8_t*)argv[1],strlen(argv[1])),req=boxed(request,request_len),m=boxed(mir,mir_len);
 TestBytes*out=(TestBytes*)(uintptr_t)spl_backend_plugin_run_v1((int64_t)(uintptr_t)&path,(int64_t)(uintptr_t)&req,(int64_t)(uintptr_t)&m);
 if(!out||out->len<32)return 3;
 uint32_t magic=0,status=1,kind=0;uint64_t pn=0,dn=0;
 memcpy(&magic,out->data,4);memcpy(&status,out->data+8,4);memcpy(&kind,out->data+12,4);memcpy(&pn,out->data+16,8);memcpy(&dn,out->data+24,8);
 if(magic!=SIMPLE_BACKEND_BRIDGE_MAGIC_V1||status!=(uint32_t)expected)return 4;
 if(expected==0&&(kind!=2||pn!=9||dn!=18||memcmp(out->data+32,"object-ok",9)||memcmp(out->data+41,"fixture-diagnostic",18)))return 5;
 puts("PASS backend-plugin-v1 native bridge");return 0;
}
