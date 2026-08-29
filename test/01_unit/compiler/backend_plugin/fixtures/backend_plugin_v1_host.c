#include "simple_backend_plugin_v1.h"
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
static int eq(simple_backend_owned_buffer_v1 b,const char*s){return b.size==strlen(s)&&memcmp(b.data,s,b.size)==0;}
int main(int argc,char**argv){
 if(argc!=2)return 2;
 void*l=dlopen(argv[1],RTLD_NOW|RTLD_LOCAL);if(!l)return 3;
 union{void*object;simple_backend_plugin_entry_v1_fn function;}e;
 e.object=dlsym(l,SIMPLE_BACKEND_PLUGIN_ENTRY_V1);if(!e.object)return 4;
 const simple_backend_descriptor_v1*d=e.function();if(!d||d->abi_version!=1||d->struct_size<sizeof(*d)||!d->vtable||d->vtable->abi_version!=1||d->vtable->struct_size<sizeof(*d->vtable))return 5;
 simple_backend_request_v1 r={0};r.abi_version=1;r.struct_size=sizeof(r);r.role=2;uint64_t s=0;if(d->vtable->open_session(&r,&s)||!s)return 6;
 const uint8_t mir[]={'M','I','R','1'};simple_backend_compile_result_v1 m={0},o={0};simple_backend_owned_buffer_v1 g={0};
 if(d->vtable->compile_module(s,(simple_backend_slice_v1){mir,4},&m)||m.abi_version!=1||m.struct_size<sizeof(m)||m.result_kind!=1||!eq(m.payload,"module-ok"))return 7;
 if(d->vtable->finalize_object(s,&o)||o.result_kind!=2||!eq(o.payload,"object-ok"))return 8;
 if(d->vtable->diagnostics(s,&g)||!eq(g,"fixture-diagnostic"))return 9;
 if(d->vtable->release_buffer(s,m.payload)||d->vtable->release_buffer(s,o.payload)||d->vtable->release_buffer(s,g))return 10;
 if(d->vtable->close_session(s))return 11;
 dlclose(l);puts("PASS backend-plugin-v1 typed fixture");return 0;
}
