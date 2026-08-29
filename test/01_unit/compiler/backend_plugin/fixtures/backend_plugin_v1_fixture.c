#include "simple_backend_plugin_v1.h"
#include <stdlib.h>
#include <string.h>
static int releases;
static int32_t owned(const char *s, uint32_t kind, simple_backend_compile_result_v1 *out) {
    size_t n = strlen(s); uint8_t *p = malloc(n ? n : 1); if (!p) return 12;
    memcpy(p, s, n); out->abi_version=1; out->struct_size=sizeof(*out);
    out->result_kind=kind; out->status=0; out->payload=(simple_backend_owned_buffer_v1){p,n,(uint64_t)(uintptr_t)p}; return 0;
}
static int32_t open_(const simple_backend_request_v1 *r,uint64_t *s){if(!r||!s||r->abi_version!=1||r->struct_size<sizeof(*r))return 20;*s=0x51A7E;return 0;}
static int32_t compile_(uint64_t s,simple_backend_slice_v1 m,simple_backend_compile_result_v1 *o){if(s!=0x51A7E||!m.data||m.size!=4)return 21;return owned("module-ok",1,o);}
static int32_t finalize_(uint64_t s,simple_backend_compile_result_v1 *o){return s==0x51A7E?owned("object-ok",2,o):22;}
static int32_t diagnostics_(uint64_t s,simple_backend_owned_buffer_v1 *o){simple_backend_compile_result_v1 r;int32_t rc=owned("fixture-diagnostic",0,&r);if(!rc)*o=r.payload;return s==0x51A7E?rc:23;}
static int32_t release_(uint64_t s,simple_backend_owned_buffer_v1 b){if(s!=0x51A7E||!b.data||b.owner_token!=(uint64_t)(uintptr_t)b.data)return 24;free((void*)b.data);releases++;return 0;}
static int32_t close_(uint64_t s){return s==0x51A7E&&releases==3?0:25;}
static const simple_backend_vtable_v1 vt={1,sizeof(vt),open_,compile_,finalize_,diagnostics_,close_,release_};
static const uint8_t id[]="fixture",ver[]="1.0.0",build[]="fixture-build",digest[]="mir-v1",targets[]="4:host";
static const simple_backend_descriptor_v1 desc={1,sizeof(desc),{id,sizeof(id)-1},{ver,sizeof(ver)-1},{build,sizeof(build)-1},{digest,sizeof(digest)-1},2,2,{targets,sizeof(targets)-1},&vt};
const simple_backend_descriptor_v1 *simple_backend_plugin_v1(void){return &desc;}
