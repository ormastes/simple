#include "runtime.h"
#include "../compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifndef _WIN32
#include <dlfcn.h>
#endif

static const uint8_t *boxed_bytes(int64_t value, int64_t *len) {
    *len = rt_array_len_safe(value);
    if (*len < 0) return NULL;
    return (const uint8_t *)(uintptr_t)
        rt_array_data_ptr((SplArray *)(uintptr_t)value);
}

static int64_t bridge_envelope(int32_t status, uint32_t kind,
    const uint8_t *payload, uint64_t payload_len,
    const uint8_t *diagnostic, uint64_t diagnostic_len) {
    uint64_t total = SIMPLE_BACKEND_BRIDGE_HEADER_SIZE_V1 + payload_len + diagnostic_len;
    if (total > INT64_MAX || total < payload_len) return rt_bytes_from_raw(0, 0);
    uint8_t *wire = (uint8_t *)calloc(1, (size_t)total);
    if (!wire) return rt_bytes_from_raw(0, 0);
    uint32_t magic = SIMPLE_BACKEND_BRIDGE_MAGIC_V1, version = 1;
    memcpy(wire, &magic, 4); memcpy(wire + 4, &version, 4);
    memcpy(wire + 8, &status, 4); memcpy(wire + 12, &kind, 4);
    memcpy(wire + 16, &payload_len, 8); memcpy(wire + 24, &diagnostic_len, 8);
    if (payload_len) memcpy(wire + 32, payload, (size_t)payload_len);
    if (diagnostic_len) memcpy(wire + 32 + payload_len, diagnostic, (size_t)diagnostic_len);
    int64_t result = rt_bytes_from_raw((int64_t)(uintptr_t)wire, (int64_t)total);
    free(wire); return result;
}

/* Request wire prefix v1: abi:u32, role:u32, capabilities:u64. */
int64_t spl_backend_plugin_run_v1(int64_t path_value, int64_t request_value,
                                  int64_t mir_value) {
    int64_t path_len=0, request_len=0, mir_len=0;
    const uint8_t *path_bytes=boxed_bytes(path_value,&path_len);
    const uint8_t *request=boxed_bytes(request_value,&request_len);
    const uint8_t *mir=boxed_bytes(mir_value,&mir_len);
    if (!path_bytes || path_len <= 0 || !request || request_len < 16 || !mir || mir_len <= 0)
        return bridge_envelope(100,0,NULL,0,NULL,0);
    char *path=(char *)malloc((size_t)path_len+1);
    if (!path) return bridge_envelope(101,0,NULL,0,NULL,0);
    memcpy(path,path_bytes,(size_t)path_len); path[path_len]=0;
    uint32_t abi=0,role=0; uint64_t caps=0;
    memcpy(&abi,request,4); memcpy(&role,request+4,4); memcpy(&caps,request+8,8);
#ifdef _WIN32
    free(path); return bridge_envelope(102,0,NULL,0,NULL,0);
#else
    void *library=dlopen(path,RTLD_NOW|RTLD_LOCAL); free(path);
    if (!library) return bridge_envelope(103,0,NULL,0,NULL,0);
    union { void *object; simple_backend_plugin_entry_v1_fn function; } entry;
    entry.object=dlsym(library,SIMPLE_BACKEND_PLUGIN_ENTRY_V1);
    if (!entry.object) { dlclose(library); return bridge_envelope(104,0,NULL,0,NULL,0); }
    const simple_backend_descriptor_v1 *descriptor=entry.function();
    if (!descriptor || abi != 1 || descriptor->abi_version != 1 ||
        descriptor->struct_size < sizeof(*descriptor) || !descriptor->vtable ||
        descriptor->vtable->abi_version != 1 ||
        descriptor->vtable->struct_size < sizeof(*descriptor->vtable)) {
        dlclose(library); return bridge_envelope(105,0,NULL,0,NULL,0);
    }
    const simple_backend_vtable_v1 *v=descriptor->vtable;
    simple_backend_request_v1 req={0}; req.abi_version=abi;
    req.struct_size=sizeof(req); req.role=role; req.required_capabilities=caps;
    uint64_t session=0; int32_t status=v->open_session(&req,&session);
    if (status || !session) { dlclose(library); return bridge_envelope(status?status:106,0,NULL,0,NULL,0); }
    simple_backend_compile_result_v1 module={0}, object={0};
    simple_backend_owned_buffer_v1 diagnostic={0};
    status=v->compile_module(session,(simple_backend_slice_v1){mir,(uint64_t)mir_len},&module);
    if (!status) status=v->finalize_object(session,&object);
    if (!status) status=v->diagnostics(session,&diagnostic);
    int64_t result=bridge_envelope(status,object.result_kind,
        status?NULL:object.payload.data,status?0:object.payload.size,
        diagnostic.data,diagnostic.size);
    if (module.payload.data) v->release_buffer(session,module.payload);
    if (object.payload.data) v->release_buffer(session,object.payload);
    if (diagnostic.data) v->release_buffer(session,diagnostic);
    int32_t close_status=v->close_session(session); dlclose(library);
    if (close_status) return bridge_envelope(close_status,0,NULL,0,NULL,0);
    return result;
#endif
}
