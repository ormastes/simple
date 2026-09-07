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

#ifndef _WIN32
typedef struct {
    void *library;
    const simple_backend_vtable_v1 *vtable;
    uint64_t provider_session;
    int owns_library;
    int finalized;
} simple_backend_bridge_batch_v1;

static int32_t bridge_resolve_provider(const uint8_t *provider,
                                       int64_t provider_len,
                                       void **library_out,
                                       int *owns_library_out,
                                       const simple_backend_vtable_v1 **vtable_out) {
    void *library = NULL;
    int owns_library = 0;
    uint32_t provider_magic = 0;
    if (provider_len >= 4) memcpy(&provider_magic, provider, 4);
    if (provider_magic == SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1) {
        uint32_t provider_version = 0;
        uint64_t handle = 0;
        if (provider_len != SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_SIZE_V1) return 107;
        memcpy(&provider_version, provider + 4, 4);
        memcpy(&handle, provider + 8, 8);
        if (provider_version != SIMPLE_BACKEND_BRIDGE_VERSION_V1 || !handle) return 107;
        library = (void *)(uintptr_t)handle;
    } else {
        char *path = (char *)malloc((size_t)provider_len + 1);
        if (!path) return 101;
        memcpy(path, provider, (size_t)provider_len);
        path[provider_len] = 0;
        library = dlopen(path, RTLD_NOW | RTLD_LOCAL);
        free(path);
        if (!library) return 103;
        owns_library = 1;
    }
    union { void *object; simple_backend_plugin_entry_v1_fn function; } entry;
    entry.object = dlsym(library, SIMPLE_BACKEND_PLUGIN_ENTRY_V1);
    if (!entry.object) {
        if (owns_library) dlclose(library);
        return 104;
    }
    const simple_backend_descriptor_v1 *descriptor = entry.function();
    if (!descriptor || descriptor->abi_version != 1 ||
        descriptor->struct_size < sizeof(*descriptor) || !descriptor->vtable ||
        descriptor->vtable->abi_version != 1 ||
        descriptor->vtable->struct_size < sizeof(*descriptor->vtable) ||
        !descriptor->vtable->open_session || !descriptor->vtable->compile_module ||
        !descriptor->vtable->finalize_object || !descriptor->vtable->diagnostics ||
        !descriptor->vtable->close_session || !descriptor->vtable->release_buffer) {
        if (owns_library) dlclose(library);
        return 105;
    }
    *library_out = library;
    *owns_library_out = owns_library;
    *vtable_out = descriptor->vtable;
    return 0;
}
#endif

/* Execute against one already-open library. Handle ownership remains with the
 * caller, so every return below leaves exactly one owner responsible for it. */
#ifndef _WIN32
static int64_t bridge_run_loaded(void *library, uint32_t abi, uint32_t role,
                                 uint64_t caps, const uint8_t *mir,
                                 int64_t mir_len) {
    union { void *object; simple_backend_plugin_entry_v1_fn function; } entry;
    entry.object=dlsym(library,SIMPLE_BACKEND_PLUGIN_ENTRY_V1);
    if (!entry.object) return bridge_envelope(104,0,NULL,0,NULL,0);
    const simple_backend_descriptor_v1 *descriptor=entry.function();
    if (!descriptor || abi != 1 || descriptor->abi_version != 1 ||
        descriptor->struct_size < sizeof(*descriptor) || !descriptor->vtable ||
        descriptor->vtable->abi_version != 1 ||
        descriptor->vtable->struct_size < sizeof(*descriptor->vtable) ||
        !descriptor->vtable->open_session ||
        !descriptor->vtable->compile_module ||
        !descriptor->vtable->finalize_object ||
        !descriptor->vtable->diagnostics ||
        !descriptor->vtable->close_session ||
        !descriptor->vtable->release_buffer)
        return bridge_envelope(105,0,NULL,0,NULL,0);
    const simple_backend_vtable_v1 *v=descriptor->vtable;
    simple_backend_request_v1 req={0}; req.abi_version=abi;
    req.struct_size=sizeof(req); req.role=role; req.required_capabilities=caps;
    uint64_t session=0; int32_t status=v->open_session(&req,&session);
    if (status || !session)
        return bridge_envelope(status?status:106,0,NULL,0,NULL,0);
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
    int32_t close_status=v->close_session(session);
    if (close_status) return bridge_envelope(close_status,0,NULL,0,NULL,0);
    return result;
}
#endif

/* Request wire prefix v1: abi:u32, role:u32, capabilities:u64.
 *
 * ABI compatibility is deliberate: legacy callers may still supply untagged
 * path bytes. Production admission supplies the tagged retained-handle packet,
 * which never calls dlopen and therefore cannot reopen substituted path bytes.
 */
int64_t spl_backend_plugin_run_v1(int64_t provider_value,
                                  int64_t request_value,
                                  int64_t mir_value) {
    int64_t provider_len=0, request_len=0, mir_len=0;
    const uint8_t *provider=boxed_bytes(provider_value,&provider_len);
    const uint8_t *request=boxed_bytes(request_value,&request_len);
    const uint8_t *mir=boxed_bytes(mir_value,&mir_len);
    if (!provider || provider_len <= 0 || !request || request_len < 16 ||
        !mir || mir_len <= 0)
        return bridge_envelope(100,0,NULL,0,NULL,0);
    uint32_t abi=0,role=0; uint64_t caps=0;
    memcpy(&abi,request,4); memcpy(&role,request+4,4); memcpy(&caps,request+8,8);
#ifdef _WIN32
    return bridge_envelope(102,0,NULL,0,NULL,0);
#else
    void *library=NULL;
    int close_library=0;
    uint32_t provider_magic=0;
    if (provider_len >= 4) memcpy(&provider_magic,provider,4);
    if (provider_magic == SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_MAGIC_V1) {
        uint32_t provider_version=0; uint64_t handle=0;
        if (provider_len != SIMPLE_BACKEND_BRIDGE_PROVIDER_HANDLE_SIZE_V1)
            return bridge_envelope(107,0,NULL,0,NULL,0);
        memcpy(&provider_version,provider+4,4);
        memcpy(&handle,provider+8,8);
        if (provider_version != SIMPLE_BACKEND_BRIDGE_VERSION_V1 || !handle)
            return bridge_envelope(107,0,NULL,0,NULL,0);
        library=(void *)(uintptr_t)handle;
    } else {
        char *path=(char *)malloc((size_t)provider_len+1);
        if (!path) return bridge_envelope(101,0,NULL,0,NULL,0);
        memcpy(path,provider,(size_t)provider_len); path[provider_len]=0;
        library=dlopen(path,RTLD_NOW|RTLD_LOCAL);
        free(path);
        if (!library) return bridge_envelope(103,0,NULL,0,NULL,0);
        close_library=1;
    }
    int64_t result=bridge_run_loaded(library,abi,role,caps,mir,mir_len);
    if (close_library) dlclose(library);
    return result;
#endif
}

int64_t spl_backend_plugin_batch_open_v1(int64_t provider_value,
                                         int64_t request_value) {
#ifdef _WIN32
    (void)provider_value; (void)request_value;
    return -102;
#else
    int64_t provider_len = 0, request_len = 0;
    const uint8_t *provider = boxed_bytes(provider_value, &provider_len);
    const uint8_t *request = boxed_bytes(request_value, &request_len);
    if (!provider || provider_len <= 0 || !request || request_len < 16) return -100;
    uint32_t abi = 0, role = 0;
    uint64_t caps = 0;
    memcpy(&abi, request, 4); memcpy(&role, request + 4, 4); memcpy(&caps, request + 8, 8);
    if (abi != SIMPLE_BACKEND_PLUGIN_ABI_V1) return -105;
    simple_backend_bridge_batch_v1 *batch = calloc(1, sizeof(*batch));
    if (!batch) return -101;
    int32_t status = bridge_resolve_provider(provider, provider_len, &batch->library,
                                             &batch->owns_library, &batch->vtable);
    if (status) { free(batch); return -(int64_t)status; }
    simple_backend_request_v1 req = {0};
    req.abi_version = abi; req.struct_size = sizeof(req); req.role = role;
    req.required_capabilities = caps;
    status = batch->vtable->open_session(&req, &batch->provider_session);
    if (status || !batch->provider_session) {
        if (batch->owns_library) dlclose(batch->library);
        free(batch);
        return -(int64_t)(status ? status : 106);
    }
    return (int64_t)(uintptr_t)batch;
#endif
}

int64_t spl_backend_plugin_batch_compile_v1(int64_t batch_handle,
                                            int64_t mir_value) {
#ifdef _WIN32
    (void)batch_handle; (void)mir_value;
    return bridge_envelope(102, 0, NULL, 0, NULL, 0);
#else
    simple_backend_bridge_batch_v1 *batch =
        (simple_backend_bridge_batch_v1 *)(uintptr_t)batch_handle;
    int64_t mir_len = 0;
    const uint8_t *mir = boxed_bytes(mir_value, &mir_len);
    if (!batch || !mir || mir_len <= 0 || batch->finalized)
        return bridge_envelope(108, 0, NULL, 0, NULL, 0);
    simple_backend_compile_result_v1 module = {0};
    int32_t status = batch->vtable->compile_module(
        batch->provider_session, (simple_backend_slice_v1){mir, (uint64_t)mir_len}, &module);
    int64_t result = bridge_envelope(status, module.result_kind,
        status ? NULL : module.payload.data, status ? 0 : module.payload.size, NULL, 0);
    if (module.payload.data)
        batch->vtable->release_buffer(batch->provider_session, module.payload);
    return result;
#endif
}

int64_t spl_backend_plugin_batch_finalize_v1(int64_t batch_handle) {
#ifdef _WIN32
    (void)batch_handle;
    return bridge_envelope(102, 0, NULL, 0, NULL, 0);
#else
    simple_backend_bridge_batch_v1 *batch =
        (simple_backend_bridge_batch_v1 *)(uintptr_t)batch_handle;
    if (!batch || batch->finalized)
        return bridge_envelope(108, 0, NULL, 0, NULL, 0);
    batch->finalized = 1;
    simple_backend_compile_result_v1 object = {0};
    simple_backend_owned_buffer_v1 diagnostic = {0};
    int32_t status = batch->vtable->finalize_object(batch->provider_session, &object);
    if (!status) status = batch->vtable->diagnostics(batch->provider_session, &diagnostic);
    int64_t result = bridge_envelope(status, object.result_kind,
        status ? NULL : object.payload.data, status ? 0 : object.payload.size,
        diagnostic.data, diagnostic.size);
    if (object.payload.data)
        batch->vtable->release_buffer(batch->provider_session, object.payload);
    if (diagnostic.data)
        batch->vtable->release_buffer(batch->provider_session, diagnostic);
    return result;
#endif
}

int32_t spl_backend_plugin_batch_close_v1(int64_t batch_handle) {
#ifdef _WIN32
    (void)batch_handle;
    return 102;
#else
    simple_backend_bridge_batch_v1 *batch =
        (simple_backend_bridge_batch_v1 *)(uintptr_t)batch_handle;
    if (!batch) return 108;
    int32_t status = batch->vtable->close_session(batch->provider_session);
    if (batch->owns_library && dlclose(batch->library) != 0 && !status) status = 109;
    free(batch);
    return status;
#endif
}
