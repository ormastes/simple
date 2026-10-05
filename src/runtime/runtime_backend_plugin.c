#include "runtime.h"
#include "../compiler/70.backend/backend_plugin/abi/simple_backend_plugin_v1.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#else
#include <dlfcn.h>
#endif

/* Keep platform operations separate from session/buffer ownership. Admitted
 * handle packets borrow their mapping; only legacy path loads are owned here. */
static void *bridge_library_open(const char *path) {
#ifdef _WIN32
    int count = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, NULL, 0);
    if (!count || (size_t)count > SIZE_MAX / sizeof(wchar_t)) return NULL;
    wchar_t *wide = malloc((size_t)count * sizeof(*wide));
    if (!wide) return NULL;
    HMODULE library = NULL;
    if (MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, wide, count))
        library = LoadLibraryW(wide);
    free(wide);
    return (void *)library;
#else
    return dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

static simple_backend_plugin_entry_v1_fn bridge_library_entry(void *library) {
#ifdef _WIN32
    union { FARPROC symbol; simple_backend_plugin_entry_v1_fn function; } entry;
    entry.symbol = GetProcAddress((HMODULE)library, SIMPLE_BACKEND_PLUGIN_ENTRY_V1);
#else
    union { void *symbol; simple_backend_plugin_entry_v1_fn function; } entry;
    entry.symbol = dlsym(library, SIMPLE_BACKEND_PLUGIN_ENTRY_V1);
#endif
    return entry.function;
}

static int bridge_library_close(void *library) {
#ifdef _WIN32
    return FreeLibrary((HMODULE)library) ? 0 : -1;
#else
    return dlclose(library);
#endif
}

static uint32_t bridge_read_u32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
        ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}

/* Strict UTF-8, no NUL. Bounded once by the enclosing packet/field limits. */
static int bridge_request_text(const uint8_t *p, size_t n) {
    for (size_t i = 0; i < n;) {
        uint32_t c = p[i++], value; size_t more;
        if (!c) return 0;
        if (c < 0x80) continue;
        if (c >= 0xc2 && c <= 0xdf) { value = c & 31; more = 1; }
        else if (c >= 0xe0 && c <= 0xef) { value = c & 15; more = 2; }
        else if (c >= 0xf0 && c <= 0xf4) { value = c & 7; more = 3; }
        else return 0;
        if (more > n - i) return 0;
        for (size_t j = 0; j < more; ++j) {
            if ((p[i] & 0xc0) != 0x80) return 0;
            value = (value << 6) | (p[i++] & 63);
        }
        if ((more == 1 && value < 0x80) || (more == 2 && value < 0x800) ||
            (more == 3 && value < 0x10000) || value > 0x10ffff ||
            (value >= 0xd800 && value <= 0xdfff)) return 0;
    }
    return 1;
}

static int bridge_request_decode(const uint8_t *p, int64_t length,
                                  simple_backend_request_v1 *request) {
    if (!p || length < SIMPLE_BACKEND_REQUEST_HEADER_SIZE_V1 ||
        length > SIMPLE_BACKEND_REQUEST_MAX_V1) return 0;
    if (bridge_read_u32(p) != SIMPLE_BACKEND_REQUEST_MAGIC_V1 ||
        bridge_read_u32(p + 4) != SIMPLE_BACKEND_REQUEST_VERSION_V1 ||
        bridge_read_u32(p + 8) != SIMPLE_BACKEND_PLUGIN_ABI_V1) return 0;
    uint32_t role = bridge_read_u32(p + 12);
    uint64_t caps = bridge_read_u32(p + 16) | ((uint64_t)bridge_read_u32(p + 20) << 32);
    if ((role != 1 && role != 2) || (caps & ~UINT64_C(63))) return 0;
    simple_backend_slice_v1 fields[6];
    size_t offset = SIMPLE_BACKEND_REQUEST_HEADER_SIZE_V1, total = (size_t)length;
    for (size_t field = 0; field < 6; ++field) {
        size_t n = bridge_read_u32(p + 24 + field * 4);
        if (n > (field == 3 ? 32768u : 4096u) || n > total - offset) return 0;
        fields[field] = (simple_backend_slice_v1){p + offset, n};
        if (field == 3) {
            if (n < 4) return 0;
            uint32_t count = bridge_read_u32(p + offset);
            if (count > 128) return 0;
            size_t cursor = offset + 4, end = offset + n;
            for (uint32_t item = 0; item < count; ++item) {
                if (end - cursor < 4) return 0;
                size_t size = bridge_read_u32(p + cursor); cursor += 4;
                if (!size || size > 4096 || size > end - cursor ||
                    !bridge_request_text(p + cursor, size)) return 0;
                cursor += size;
            }
            if (cursor != end) return 0;
        } else if ((!n && field != 2) || !bridge_request_text(p + offset, n)) return 0;
        offset += n;
    }
    if (offset != total) return 0;
    *request = (simple_backend_request_v1){0};
    request->abi_version = SIMPLE_BACKEND_PLUGIN_ABI_V1;
    request->struct_size = sizeof(*request); request->role = role;
    request->required_capabilities = caps;
    request->backend_name = fields[0]; request->target = fields[1];
    request->cpu = fields[2]; request->features_wire = fields[3];
    request->optimization = fields[4]; request->mir_abi_digest = fields[5];
    return 1;
}

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
        library = bridge_library_open(path);
        free(path);
        if (!library) return 103;
        owns_library = 1;
    }
    simple_backend_plugin_entry_v1_fn entry = bridge_library_entry(library);
    if (!entry) {
        if (owns_library) bridge_library_close(library);
        return 104;
    }
    const simple_backend_descriptor_v1 *descriptor = entry();
    if (!descriptor || descriptor->abi_version != 1 ||
        descriptor->struct_size < sizeof(*descriptor) || !descriptor->vtable ||
        descriptor->vtable->abi_version != 1 ||
        descriptor->vtable->struct_size < sizeof(*descriptor->vtable) ||
        !descriptor->vtable->open_session || !descriptor->vtable->compile_module ||
        !descriptor->vtable->finalize_object || !descriptor->vtable->diagnostics ||
        !descriptor->vtable->close_session || !descriptor->vtable->release_buffer) {
        if (owns_library) bridge_library_close(library);
        return 105;
    }
    *library_out = library;
    *owns_library_out = owns_library;
    *vtable_out = descriptor->vtable;
    return 0;
}

/* Execute against one already-open library. Handle ownership remains with the
 * caller, so every return below leaves exactly one owner responsible for it. */
static int64_t bridge_run_loaded(void *library, const simple_backend_request_v1 *request,
                                 const uint8_t *mir,
                                 int64_t mir_len) {
    simple_backend_plugin_entry_v1_fn entry=bridge_library_entry(library);
    if (!entry) return bridge_envelope(104,0,NULL,0,NULL,0);
    const simple_backend_descriptor_v1 *descriptor=entry();
    if (!descriptor || descriptor->abi_version != 1 ||
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
    uint64_t session=0; int32_t status=v->open_session(request,&session);
    if (status || !session)
        return bridge_envelope(status?status:106,0,NULL,0,NULL,0);
    simple_backend_compile_result_v1 module={0}, object={0};
    simple_backend_owned_buffer_v1 diagnostic={0};
    status=v->compile_module(session,(simple_backend_slice_v1){mir,(uint64_t)mir_len},&module);
    if (!status) status=v->finalize_object(session,&object);
    /* Diagnostics describe both successful and failed provider operations.
     * Calling this only on success erased the real compile/finalize failure
     * and reduced the caller's evidence to an opaque scalar status. Preserve
     * the primary failure while still collecting its provider-owned message. */
    int32_t diagnostic_status=v->diagnostics(session,&diagnostic);
    if (!status && diagnostic_status) status=diagnostic_status;
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

/* Complete versioned request is decoded before loading a provider.
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
    simple_backend_request_v1 decoded;
    if (!provider || provider_len <= 0 || !bridge_request_decode(request, request_len, &decoded) ||
        !mir || mir_len <= 0)
        return bridge_envelope(100,0,NULL,0,NULL,0);
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
        library=bridge_library_open(path);
        free(path);
        if (!library) return bridge_envelope(103,0,NULL,0,NULL,0);
        close_library=1;
    }
    int64_t result=bridge_run_loaded(library,&decoded,mir,mir_len);
    if (close_library) bridge_library_close(library);
    return result;
}

int64_t spl_backend_plugin_batch_open_v1(int64_t provider_value,
                                         int64_t request_value) {
    int64_t provider_len = 0, request_len = 0;
    const uint8_t *provider = boxed_bytes(provider_value, &provider_len);
    const uint8_t *request = boxed_bytes(request_value, &request_len);
    simple_backend_request_v1 req;
    if (!provider || provider_len <= 0 || !bridge_request_decode(request, request_len, &req)) return -100;
    simple_backend_bridge_batch_v1 *batch = calloc(1, sizeof(*batch));
    if (!batch) return -101;
    int32_t status = bridge_resolve_provider(provider, provider_len, &batch->library,
                                             &batch->owns_library, &batch->vtable);
    if (status) { free(batch); return -(int64_t)status; }
    status = batch->vtable->open_session(&req, &batch->provider_session);
    if (status || !batch->provider_session) {
        if (batch->owns_library) bridge_library_close(batch->library);
        free(batch);
        return -(int64_t)(status ? status : 106);
    }
    return (int64_t)(uintptr_t)batch;
}

int64_t spl_backend_plugin_batch_compile_v1(int64_t batch_handle,
                                            int64_t mir_value) {
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
}

int64_t spl_backend_plugin_batch_finalize_v1(int64_t batch_handle) {
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
}

int32_t spl_backend_plugin_batch_close_v1(int64_t batch_handle) {
    simple_backend_bridge_batch_v1 *batch =
        (simple_backend_bridge_batch_v1 *)(uintptr_t)batch_handle;
    if (!batch) return 108;
    int32_t status = batch->vtable->close_session(batch->provider_session);
    if (batch->owns_library && bridge_library_close(batch->library) != 0 && !status) status = 109;
    free(batch);
    return status;
}
