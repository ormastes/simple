/* Counterpart conformance — narrow native runtime shim.
 *
 * This is the ONLY place that touches dlopen/dlsym, scf_api_v1 function
 * pointers, and raw provider buffers. The Simple side (see
 * src/lib/nogc_sync_mut/sffi/counterpart_abi.spl) sees a flat API of int64
 * handles and text values: no function pointers and no upstream types ever
 * cross into Simple.
 *
 * Responsibilities:
 *   - dlopen/dlsym of the one bootstrap symbol `scf_get_api`
 *   - ABI negotiation: reject a table whose abi_version or struct_size does not
 *     match what this shim was compiled against
 *   - own the scf_writer_v1 growable buffer, so the adapter allocates nothing
 *     the caller must free
 *   - hand out opaque int64 instance handles, never pointers
 *   - never trust a returned pointer without its length
 *
 * NOT in scope: crash containment. An in-process adapter that abort()s takes
 * this process with it. Crash containment is the isolated worker (F3); this
 * shim only reports what it can observe in-process.
 *
 * Design: doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md §3
 */

#include "../../tools/counterpart/sdk/c/simple_counterpart_abi.h"

#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <dlfcn.h>
#endif

/* When built inside the runtime we box text through the interpreter's string
 * representation; standalone (unit compile of this file alone) we degrade to
 * stubs so the file always builds with `cc -c -std=c99 -Wall -Wextra`. */
#if defined(__has_include)
#  if __has_include("runtime.h")
#    include "runtime.h"
#    define SCF_HAVE_RUNTIME 1
#  endif
#endif

#ifndef SCF_HAVE_RUNTIME
#define SCF_HAVE_RUNTIME 0
extern int64_t rt_string_new(const uint8_t *bytes, uint64_t len);
extern const char *rt_interp_cstr(int64_t value);
extern int64_t rt_core_nil(void);
#endif

/* ------------------------------------------------------------------------ */
/* Shim status codes                                                         */
/* ------------------------------------------------------------------------ */
/* 0 and the positive SCF_* codes come straight from the adapter. Negative
 * codes are the shim's own; they describe loading and handle problems the
 * adapter never sees. Kept distinct so a load failure is never reported as an
 * adapter-level OK. */

#define SCF_RT_OK                    0
#define SCF_RT_ERR_BAD_ARG         (-1)
#define SCF_RT_ERR_DLOPEN          (-2)
#define SCF_RT_ERR_NO_SYMBOL       (-3)
#define SCF_RT_ERR_NULL_API        (-4)
#define SCF_RT_ERR_ABI_VERSION     (-5)
#define SCF_RT_ERR_STRUCT_SIZE     (-6)
#define SCF_RT_ERR_INCOMPLETE_API  (-7)
#define SCF_RT_ERR_OPEN_FAILED     (-8)
#define SCF_RT_ERR_BAD_HANDLE      (-9)
#define SCF_RT_ERR_OOM            (-10)
#define SCF_RT_ERR_WRITER         (-11)

/* ------------------------------------------------------------------------ */
/* Growable output buffer owned by this shim                                 */
/* ------------------------------------------------------------------------ */

typedef struct {
    uint8_t *data;
    uint64_t length;
    uint64_t capacity;
    int failed;
} scf_buffer;

static void scf_buffer_init(scf_buffer *buffer) {
    buffer->data = NULL;
    buffer->length = 0;
    buffer->capacity = 0;
    buffer->failed = 0;
}

static void scf_buffer_free(scf_buffer *buffer) {
    free(buffer->data);
    scf_buffer_init(buffer);
}

/* Hard ceiling so a runaway adapter cannot exhaust the host. 256 MiB. */
#define SCF_BUFFER_LIMIT ((uint64_t)256u * 1024u * 1024u)

static int32_t scf_buffer_write(void *context, const uint8_t *data, uint64_t size) {
    scf_buffer *buffer = (scf_buffer *)context;
    uint64_t required;
    uint64_t capacity;
    uint8_t *grown;

    if (!buffer) return SCF_INVALID_ARG;
    if (buffer->failed) return SCF_INTERNAL;
    if (size == 0) return SCF_OK;
    if (!data) { buffer->failed = 1; return SCF_INVALID_ARG; }

    required = buffer->length + size;
    if (required < buffer->length || required > SCF_BUFFER_LIMIT) {
        buffer->failed = 1;
        return SCF_INTERNAL;
    }
    if (required > buffer->capacity) {
        capacity = buffer->capacity ? buffer->capacity : 1024u;
        while (capacity < required) {
            if (capacity > SCF_BUFFER_LIMIT / 2u) { capacity = required; break; }
            capacity *= 2u;
        }
        grown = (uint8_t *)realloc(buffer->data, (size_t)capacity);
        if (!grown) { buffer->failed = 1; return SCF_INTERNAL; }
        buffer->data = grown;
        buffer->capacity = capacity;
    }
    memcpy(buffer->data + buffer->length, data, (size_t)size);
    buffer->length = required;
    return SCF_OK;
}

static scf_writer_v1 scf_buffer_writer(scf_buffer *buffer) {
    scf_writer_v1 writer;
    writer.context = buffer;
    writer.write = scf_buffer_write;
    return writer;
}

/* ------------------------------------------------------------------------ */
/* Loaded provider slot                                                      */
/* ------------------------------------------------------------------------ */

typedef struct {
    int in_use;
    void *library;
    const scf_api_v1 *api;
    scf_instance_v1 *instance;
    scf_buffer response;
    scf_buffer trace;
} scf_slot;

#define SCF_MAX_SLOTS 32

static scf_slot g_slots[SCF_MAX_SLOTS];
static char g_last_error[512];

static void scf_set_error(const char *message) {
    size_t length;
    if (!message) { g_last_error[0] = '\0'; return; }
    length = strlen(message);
    if (length >= sizeof(g_last_error)) length = sizeof(g_last_error) - 1u;
    memcpy(g_last_error, message, length);
    g_last_error[length] = '\0';
}

static scf_slot *scf_slot_for(int64_t handle) {
    int64_t index = handle - 1;
    if (index < 0 || index >= SCF_MAX_SLOTS) return NULL;
    if (!g_slots[index].in_use) return NULL;
    return &g_slots[index];
}

static void *scf_dlopen(const char *path) {
#ifdef _WIN32
    return (void *)LoadLibraryA(path);
#else
    return dlopen(path, RTLD_NOW | RTLD_LOCAL);
#endif
}

static void *scf_dlsym(void *library, const char *name) {
#ifdef _WIN32
    return (void *)(intptr_t)GetProcAddress((HMODULE)library, name);
#else
    return dlsym(library, name);
#endif
}

static void scf_dlclose(void *library) {
    if (!library) return;
#ifdef _WIN32
    FreeLibrary((HMODULE)library);
#else
    dlclose(library);
#endif
}

/* ------------------------------------------------------------------------ */
/* Public flat C API                                                         */
/* ------------------------------------------------------------------------ */

/* Duplicate a shim-owned buffer into a caller-owned NUL-terminated block.
 * Callers release it with simple_counterpart_free_buffer. */
static char *scf_export(const uint8_t *data, uint64_t length) {
    char *copy = (char *)malloc((size_t)length + 1u);
    if (!copy) return NULL;
    if (length > 0 && data) memcpy(copy, data, (size_t)length);
    copy[length] = '\0';
    return copy;
}

void simple_counterpart_free_buffer(char *buffer) {
    free(buffer);
}

const char *simple_counterpart_last_error(void) {
    return g_last_error;
}

/* Open an adapter. Returns a positive opaque handle, or a negative
 * SCF_RT_ERR_* code. `config` may be NULL (treated as empty SDN). When
 * `out_err` is non-NULL it receives a caller-owned message on failure. */
int64_t simple_counterpart_open(const char *path, const char *config, char **out_err) {
    int index;
    scf_slot *slot = NULL;
    int64_t handle = 0;
    void *library;
    scf_get_api_fn get_api;
    const scf_api_v1 *api;
    scf_slice_v1 configuration;
    scf_instance_v1 *instance = NULL;
    int32_t status;

    if (out_err) *out_err = NULL;
    scf_set_error("");

    if (!path || path[0] == '\0') {
        scf_set_error("counterpart open: empty library path");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_BAD_ARG;
    }

    for (index = 0; index < SCF_MAX_SLOTS; index++) {
        if (!g_slots[index].in_use) { slot = &g_slots[index]; handle = index + 1; break; }
    }
    if (!slot) {
        scf_set_error("counterpart open: all provider slots in use");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_OOM;
    }

    library = scf_dlopen(path);
    if (!library) {
        scf_set_error("counterpart open: dlopen failed");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_DLOPEN;
    }

    /* Object-pointer to function-pointer conversion is implementation-defined
     * in C99 but required by POSIX dlsym; routed through a union to keep
     * -Wpedantic quiet without a cast that hides intent. */
    {
        union { void *object; scf_get_api_fn function; } bridge;
        bridge.object = scf_dlsym(library, SCF_GET_API_SYMBOL);
        get_api = bridge.function;
    }
    if (!get_api) {
        scf_dlclose(library);
        scf_set_error("counterpart open: library exports no scf_get_api");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_NO_SYMBOL;
    }

    api = get_api(SCF_ABI_V1);
    if (!api) {
        scf_dlclose(library);
        scf_set_error("counterpart open: adapter refused ABI v1");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_NULL_API;
    }
    if (api->abi_version != SCF_ABI_V1) {
        scf_dlclose(library);
        scf_set_error("counterpart open: abi_version mismatch");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_ABI_VERSION;
    }
    /* A smaller table than we compiled against means fields we would read do
     * not exist. Larger is fine: the adapter is newer and we read the v1 prefix. */
    if (api->struct_size < (uint32_t)sizeof(scf_api_v1)) {
        scf_dlclose(library);
        scf_set_error("counterpart open: struct_size smaller than scf_api_v1");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_STRUCT_SIZE;
    }
    if (!api->manifest || !api->open || !api->invoke || !api->reset || !api->close) {
        scf_dlclose(library);
        scf_set_error("counterpart open: function table has null entries");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_INCOMPLETE_API;
    }

    configuration.data = config ? (const uint8_t *)config : NULL;
    configuration.size = config ? (uint64_t)strlen(config) : 0u;

    status = api->open(configuration, &instance);
    if (status != SCF_OK || !instance) {
        scf_dlclose(library);
        scf_set_error("counterpart open: adapter open() failed");
        if (out_err) *out_err = scf_export((const uint8_t *)g_last_error, strlen(g_last_error));
        return SCF_RT_ERR_OPEN_FAILED;
    }

    slot->in_use = 1;
    slot->library = library;
    slot->api = api;
    slot->instance = instance;
    scf_buffer_init(&slot->response);
    scf_buffer_init(&slot->trace);
    return handle;
}

int32_t simple_counterpart_manifest(int64_t handle, char **out, int64_t *out_len) {
    scf_slot *slot = scf_slot_for(handle);
    scf_buffer buffer;
    scf_writer_v1 writer;
    int32_t status;

    if (out) *out = NULL;
    if (out_len) *out_len = 0;
    if (!slot) { scf_set_error("counterpart manifest: bad handle"); return SCF_RT_ERR_BAD_HANDLE; }
    if (!out || !out_len) { scf_set_error("counterpart manifest: null out param"); return SCF_RT_ERR_BAD_ARG; }

    scf_buffer_init(&buffer);
    writer = scf_buffer_writer(&buffer);
    status = slot->api->manifest(&writer);
    if (status != SCF_OK || buffer.failed) {
        scf_buffer_free(&buffer);
        scf_set_error("counterpart manifest: adapter write failed");
        return status != SCF_OK ? status : SCF_RT_ERR_WRITER;
    }
    *out = scf_export(buffer.data, buffer.length);
    *out_len = (int64_t)buffer.length;
    scf_buffer_free(&buffer);
    if (!*out) { *out_len = 0; return SCF_RT_ERR_OOM; }
    return SCF_RT_OK;
}

int32_t simple_counterpart_invoke(int64_t handle,
                                  const char *component,
                                  const char *request,
                                  int64_t request_len,
                                  char **out_response, int64_t *out_response_len,
                                  char **out_trace, int64_t *out_trace_len) {
    scf_slot *slot = scf_slot_for(handle);
    scf_slice_v1 component_slice;
    scf_slice_v1 request_slice;
    scf_writer_v1 response_writer;
    scf_writer_v1 trace_writer;
    int32_t status;

    if (out_response) *out_response = NULL;
    if (out_response_len) *out_response_len = 0;
    if (out_trace) *out_trace = NULL;
    if (out_trace_len) *out_trace_len = 0;

    if (!slot) { scf_set_error("counterpart invoke: bad handle"); return SCF_RT_ERR_BAD_HANDLE; }
    if (!component) { scf_set_error("counterpart invoke: null component"); return SCF_RT_ERR_BAD_ARG; }
    /* Never trust a pointer without its length, and never a length without a
     * pointer. Both halves are validated before anything is read. */
    if (request_len < 0) { scf_set_error("counterpart invoke: negative request length"); return SCF_RT_ERR_BAD_ARG; }
    if (request_len > 0 && !request) { scf_set_error("counterpart invoke: length without buffer"); return SCF_RT_ERR_BAD_ARG; }

    slot->response.length = 0;
    slot->response.failed = 0;
    slot->trace.length = 0;
    slot->trace.failed = 0;

    component_slice.data = (const uint8_t *)component;
    component_slice.size = (uint64_t)strlen(component);
    request_slice.data = (request_len > 0) ? (const uint8_t *)request : NULL;
    request_slice.size = (uint64_t)request_len;

    response_writer = scf_buffer_writer(&slot->response);
    trace_writer = scf_buffer_writer(&slot->trace);

    status = slot->api->invoke(slot->instance, component_slice, request_slice,
                               &response_writer, &trace_writer);
    if (status != SCF_OK) {
        scf_set_error("counterpart invoke: adapter returned a non-ok status");
        return status;
    }
    if (slot->response.failed || slot->trace.failed) {
        scf_set_error("counterpart invoke: output buffer overflowed");
        return SCF_RT_ERR_WRITER;
    }

    if (out_response && out_response_len) {
        *out_response = scf_export(slot->response.data, slot->response.length);
        if (!*out_response) return SCF_RT_ERR_OOM;
        *out_response_len = (int64_t)slot->response.length;
    }
    if (out_trace && out_trace_len) {
        *out_trace = scf_export(slot->trace.data, slot->trace.length);
        if (!*out_trace) return SCF_RT_ERR_OOM;
        *out_trace_len = (int64_t)slot->trace.length;
    }
    return SCF_RT_OK;
}

int32_t simple_counterpart_reset(int64_t handle) {
    scf_slot *slot = scf_slot_for(handle);
    if (!slot) { scf_set_error("counterpart reset: bad handle"); return SCF_RT_ERR_BAD_HANDLE; }
    slot->response.length = 0;
    slot->trace.length = 0;
    return slot->api->reset(slot->instance);
}

int32_t simple_counterpart_close(int64_t handle) {
    scf_slot *slot = scf_slot_for(handle);
    if (!slot) return SCF_RT_ERR_BAD_HANDLE;
    if (slot->api && slot->instance) slot->api->close(slot->instance);
    scf_buffer_free(&slot->response);
    scf_buffer_free(&slot->trace);
    scf_dlclose(slot->library);
    slot->library = NULL;
    slot->api = NULL;
    slot->instance = NULL;
    slot->in_use = 0;
    return SCF_RT_OK;
}

/* ------------------------------------------------------------------------ */
/* Simple-facing value API                                                   */
/* ------------------------------------------------------------------------ */
/* Simple externs cannot express `char**` out-parameters, so the Simple side
 * calls these instead: an i64 status or handle comes back from the action, and
 * the payload is read separately as a boxed text value. Both the native
 * (ptr,len) and interpreter (boxed value) argument conventions used elsewhere
 * in this runtime are provided. */

static int64_t scf_box(const uint8_t *data, uint64_t length) {
    if (!data && length > 0) return rt_string_new((const uint8_t *)"", 0u);
    return rt_string_new(data ? data : (const uint8_t *)"", length);
}

int64_t rt_counterpart_open(const uint8_t *path_ptr, uint64_t path_len,
                            const uint8_t *config_ptr, uint64_t config_len) {
    char *path;
    char *config;
    int64_t result;

    if (!path_ptr || path_len == 0) return SCF_RT_ERR_BAD_ARG;
    path = (char *)malloc((size_t)path_len + 1u);
    if (!path) return SCF_RT_ERR_OOM;
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = '\0';

    config = (char *)malloc((size_t)config_len + 1u);
    if (!config) { free(path); return SCF_RT_ERR_OOM; }
    if (config_len > 0 && config_ptr) memcpy(config, config_ptr, (size_t)config_len);
    config[config_len] = '\0';

    result = simple_counterpart_open(path, config, NULL);
    free(path);
    free(config);
    return result;
}

/* Returns the manifest as boxed text; empty text on any failure, which the
 * Simple wrapper treats as rejected_manifest rather than as an empty pass. */
int64_t rt_counterpart_manifest_text(int64_t handle) {
    scf_slot *slot = scf_slot_for(handle);
    scf_buffer buffer;
    scf_writer_v1 writer;
    int64_t boxed;

    if (!slot) return scf_box((const uint8_t *)"", 0u);
    scf_buffer_init(&buffer);
    writer = scf_buffer_writer(&buffer);
    if (slot->api->manifest(&writer) != SCF_OK || buffer.failed) {
        scf_buffer_free(&buffer);
        return scf_box((const uint8_t *)"", 0u);
    }
    boxed = scf_box(buffer.data, buffer.length);
    scf_buffer_free(&buffer);
    return boxed;
}

/* Invoke, retaining response and trace in the slot. Returns the status; the
 * payloads are then read with rt_counterpart_response_text / _trace_text. */
int64_t rt_counterpart_invoke(int64_t handle,
                              const uint8_t *component_ptr, uint64_t component_len,
                              const uint8_t *request_ptr, uint64_t request_len) {
    scf_slot *slot = scf_slot_for(handle);
    scf_slice_v1 component_slice;
    scf_slice_v1 request_slice;
    scf_writer_v1 response_writer;
    scf_writer_v1 trace_writer;
    int32_t status;

    if (!slot) return SCF_RT_ERR_BAD_HANDLE;
    if (!component_ptr || component_len == 0) return SCF_RT_ERR_BAD_ARG;
    if (request_len > 0 && !request_ptr) return SCF_RT_ERR_BAD_ARG;

    slot->response.length = 0;
    slot->response.failed = 0;
    slot->trace.length = 0;
    slot->trace.failed = 0;

    component_slice.data = component_ptr;
    component_slice.size = component_len;
    request_slice.data = (request_len > 0) ? request_ptr : NULL;
    request_slice.size = request_len;

    response_writer = scf_buffer_writer(&slot->response);
    trace_writer = scf_buffer_writer(&slot->trace);
    status = slot->api->invoke(slot->instance, component_slice, request_slice,
                               &response_writer, &trace_writer);
    if (status != SCF_OK) return (int64_t)status;
    if (slot->response.failed || slot->trace.failed) return SCF_RT_ERR_WRITER;
    return SCF_RT_OK;
}

int64_t rt_counterpart_response_text(int64_t handle) {
    scf_slot *slot = scf_slot_for(handle);
    if (!slot) return scf_box((const uint8_t *)"", 0u);
    return scf_box(slot->response.data, slot->response.length);
}

int64_t rt_counterpart_trace_text(int64_t handle) {
    scf_slot *slot = scf_slot_for(handle);
    if (!slot) return scf_box((const uint8_t *)"", 0u);
    return scf_box(slot->trace.data, slot->trace.length);
}

int64_t rt_counterpart_last_error_text(void) {
    return scf_box((const uint8_t *)g_last_error, (uint64_t)strlen(g_last_error));
}

int64_t rt_counterpart_reset(int64_t handle) {
    return (int64_t)simple_counterpart_reset(handle);
}

int64_t rt_counterpart_close(int64_t handle) {
    return (int64_t)simple_counterpart_close(handle);
}

/* Probe used by the Simple wrapper to prove version negotiation fails closed
 * without opening an instance: returns 1 when the library at `path` serves the
 * requested ABI, 0 when it refuses, and a negative code when it cannot load. */
int64_t rt_counterpart_probe_abi(const uint8_t *path_ptr, uint64_t path_len, int64_t requested_abi) {
    char *path;
    void *library;
    scf_get_api_fn get_api;
    const scf_api_v1 *api;

    if (!path_ptr || path_len == 0) return SCF_RT_ERR_BAD_ARG;
    if (requested_abi < 0 || requested_abi > (int64_t)0xFFFFFFFF) return SCF_RT_ERR_BAD_ARG;
    path = (char *)malloc((size_t)path_len + 1u);
    if (!path) return SCF_RT_ERR_OOM;
    memcpy(path, path_ptr, (size_t)path_len);
    path[path_len] = '\0';

    library = scf_dlopen(path);
    free(path);
    if (!library) return SCF_RT_ERR_DLOPEN;
    {
        union { void *object; scf_get_api_fn function; } bridge;
        bridge.object = scf_dlsym(library, SCF_GET_API_SYMBOL);
        get_api = bridge.function;
    }
    if (!get_api) { scf_dlclose(library); return SCF_RT_ERR_NO_SYMBOL; }
    api = get_api((uint32_t)requested_abi);
    scf_dlclose(library);
    if (!api) return 0;
    return 1;
}
