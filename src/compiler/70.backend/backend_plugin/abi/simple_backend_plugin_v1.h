#ifndef SIMPLE_BACKEND_PLUGIN_V1_H
#define SIMPLE_BACKEND_PLUGIN_V1_H
#include <stdint.h>
#if defined(_WIN32)
#define SIMPLE_BACKEND_PLUGIN_EXPORT __declspec(dllexport)
#else
#define SIMPLE_BACKEND_PLUGIN_EXPORT __attribute__((visibility("default")))
#endif
#define SIMPLE_BACKEND_PLUGIN_ABI_V1 UINT32_C(1)
#define SIMPLE_BACKEND_PLUGIN_ENTRY_V1 "simple_backend_plugin_v1"
typedef struct { const uint8_t *data; uint64_t size; } simple_backend_slice_v1;
/* Provider-owned output; release exactly once when data is non-NULL. */
typedef struct { const uint8_t *data; uint64_t size; uint64_t owner_token; }
    simple_backend_owned_buffer_v1;
typedef struct {
    uint32_t abi_version, struct_size, role, reserved0;
    simple_backend_slice_v1 backend_name, target, cpu, features_wire;
    simple_backend_slice_v1 optimization, mir_abi_digest;
    uint64_t required_capabilities;
} simple_backend_request_v1;
typedef struct {
    uint32_t abi_version, struct_size, result_kind;
    int32_t status;
    simple_backend_owned_buffer_v1 payload;
} simple_backend_compile_result_v1;
typedef int32_t (*simple_backend_open_session_v1_fn)(const simple_backend_request_v1 *, uint64_t *);
typedef int32_t (*simple_backend_compile_module_v1_fn)(uint64_t, simple_backend_slice_v1, simple_backend_compile_result_v1 *);
typedef int32_t (*simple_backend_finalize_object_v1_fn)(uint64_t, simple_backend_compile_result_v1 *);
typedef int32_t (*simple_backend_diagnostics_v1_fn)(uint64_t, simple_backend_owned_buffer_v1 *);
typedef int32_t (*simple_backend_close_session_v1_fn)(uint64_t);
typedef int32_t (*simple_backend_release_buffer_v1_fn)(uint64_t, simple_backend_owned_buffer_v1);
typedef struct {
    uint32_t abi_version, struct_size;
    simple_backend_open_session_v1_fn open_session;
    simple_backend_compile_module_v1_fn compile_module;
    simple_backend_finalize_object_v1_fn finalize_object;
    simple_backend_diagnostics_v1_fn diagnostics;
    simple_backend_close_session_v1_fn close_session;
    simple_backend_release_buffer_v1_fn release_buffer;
} simple_backend_vtable_v1;
typedef struct {
    uint32_t abi_version, struct_size;
    simple_backend_slice_v1 provider_identity, provider_version, build_id, mir_abi_digest;
    uint64_t roles, capabilities;
    simple_backend_slice_v1 targets_wire;
    const simple_backend_vtable_v1 *vtable;
} simple_backend_descriptor_v1;
typedef const simple_backend_descriptor_v1 *(*simple_backend_plugin_entry_v1_fn)(void);
SIMPLE_BACKEND_PLUGIN_EXPORT const simple_backend_descriptor_v1 *simple_backend_plugin_v1(void);
#endif
