/* Minimal v1 backend provider entry. C exists only at this ABI boundary; the
 * provider build step and loader live in Simple (app.build.targets.provider_shim).
 * The provider advertises no compile roles: compile/finalize report
 * SBP_STATUS_UNSUPPORTED until a real code generator is linked behind it. */
#include "simple_backend_plugin_v1.h"

#define SBP_STATUS_OK 0
#define SBP_STATUS_UNSUPPORTED (-2)
#define SBP_STATUS_BAD_ARGUMENT (-3)
#define SBP_SESSION_HANDLE UINT64_C(1)

#define SBP_SLICE(s) { (const uint8_t *)(s), (uint64_t)(sizeof(s) - 1) }

static int32_t sbp_open_session(const simple_backend_request_v1 *request, uint64_t *session) {
    if (request == 0 || session == 0) return SBP_STATUS_BAD_ARGUMENT;
    if (request->abi_version != SIMPLE_BACKEND_PLUGIN_ABI_V1) return SBP_STATUS_BAD_ARGUMENT;
    if (request->struct_size < sizeof(simple_backend_request_v1)) return SBP_STATUS_BAD_ARGUMENT;
    *session = SBP_SESSION_HANDLE;
    return SBP_STATUS_OK;
}

static int32_t sbp_compile_module(uint64_t session, simple_backend_slice_v1 mir,
                                  simple_backend_compile_result_v1 *out) {
    (void)mir;
    if (session != SBP_SESSION_HANDLE || out == 0) return SBP_STATUS_BAD_ARGUMENT;
    out->abi_version = SIMPLE_BACKEND_PLUGIN_ABI_V1;
    out->struct_size = (uint32_t)sizeof(*out);
    out->result_kind = 0;
    out->status = SBP_STATUS_UNSUPPORTED;
    out->payload.data = 0;
    out->payload.size = 0;
    out->payload.owner_token = 0;
    return SBP_STATUS_UNSUPPORTED;
}

static int32_t sbp_finalize_object(uint64_t session, simple_backend_compile_result_v1 *out) {
    return sbp_compile_module(session, (simple_backend_slice_v1){0, 0}, out);
}

static int32_t sbp_diagnostics(uint64_t session, simple_backend_owned_buffer_v1 *out) {
    if (session != SBP_SESSION_HANDLE || out == 0) return SBP_STATUS_BAD_ARGUMENT;
    out->data = 0;
    out->size = 0;
    out->owner_token = 0;
    return SBP_STATUS_OK;
}

static int32_t sbp_close_session(uint64_t session) {
    return session == SBP_SESSION_HANDLE ? SBP_STATUS_OK : SBP_STATUS_BAD_ARGUMENT;
}

static int32_t sbp_release_buffer(uint64_t session, simple_backend_owned_buffer_v1 buffer) {
    (void)buffer; /* every buffer this provider returns is empty and unowned */
    return session == SBP_SESSION_HANDLE ? SBP_STATUS_OK : SBP_STATUS_BAD_ARGUMENT;
}

static const simple_backend_vtable_v1 sbp_vtable = {
    SIMPLE_BACKEND_PLUGIN_ABI_V1, (uint32_t)sizeof(simple_backend_vtable_v1),
    sbp_open_session, sbp_compile_module, sbp_finalize_object,
    sbp_diagnostics, sbp_close_session, sbp_release_buffer,
};

static const simple_backend_descriptor_v1 sbp_descriptor = {
    SIMPLE_BACKEND_PLUGIN_ABI_V1, (uint32_t)sizeof(simple_backend_descriptor_v1),
    SBP_SLICE("simple-provider-entry-v1"), SBP_SLICE("1"), SBP_SLICE("provider_entry_v1.c"),
    { 0, 0 },
    0, 0,
    { 0, 0 },
    &sbp_vtable,
};

SIMPLE_BACKEND_PLUGIN_EXPORT const simple_backend_descriptor_v1 *simple_backend_plugin_v1(void) {
    return &sbp_descriptor;
}
