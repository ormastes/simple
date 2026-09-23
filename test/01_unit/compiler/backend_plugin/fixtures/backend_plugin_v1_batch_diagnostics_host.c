/* Exercise the real retained-session dispatch with a mock provider vtable.
 * Including the bridge lets this bounded test inject a session without a DSO. */
#include "runtime_backend_plugin.c"
#include <assert.h>
#include <stdio.h>

typedef struct { uint8_t *data; int64_t len; } TestBytes;
static int compile_calls, finalize_calls, diagnostic_calls, close_calls;
static int allocated, released;
static const uint8_t *live[2];
static int32_t operation_status, diagnostic_status;
static int diagnostic_mode; /* 0: absent, 1: text, 2: owned empty buffer */

int64_t rt_array_len_safe(int64_t value) {
    return ((TestBytes *)(uintptr_t)value)->len;
}
int64_t rt_array_data_ptr(SplArray *value) {
    return (int64_t)(uintptr_t)((TestBytes *)value)->data;
}
int64_t rt_bytes_from_raw(int64_t pointer, int64_t size) {
    TestBytes *out = calloc(1, sizeof(*out));
    assert(out);
    out->data = malloc(size ? (size_t)size : 1);
    assert(out->data);
    out->len = size;
    if (size) memcpy(out->data, (void *)(uintptr_t)pointer, (size_t)size);
    return (int64_t)(uintptr_t)out;
}
static simple_backend_owned_buffer_v1 owned(const char *text) {
    size_t size = strlen(text);
    uint8_t *data = malloc(size ? size : 1);
    assert(data && allocated < 2);
    memcpy(data, text, size);
    live[allocated++] = data;
    return (simple_backend_owned_buffer_v1){data, size, (uint64_t)(uintptr_t)data};
}
static int32_t compile_(uint64_t session, simple_backend_slice_v1 mir,
                         simple_backend_compile_result_v1 *out) {
    assert(session == 17 && mir.size == 4 && !memcmp(mir.data, "MIR1", 4));
    compile_calls++;
    out->result_kind = 1;
    out->payload = owned("module");
    return operation_status;
}
static int32_t finalize_(uint64_t session, simple_backend_compile_result_v1 *out) {
    assert(session == 17);
    finalize_calls++;
    out->result_kind = 2;
    out->payload = owned("object");
    return operation_status;
}
static int32_t diagnostics_(uint64_t session, simple_backend_owned_buffer_v1 *out) {
    assert(session == 17);
    diagnostic_calls++;
    if (diagnostic_mode) *out = owned(diagnostic_mode == 1 ? "provider failure" : "");
    return diagnostic_status;
}
static int32_t release_(uint64_t session, simple_backend_owned_buffer_v1 buffer) {
    assert(session == 17 && buffer.data);
    assert(buffer.owner_token == (uint64_t)(uintptr_t)buffer.data);
    int index = 0;
    while (index < allocated && live[index] != buffer.data) index++;
    assert(index < allocated); /* unknown or double release */
    live[index] = NULL;
    memset((void *)buffer.data, 0xdd, (size_t)buffer.size);
    free((void *)buffer.data);
    released++;
    return 0;
}
static int32_t close_(uint64_t session) {
    assert(session == 17 && allocated == released);
    close_calls++;
    return 0;
}
static const simple_backend_vtable_v1 vtable = {
    .abi_version = 1, .struct_size = sizeof(vtable),
    .compile_module = compile_, .finalize_object = finalize_,
    .diagnostics = diagnostics_, .release_buffer = release_, .close_session = close_
};
static void check_envelope(int64_t value, int32_t status, uint32_t kind,
                             const char *payload, const char *diagnostic) {
    TestBytes *out = (TestBytes *)(uintptr_t)value;
    uint32_t magic, version, actual_kind;
    int32_t actual_status;
    uint64_t payload_size, diagnostic_size;
    assert(out && out->len >= 32);
    memcpy(&magic, out->data, 4);
    memcpy(&version, out->data + 4, 4);
    memcpy(&actual_status, out->data + 8, 4);
    memcpy(&actual_kind, out->data + 12, 4);
    memcpy(&payload_size, out->data + 16, 8);
    memcpy(&diagnostic_size, out->data + 24, 8);
    assert(magic == SIMPLE_BACKEND_BRIDGE_MAGIC_V1 && version == 1);
    assert(actual_status == status && actual_kind == kind);
    assert(payload_size == strlen(payload) && diagnostic_size == strlen(diagnostic));
    assert((uint64_t)out->len == 32 + payload_size + diagnostic_size);
    assert(!memcmp(out->data + 32, payload, (size_t)payload_size));
    assert(!memcmp(out->data + 32 + payload_size, diagnostic, (size_t)diagnostic_size));
    free(out->data);
    free(out);
}
static void run_case(int finalize, int32_t status, int32_t diag_status, int mode) {
    compile_calls = finalize_calls = diagnostic_calls = close_calls = 0;
    allocated = released = 0;
    memset(live, 0, sizeof(live));
    operation_status = status;
    diagnostic_status = diag_status;
    diagnostic_mode = mode;
    simple_backend_bridge_batch_v1 *batch = calloc(1, sizeof(*batch));
    assert(batch);
    batch->vtable = &vtable;
    batch->provider_session = 17;
    int64_t handle = (int64_t)(uintptr_t)batch;
    TestBytes mir = {(uint8_t *)"MIR1", 4};
    int64_t result = finalize ? spl_backend_plugin_batch_finalize_v1(handle)
        : spl_backend_plugin_batch_compile_v1(handle, (int64_t)(uintptr_t)&mir);
    int expect_diagnostics = finalize || status != 0;
    int32_t expected_status = status ? status : (expect_diagnostics ? diag_status : 0);
    assert(compile_calls == !finalize && finalize_calls == finalize);
    assert(diagnostic_calls == expect_diagnostics && close_calls == 0);
    assert(allocated == 1 + (expect_diagnostics && mode != 0));
    assert(released == allocated && !live[0] && !live[1]);
    check_envelope(result, expected_status, finalize ? 2 : 1,
        expected_status ? "" : (finalize ? "object" : "module"),
        expect_diagnostics && mode == 1 ? "provider failure" : "");
    if (finalize) {
        check_envelope(spl_backend_plugin_batch_finalize_v1(handle), 108, 0, "", "");
        check_envelope(spl_backend_plugin_batch_compile_v1(handle,
            (int64_t)(uintptr_t)&mir), 108, 0, "", "");
        assert(finalize_calls == 1 && compile_calls == 0 && diagnostic_calls == 1);
    }
    assert(spl_backend_plugin_batch_close_v1(handle) == 0 && close_calls == 1);
}
int main(void) {
    for (int finalize = 0; finalize <= 1; finalize++)
        for (int failure = 0; failure <= 1; failure++)
            for (int diag_failure = 0; diag_failure <= 1; diag_failure++)
                for (int mode = 0; mode <= 2; mode++)
                    run_case(finalize, failure ? (finalize ? 33 : 32) : 0,
                        diag_failure ? 34 : 0, mode);
    puts("PASS retained batch diagnostics: 24 cases, exact call/release counts");
    return 0;
}
