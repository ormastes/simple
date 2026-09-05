/* Mock counterpart provider adapter (Wave-2 P1).
 *
 * Exercises every path of the scf_api_v1 ABI without any upstream dependency:
 *
 *   mock.echo    returns the request bytes verbatim inside a response envelope
 *   mock.hash    returns a stable FNV-1a-64 hex of the request (deterministic)
 *   mock.error   returns a STRUCTURED error envelope with status SCF_OK — this
 *                is the case that proves an error is data, not an overloaded
 *                nonzero return
 *   mock.crash   deliberately abort()s, so the isolated worker can be shown to
 *                report provider_status: crashed rather than normalizing it
 *
 * Envelopes are SDN text written through the caller's writer. The adapter
 * allocates nothing the caller must free.
 *
 * Design: doc/05_design/infra/counterpart/counterpart_conformance_infrastructure_design_2026-08-09.md §3
 */

#include "simple_counterpart_abi.h"

#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------------ */
/* Instance                                                                  */
/* ------------------------------------------------------------------------ */

struct scf_instance_v1 {
    uint32_t magic;
    uint64_t invocation_count;
};

#define MOCK_MAGIC 0x5343464Du /* "SCFM" */

/* ------------------------------------------------------------------------ */
/* Writer helpers — all output goes through the caller's sink                */
/* ------------------------------------------------------------------------ */

static int32_t mock_write(scf_writer_v1 *w, const char *text) {
    if (!w || !w->write) return SCF_OK; /* NULL writer means discard */
    return w->write(w->context, (const uint8_t *)text, (uint64_t)strlen(text));
}

static int32_t mock_write_bytes(scf_writer_v1 *w, const uint8_t *data, uint64_t size) {
    if (!w || !w->write) return SCF_OK;
    if (size == 0) return SCF_OK;
    if (!data) return SCF_INVALID_ARG;
    return w->write(w->context, data, size);
}

/* Write bytes as SDN-safe text: printable ASCII passes through with `"` and
 * `\` escaped, everything else becomes \xHH. Never assumes NUL termination. */
static int32_t mock_write_escaped(scf_writer_v1 *w, const uint8_t *data, uint64_t size) {
    static const char hex[] = "0123456789abcdef";
    char buffer[256];
    size_t filled = 0;
    uint64_t index;
    int32_t status;

    if (size == 0) return SCF_OK;
    if (!data) return SCF_INVALID_ARG;

    for (index = 0; index < size; index++) {
        uint8_t byte = data[index];
        char encoded[4];
        size_t encoded_len;

        if (byte == '"' || byte == '\\') {
            encoded[0] = '\\';
            encoded[1] = (char)byte;
            encoded_len = 2;
        } else if (byte >= 0x20 && byte < 0x7F) {
            encoded[0] = (char)byte;
            encoded_len = 1;
        } else {
            encoded[0] = '\\';
            encoded[1] = 'x';
            encoded[2] = hex[(byte >> 4) & 0xF];
            encoded[3] = hex[byte & 0xF];
            encoded_len = 4;
        }

        if (filled + encoded_len > sizeof(buffer)) {
            status = mock_write_bytes(w, (const uint8_t *)buffer, (uint64_t)filled);
            if (status != SCF_OK) return status;
            filled = 0;
        }
        memcpy(buffer + filled, encoded, encoded_len);
        filled += encoded_len;
    }
    if (filled > 0) {
        return mock_write_bytes(w, (const uint8_t *)buffer, (uint64_t)filled);
    }
    return SCF_OK;
}

static int32_t mock_write_u64(scf_writer_v1 *w, uint64_t value) {
    char digits[21];
    size_t position = sizeof(digits);
    if (value == 0) {
        return mock_write(w, "0");
    }
    while (value > 0 && position > 0) {
        digits[--position] = (char)('0' + (int)(value % 10u));
        value /= 10u;
    }
    return mock_write_bytes(w, (const uint8_t *)(digits + position),
                            (uint64_t)(sizeof(digits) - position));
}

/* ------------------------------------------------------------------------ */
/* FNV-1a 64 — deterministic, byte-exact, no allocation                      */
/* ------------------------------------------------------------------------ */

static uint64_t mock_fnv1a64(const uint8_t *data, uint64_t size) {
    uint64_t hash = 1469598103934665603ULL; /* offset basis */
    uint64_t index;
    if (!data) return hash;
    for (index = 0; index < size; index++) {
        hash ^= (uint64_t)data[index];
        hash *= 1099511628211ULL; /* prime */
    }
    return hash;
}

static void mock_hex64(uint64_t value, char out[17]) {
    static const char hex[] = "0123456789abcdef";
    int shift;
    int position = 0;
    for (shift = 60; shift >= 0; shift -= 4) {
        out[position++] = hex[(value >> shift) & 0xFULL];
    }
    out[16] = '\0';
}

/* ------------------------------------------------------------------------ */
/* Slice helpers                                                             */
/* ------------------------------------------------------------------------ */

static int mock_slice_is_valid(scf_slice_v1 slice) {
    return (slice.size == 0) || (slice.data != NULL);
}

static int mock_slice_equals(scf_slice_v1 slice, const char *literal) {
    uint64_t length = (uint64_t)strlen(literal);
    if (slice.size != length) return 0;
    if (length == 0) return 1;
    if (!slice.data) return 0;
    return memcmp(slice.data, literal, (size_t)length) == 0;
}

/* ------------------------------------------------------------------------ */
/* Manifest                                                                  */
/* ------------------------------------------------------------------------ */

static const char MOCK_MANIFEST_SDN[] =
    "provider_id: mock\n"
    "provider_kind: native_in_process\n"
    "independence_group: mock\n"
    "abi_version: 1\n"
    "version: 1.0.0\n"
    "artifact_hash: mock-adapter-v1\n"
    "license_spdx: Apache-2.0\n"
    "components:\n"
    "  - component_id: mock.echo\n"
    "    counterpart_boundary_id: mock.execution.echo@1\n"
    "    input_schema_id: mock.request@1\n"
    "    output_schema_id: mock.echo_response@1\n"
    "    stateful: false\n"
    "    reset_supported: true\n"
    "    deterministic_claim: deterministic\n"
    "    supported_relations: [byte_exact]\n"
    "    supported_execution_modes: [cpu_reference]\n"
    "    capability_requirements: []\n"
    "  - component_id: mock.hash\n"
    "    counterpart_boundary_id: mock.execution.hash@1\n"
    "    input_schema_id: mock.request@1\n"
    "    output_schema_id: mock.hash_response@1\n"
    "    stateful: false\n"
    "    reset_supported: true\n"
    "    deterministic_claim: deterministic\n"
    "    supported_relations: [byte_exact, canonical_exact]\n"
    "    supported_execution_modes: [cpu_reference]\n"
    "    capability_requirements: []\n"
    "  - component_id: mock.error\n"
    "    counterpart_boundary_id: mock.execution.error@1\n"
    "    input_schema_id: mock.request@1\n"
    "    output_schema_id: mock.error_envelope@1\n"
    "    stateful: false\n"
    "    reset_supported: true\n"
    "    deterministic_claim: deterministic\n"
    "    supported_relations: [structural_equal]\n"
    "    supported_execution_modes: [cpu_reference]\n"
    "    capability_requirements: []\n"
    "  - component_id: mock.crash\n"
    "    counterpart_boundary_id: mock.execution.crash@1\n"
    "    input_schema_id: mock.request@1\n"
    "    output_schema_id: mock.never@1\n"
    "    stateful: false\n"
    "    reset_supported: false\n"
    "    deterministic_claim: deterministic\n"
    "    supported_relations: []\n"
    "    supported_execution_modes: [cpu_reference]\n"
    "    capability_requirements: [isolated_worker]\n";

static int32_t mock_manifest(scf_writer_v1 *output) {
    if (!output) return SCF_INVALID_ARG;
    return mock_write(output, MOCK_MANIFEST_SDN);
}

/* ------------------------------------------------------------------------ */
/* Lifecycle                                                                 */
/* ------------------------------------------------------------------------ */

static int32_t mock_open(scf_slice_v1 configuration, scf_instance_v1 **out_instance) {
    struct scf_instance_v1 *instance;

    if (!out_instance) return SCF_INVALID_ARG;
    *out_instance = NULL;
    if (!mock_slice_is_valid(configuration)) return SCF_INVALID_ARG;

    instance = (struct scf_instance_v1 *)calloc(1, sizeof(struct scf_instance_v1));
    if (!instance) return SCF_INTERNAL;
    instance->magic = MOCK_MAGIC;
    instance->invocation_count = 0;
    *out_instance = instance;
    return SCF_OK;
}

static int32_t mock_reset(scf_instance_v1 *instance) {
    if (!instance || instance->magic != MOCK_MAGIC) return SCF_INVALID_ARG;
    instance->invocation_count = 0;
    return SCF_OK;
}

static void mock_close(scf_instance_v1 *instance) {
    if (!instance) return;
    if (instance->magic != MOCK_MAGIC) return;
    instance->magic = 0;
    free(instance);
}

/* ------------------------------------------------------------------------ */
/* Trace envelope                                                            */
/* ------------------------------------------------------------------------ */

static int32_t mock_write_trace(scf_writer_v1 *trace,
                                const char *component,
                                uint64_t invocation,
                                uint64_t request_size) {
    int32_t status;
    if (!trace || !trace->write) return SCF_OK;
    status = mock_write(trace, "schema_id: mock.trace@1\nprovider_id: mock\n"
                               "execution_mode: cpu_reference\ncomponent_id: ");
    if (status != SCF_OK) return status;
    status = mock_write(trace, component);
    if (status != SCF_OK) return status;
    status = mock_write(trace, "\ninvocation: ");
    if (status != SCF_OK) return status;
    status = mock_write_u64(trace, invocation);
    if (status != SCF_OK) return status;
    status = mock_write(trace, "\nrequest_bytes: ");
    if (status != SCF_OK) return status;
    status = mock_write_u64(trace, request_size);
    if (status != SCF_OK) return status;
    return mock_write(trace, "\ncompleted: true\n");
}

/* ------------------------------------------------------------------------ */
/* Components                                                                */
/* ------------------------------------------------------------------------ */

static int32_t mock_component_echo(scf_slice_v1 request, scf_writer_v1 *response) {
    int32_t status = mock_write(response,
        "schema_id: mock.echo_response@1\nschema_version: 1\nstatus: ok\n"
        "item_count: 1\nbody: \"");
    if (status != SCF_OK) return status;
    status = mock_write_escaped(response, request.data, request.size);
    if (status != SCF_OK) return status;
    return mock_write(response, "\"\n");
}

static int32_t mock_component_hash(scf_slice_v1 request, scf_writer_v1 *response) {
    char hex[17];
    int32_t status;
    mock_hex64(mock_fnv1a64(request.data, request.size), hex);

    status = mock_write(response,
        "schema_id: mock.hash_response@1\nschema_version: 1\nstatus: ok\n"
        "item_count: 1\nalgorithm: fnv1a64\ndigest: ");
    if (status != SCF_OK) return status;
    status = mock_write(response, hex);
    if (status != SCF_OK) return status;
    status = mock_write(response, "\ninput_bytes: ");
    if (status != SCF_OK) return status;
    status = mock_write_u64(response, request.size);
    if (status != SCF_OK) return status;
    return mock_write(response, "\n");
}

/* Structured error ENVELOPE, returned with SCF_OK. A bare nonzero return would
 * lose the reason and let a caller normalize the failure away. */
static int32_t mock_component_error(scf_slice_v1 request, scf_writer_v1 *response) {
    int32_t status = mock_write(response,
        "schema_id: mock.error_envelope@1\nschema_version: 1\nstatus: error\n"
        "item_count: 0\nerror_code: mock.deliberate_failure\n"
        "error_message: \"mock.error always fails by contract\"\n"
        "retryable: false\nrequest_bytes: ");
    if (status != SCF_OK) return status;
    status = mock_write_u64(response, request.size);
    if (status != SCF_OK) return status;
    return mock_write(response, "\n");
}

static int32_t mock_invoke(scf_instance_v1 *instance,
                           scf_slice_v1 component_id,
                           scf_slice_v1 request_envelope,
                           scf_writer_v1 *response_envelope,
                           scf_writer_v1 *trace_envelope) {
    int32_t status;
    const char *component_name;

    if (!instance || instance->magic != MOCK_MAGIC) return SCF_INVALID_ARG;
    if (!mock_slice_is_valid(component_id)) return SCF_INVALID_ARG;
    if (!mock_slice_is_valid(request_envelope)) return SCF_INVALID_ARG;
    if (component_id.size == 0) return SCF_UNKNOWN_COMPONENT;

    instance->invocation_count += 1;

    if (mock_slice_equals(component_id, "mock.crash")) {
        /* Deliberate: proves the isolated worker reports `crashed` instead of
         * folding an aborted provider into "unavailable". Never call this
         * in-process from a test harness. */
        abort();
    }

    if (mock_slice_equals(component_id, "mock.echo")) {
        component_name = "mock.echo";
        status = mock_component_echo(request_envelope, response_envelope);
    } else if (mock_slice_equals(component_id, "mock.hash")) {
        component_name = "mock.hash";
        status = mock_component_hash(request_envelope, response_envelope);
    } else if (mock_slice_equals(component_id, "mock.error")) {
        component_name = "mock.error";
        status = mock_component_error(request_envelope, response_envelope);
    } else {
        return SCF_UNKNOWN_COMPONENT;
    }

    if (status != SCF_OK) return status;
    return mock_write_trace(trace_envelope, component_name,
                            instance->invocation_count, request_envelope.size);
}

/* ------------------------------------------------------------------------ */
/* Bootstrap                                                                 */
/* ------------------------------------------------------------------------ */

static const scf_api_v1 MOCK_API = {
    (uint32_t)sizeof(scf_api_v1),
    SCF_ABI_V1,
    mock_manifest,
    mock_open,
    mock_invoke,
    mock_reset,
    mock_close
};

const scf_api_v1 *scf_get_api(uint32_t requested_abi) {
    if (requested_abi != SCF_ABI_V1) return NULL;
    return &MOCK_API;
}
