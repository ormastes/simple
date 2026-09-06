/*
 * Fixture-only implementation of libsimple_chromium_primitive_oracle ABI v1.
 *
 * It deliberately does not link Chromium, Blink, Viz, Electron, or a GPU
 * library.  It exercises the dynamic ABI, deterministic primitive request
 * validation, and bounded output/error ownership contract. Its trace says
 * "fixture-not-chromium", so no caller may promote it as Chrome or GPU proof.
 */

#include "simple_chromium_primitive_oracle.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

#define ORACLE_MAX_SESSIONS 64u
#define ORACLE_ERROR_CAPACITY 256u

struct oracle_session {
    uint64_t magic;
    bool released;
    char last_error[ORACLE_ERROR_CAPACITY];
};

static struct oracle_session sessions[ORACLE_MAX_SESSIONS];
static uint64_t session_count;

static const char fixture_trace[] =
    "{\"schema_version\":1,\"run_id\":\"fixture-run\","
    "\"environment_profile_id\":\"chrome-web-oracle-fixture\","
    "\"ui_environment_profile_id\":\"host-web-fixture\","
    "\"arch\":\"fixture\",\"transport\":\"fixture-dynload\","
    "\"enabled_features\":[\"primitive-v1\",\"fixture-only\"],"
    "\"venus_version\":\"n/a\",\"device_identity\":\"unavailable\","
    "\"oracle_identity\":\"fixture-not-chromium\","
    "\"device_origin_readback\":false,\"fallback_used\":false,"
    "\"dropped_events\":0,\"complete\":true,\"events\":["
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":0,\"monotonic_ns\":0,\"layer_id\":\"web_dom\",\"operation\":\"tree\",\"object_id\":\"root\",\"parent_id\":\"\",\"result_class\":\"ok\",\"error_class\":\"\",\"payload_digest\":\"fixture-dom\",\"scalar_fields\":\"tag=div\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"},"
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":1,\"monotonic_ns\":1,\"layer_id\":\"web_style\",\"operation\":\"computed\",\"object_id\":\"root\",\"parent_id\":\"\",\"result_class\":\"ok\",\"error_class\":\"\",\"payload_digest\":\"fixture-style\",\"scalar_fields\":\"background=rgba8;border=rgba8;text=font-metrics\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"},"
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":2,\"monotonic_ns\":2,\"layer_id\":\"web_layout\",\"operation\":\"boxes\",\"object_id\":\"root\",\"parent_id\":\"\",\"result_class\":\"ok\",\"error_class\":\"\",\"payload_digest\":\"fixture-layout\",\"scalar_fields\":\"image=intrinsic;resize=viewport;scroll=offset\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"},"
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":3,\"monotonic_ns\":3,\"layer_id\":\"web_paint\",\"operation\":\"cpu_readback\",\"object_id\":\"frame\",\"parent_id\":\"root\",\"result_class\":\"ok\",\"error_class\":\"\",\"payload_digest\":\"fixture-cpu-pixels\",\"scalar_fields\":\"border=paint;image=paint;rect=paint;text=paint\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"},"
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":4,\"monotonic_ns\":4,\"layer_id\":\"web_input\",\"operation\":\"dispatch\",\"object_id\":\"root\",\"parent_id\":\"\",\"result_class\":\"ok\",\"error_class\":\"\",\"payload_digest\":\"fixture-input\",\"scalar_fields\":\"alt_left=false;alt_right=false;ctrl_left=false;ctrl_right=false;event=pointer-click-keyboard\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"},"
    "{\"schema_version\":1,\"run_id\":\"fixture-run\",\"sequence\":5,\"monotonic_ns\":5,\"layer_id\":\"web_gpu\",\"operation\":\"requested\",\"object_id\":\"frame\",\"parent_id\":\"root\",\"result_class\":\"unavailable\",\"error_class\":\"fixture-no-gpu\",\"payload_digest\":\"unavailable\",\"scalar_fields\":\"receipt=unavailable\",\"environment_profile_id\":\"chrome-web-oracle-fixture\"}]}";

static struct oracle_session *session_from_handle(int64_t handle) {
    struct oracle_session *candidate = (struct oracle_session *)(intptr_t)handle;
    for (uint64_t index = 0; index < session_count; ++index) {
        if (candidate == &sessions[index] && sessions[index].magic == 0x53494d504c454f52ULL) {
            return candidate;
        }
    }
    return NULL;
}

static void set_error(struct oracle_session *session, const char *message) {
    if (session == NULL) return;
    (void)snprintf(session->last_error, sizeof(session->last_error), "%s", message);
}

static bool request_has(const uint8_t *request, uint64_t request_len, const char *needle) {
    size_t needle_len = strlen(needle);
    if (request == NULL || request_len < needle_len) return false;
    for (uint64_t index = 0; index + needle_len <= request_len; ++index) {
        if (memcmp(request + index, needle, needle_len) == 0) return true;
    }
    return false;
}

static int32_t copy_response(struct oracle_session *session, const char *source,
                             uint8_t *response, uint64_t response_capacity,
                             uint64_t *response_len) {
    const uint64_t length = (uint64_t)strlen(source);
    if (response_len == NULL) {
        set_error(session, "response_len is required");
        return SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST;
    }
    *response_len = length;
    if (response == NULL || response_capacity < length) {
        set_error(session, "caller response buffer is too small");
        return SIMPLE_CHROMIUM_ORACLE_BUFFER_TOO_SMALL;
    }
    memcpy(response, source, (size_t)length);
    return SIMPLE_CHROMIUM_ORACLE_OK;
}

uint32_t simple_chromium_oracle_abi_version(void) {
    return SIMPLE_CHROMIUM_ORACLE_ABI_VERSION;
}

int64_t simple_chromium_oracle_create(const uint8_t *config, uint64_t config_len) {
    if (config == NULL || config_len > SIMPLE_CHROMIUM_ORACLE_MAX_REQUEST_BYTES ||
        !request_has(config, config_len, "{")) {
        return 0;
    }
    if (session_count >= ORACLE_MAX_SESSIONS) return 0;
    struct oracle_session *session = &sessions[session_count++];
    session->magic = 0x53494d504c454f52ULL;
    session->released = false;
    session->last_error[0] = '\0';
    return (int64_t)(intptr_t)session;
}

int32_t simple_chromium_oracle_run_json_into(int64_t handle,
    const uint8_t *request, uint64_t request_len, uint8_t *response,
    uint64_t response_capacity, uint64_t *response_len) {
    struct oracle_session *session = session_from_handle(handle);
    if (session == NULL) return SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST;
    if (session->released) {
        set_error(session, "released bridge handle");
        return SIMPLE_CHROMIUM_ORACLE_RELEASED_HANDLE;
    }
    if (request == NULL || request_len == 0 || request_len > SIMPLE_CHROMIUM_ORACLE_MAX_REQUEST_BYTES) {
        set_error(session, "invalid bounded primitive request");
        return SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST;
    }
    const char *required[] = {"\"rect\"", "\"text\"", "\"image\"", "\"pointer\"",
        "\"keyboard\"", "\"scroll\"", "\"resize\""};
    for (size_t index = 0; index < sizeof(required) / sizeof(required[0]); ++index) {
        if (!request_has(request, request_len, required[index])) {
            set_error(session, "unsupported primitive fixture request");
            return SIMPLE_CHROMIUM_ORACLE_UNSUPPORTED_PRIMITIVE;
        }
    }
    return copy_response(session, fixture_trace, response, response_capacity, response_len);
}

int32_t simple_chromium_oracle_last_error_into(int64_t handle,
    uint8_t *response, uint64_t response_capacity, uint64_t *response_len) {
    struct oracle_session *session = session_from_handle(handle);
    if (session == NULL) return SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST;
    return copy_response(session, session->last_error, response, response_capacity, response_len);
}

int32_t simple_chromium_oracle_destroy(int64_t handle) {
    struct oracle_session *session = session_from_handle(handle);
    if (session == NULL) return SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST;
    if (session->released) {
        set_error(session, "released bridge handle");
        return SIMPLE_CHROMIUM_ORACLE_RELEASED_HANDLE;
    }
    session->released = true;
    set_error(session, "released bridge handle");
    return SIMPLE_CHROMIUM_ORACLE_OK;
}
