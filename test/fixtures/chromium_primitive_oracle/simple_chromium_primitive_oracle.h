#ifndef SIMPLE_CHROMIUM_PRIMITIVE_ORACLE_H
#define SIMPLE_CHROMIUM_PRIMITIVE_ORACLE_H

#include <stdint.h>

/* Fixture-only ABI: this header is not a Chromium/Blink/Viz public API. */
#define SIMPLE_CHROMIUM_ORACLE_ABI_VERSION 1u
#define SIMPLE_CHROMIUM_ORACLE_MAX_REQUEST_BYTES (1024u * 1024u)
#define SIMPLE_CHROMIUM_ORACLE_MAX_RESPONSE_BYTES (4u * 1024u * 1024u)

enum simple_chromium_oracle_status {
    SIMPLE_CHROMIUM_ORACLE_OK = 0,
    SIMPLE_CHROMIUM_ORACLE_INVALID_REQUEST = 1,
    SIMPLE_CHROMIUM_ORACLE_UNSUPPORTED_PRIMITIVE = 2,
    SIMPLE_CHROMIUM_ORACLE_BUFFER_TOO_SMALL = 3,
    SIMPLE_CHROMIUM_ORACLE_ADAPTER_FAILURE = 4,
    SIMPLE_CHROMIUM_ORACLE_RELEASED_HANDLE = 5
};

uint32_t simple_chromium_oracle_abi_version(void);
int64_t simple_chromium_oracle_create(const uint8_t *config, uint64_t config_len);
int32_t simple_chromium_oracle_run_json_into(int64_t handle,
    const uint8_t *request, uint64_t request_len, uint8_t *response,
    uint64_t response_capacity, uint64_t *response_len);
int32_t simple_chromium_oracle_last_error_into(int64_t handle,
    uint8_t *response, uint64_t response_capacity, uint64_t *response_len);
int32_t simple_chromium_oracle_destroy(int64_t handle);

#endif
