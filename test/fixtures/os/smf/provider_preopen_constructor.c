#define _POSIX_C_SOURCE 200809L
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

#ifndef SIMPLE_PROVIDER_MARKER_PATH
#error SIMPLE_PROVIDER_MARKER_PATH must be supplied by the fixture builder
#endif

__attribute__((constructor)) static void record_provider_open(void) {
    static const char marker[] = "constructor-ran\n";
    int fd = open(SIMPLE_PROVIDER_MARKER_PATH,
                  O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return;
    (void)write(fd, marker, sizeof(marker) - 1);
    (void)close(fd);
}

static void write_u32_le(uint8_t *out, uint32_t value) {
    for (unsigned i = 0; i < 4; ++i) out[i] = (uint8_t)(value >> (i * 8));
}

/* Matches runtime_native.c's simple_provider_query_v1_fn:
 * int32_t(uint64_t request_address, uint64_t result_address). The 84-byte
 * response follows provider_query_wire.spl's packed offsets. This fixture is
 * callable but reports SIMPLE_PROVIDER_INTERFACE_UNKNOWN and creates no
 * provider handles; the test verifies admission, not query success. */
__attribute__((visibility("default"))) int32_t simple_provider_query_v1(
        uint64_t request_address, uint64_t result_address) {
    const uint8_t *request = (const uint8_t *)(uintptr_t)request_address;
    uint8_t *result = (uint8_t *)(uintptr_t)result_address;
    if (!request || !result) return -9;
    memset(result, 0, 84);
    write_u32_le(result, 1);  /* SIMPLE_PROVIDER_INTERFACE_UNKNOWN */
    write_u32_le(result + 12, 84); /* SIMPLE_PROVIDER_QUERY_RESULT_V1_SIZE */
    return 1;
}
