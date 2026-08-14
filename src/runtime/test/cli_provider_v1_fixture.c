/* Real shared-library fixture for the Simple provider/CLI packed ABIs. */
#include <stdint.h>
#include <string.h>

static uint32_t rd32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static uint64_t rd64(const uint8_t *p) {
    uint64_t v = 0;
    for (unsigned i = 0; i < 8; ++i) v |= (uint64_t)p[i] << (8 * i);
    return v;
}
static void wr32(uint8_t *p, uint32_t v) {
    for (unsigned i = 0; i < 4; ++i) p[i] = (uint8_t)(v >> (8 * i));
}
static void wr64(uint8_t *p, uint64_t v) {
    for (unsigned i = 0; i < 8; ++i) p[i] = (uint8_t)(v >> (8 * i));
}

int32_t simple_provider_query_v1(const uint8_t *request, uint8_t *result) {
    const uint64_t cli_interface = UINT64_C(5999723006133093425);
    if (!request || !result || rd32(request) != 44 ||
            rd64(request + 4) != cli_interface || rd32(request + 12) != 1 ||
            rd64(request + 20) == 0) return -9;
    memset(result, 0, 60);
    wr32(result, 0);
    wr32(result + 4, 1);
    wr32(result + 8, 0);
    wr32(result + 12, 28);
    wr64(result + 16, UINT64_C(0x434c4931));
    wr64(result + 24, UINT64_C(0x50525631));
    wr64(result + 32, UINT64_C(0x1111));
    wr64(result + 40, UINT64_C(0x2222));
    wr64(result + 48, UINT64_C(0x3333));
    return 0;
}

int32_t simple_cli_command_invoke_v1(uint64_t interface_handle,
        uint64_t provider_context, const uint8_t *request,
        uint32_t request_len, uint8_t *result, uint32_t result_capacity) {
    static const char output[] = "native-provider-ok";
    if (interface_handle != UINT64_C(0x434c4931) ||
            provider_context != UINT64_C(0x50525631) || !request || !result ||
            request_len < 28 || rd32(request) != 28 || rd32(request + 4) != 3)
        return 1;
    uint32_t command_offset = rd32(request + 8);
    uint32_t command_length = rd32(request + 12);
    if (command_offset != 28 || command_length != 3 ||
            command_offset + command_length > request_len ||
            memcmp(request + command_offset, "fmt", 3) != 0 ||
            result_capacity < 20 + sizeof(output) - 1) return 1;
    memset(result, 0, result_capacity);
    wr32(result, 0);
    wr32(result + 4, 20);
    wr32(result + 8, sizeof(output) - 1);
    wr32(result + 12, 20 + sizeof(output) - 1);
    wr32(result + 16, 0);
    memcpy(result + 20, output, sizeof(output) - 1);
    return 0;
}
