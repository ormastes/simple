/* Host proof: dlopen a real provider and cross both exact runtime ABIs. */
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern int32_t rt_provider_query_v1_call(int64_t, int64_t, int64_t);
extern int32_t rt_cli_command_v1_call(int64_t, int64_t, int64_t,
    int64_t, int64_t, int64_t, int64_t);

static void wr32(uint8_t *p, uint32_t v) {
    for (unsigned i = 0; i < 4; ++i) p[i] = (uint8_t)(v >> (8 * i));
}
static void wr64(uint8_t *p, uint64_t v) {
    for (unsigned i = 0; i < 8; ++i) p[i] = (uint8_t)(v >> (8 * i));
}
static uint32_t rd32(const uint8_t *p) {
    return (uint32_t)p[0] | ((uint32_t)p[1] << 8) |
           ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24);
}
static uint64_t rd64(const uint8_t *p) {
    uint64_t v = 0;
    for (unsigned i = 0; i < 8; ++i) v |= (uint64_t)p[i] << (8 * i);
    return v;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 3) return 10;
    const char *expected = argc == 3 ? argv[2] : "native-provider-ok";
    size_t expected_len = strlen(expected);
    if (expected_len == 0 || expected_len > 100) return 10;
    void *lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (!lib) return 11;
    void *query_fn = dlsym(lib, "simple_provider_query_v1");
    void *invoke_fn = dlsym(lib, "simple_cli_command_invoke_v1");
    if (!query_fn || !invoke_fn) return 12;

    uint8_t query[44] = {0}, query_result[60] = {0};
    wr32(query, 44);
    wr64(query + 4, UINT64_C(5999723006133093425));
    wr32(query + 12, 1);
    wr64(query + 20, 1);
    if (rt_provider_query_v1_call((int64_t)(intptr_t)query_fn,
            (int64_t)(intptr_t)query, (int64_t)(intptr_t)query_result) != 0)
        return 13;
    if (rd32(query_result) != 0 || rd32(query_result + 4) != 1 ||
            rd32(query_result + 12) != 28 || rd64(query_result + 16) == 0)
        return 14;

    uint8_t request[35] = {0}, result[128] = {0};
    wr32(request, 28); wr32(request + 4, 3);
    wr32(request + 8, 28); wr32(request + 12, 3);
    wr32(request + 16, 31); wr32(request + 20, 4);
    wr32(request + 24, sizeof(result));
    memcpy(request + 28, "fmt", 3);
    /* Canonical empty argument list: count=0. */
    if (rt_cli_command_v1_call((int64_t)(intptr_t)invoke_fn,
            (int64_t)rd64(query_result + 16),
            (int64_t)rd64(query_result + 24),
            (int64_t)(intptr_t)request, sizeof(request),
            (int64_t)(intptr_t)result, sizeof(result)) != 0) return 15;
    if (rd32(result) != 0 || rd32(result + 4) != 20 ||
            rd32(result + 8) != expected_len ||
            memcmp(result + 20, expected, expected_len) != 0)
        return 16;
    if (dlclose(lib) != 0) return 17;
    puts("PASS cli_provider_v1_host_selfcheck");
    return 0;
}
