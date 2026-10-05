#include "../simple_vector_kernel_abi_v1.h"
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef int32_t (*query_fn)(uint64_t, uint64_t);
typedef int64_t (*apply_fn)(int64_t, int64_t, int64_t);

static int fail(const char *message) {
    fprintf(stderr, "FAIL vector provider event selfcheck: %s\n", message);
    return 1;
}

static void query_request(uint8_t request[44], uint64_t capabilities) {
    memset(request, 0, 44);
    simple_vector_wr32(request, 44);
    simple_vector_wr64(request + 4, SIMPLE_VECTOR_KERNELS_V1_INTERFACE);
    simple_vector_wr32(request + 12, 1);
    simple_vector_wr32(request + 16, 0);
    simple_vector_wr64(request + 20, 1);
    simple_vector_wr64(request + 36, capabilities);
}

static int open_provider(const char *path, void **library, query_fn *query,
        apply_fn *apply, int64_t *handle) {
    *library = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (!*library) {
        const char *error = dlerror();
        return fail(error ? error : "dlopen failed");
    }
    *query = (query_fn)dlsym(*library, "simple_provider_query_v1");
    *apply = (apply_fn)dlsym(*library, "simple_vector_apply_v1");
    if (!*query || !*apply) return fail("provider entry point missing");
    uint8_t request[44], response[84];
    query_request(request, 15);
    if ((*query)((uintptr_t)request, (uintptr_t)response) != 0 ||
            simple_vector_rd32(response) != SIMPLE_VECTOR_OK)
        return fail("provider query failed");
    *handle = (int64_t)simple_vector_rd64(response + 16);
    if (*handle <= 0) return fail("provider returned an invalid capability handle");
    return 0;
}

static int apply_bitmap(apply_fn apply, int64_t handle, uint32_t words,
        uint32_t opcode, int invalid_descriptor) {
    uint32_t left[33], right[33], output[33];
    for (uint32_t i = 0; i < 33; ++i) {
        left[i] = i * UINT32_C(0x10201) | UINT32_C(0x80000001);
        right[i] = UINT32_C(0xf0f0a55a) ^ (i * UINT32_C(0x30007));
        output[i] = UINT32_C(0xdeadbeef);
    }
    uint8_t request[64] = {0}, response[24] = {0};
    simple_vector_wr32(request, invalid_descriptor ? 63 : 64);
    simple_vector_wr32(request + 4, opcode);
    simple_vector_wr64(request + 8, (uintptr_t)left);
    simple_vector_wr64(request + 16, (uint64_t)words * 4);
    simple_vector_wr64(request + 24, (uintptr_t)right);
    simple_vector_wr64(request + 32, (uint64_t)words * 4);
    simple_vector_wr64(request + 40, (uintptr_t)output);
    simple_vector_wr64(request + 48, (uint64_t)words * 4);
    if (apply(handle, (uintptr_t)request, (uintptr_t)response) != 0)
        return fail("apply returned a transport error");
    const uint32_t expected_status = invalid_descriptor
        ? SIMPLE_VECTOR_INVALID_REQUEST : SIMPLE_VECTOR_OK;
    if (simple_vector_rd32(response) != 24 ||
            simple_vector_rd32(response + 4) != expected_status)
        return fail("unexpected bitmap response status");
    if (invalid_descriptor) {
        for (uint32_t i = 0; i < words; ++i)
            if (output[i] != UINT32_C(0xdeadbeef)) return fail("invalid request wrote output");
        return 0;
    }
    if (simple_vector_rd64(response + 8) != (uint64_t)words * 4)
        return fail("successful bitmap response byte count differs");
    for (uint32_t i = 0; i < words; ++i) {
        const uint32_t expected = opcode == SIMPLE_VECTOR_BITMAP_AND_U32
            ? left[i] & right[i] : left[i] | right[i];
        if (output[i] != expected) return fail("bitmap output differs from scalar oracle");
    }
    return 0;
}

static int apply_http(apply_fn apply, int64_t handle, uint32_t opcode) {
    uint8_t input[193];
    memset(input, 'x', sizeof(input));
    uint64_t argument = 0;
    int64_t expected = -1;
    if (opcode == SIMPLE_VECTOR_HTTP_FIND_BYTE) {
        argument = 0x7f;
        expected = 130;
        input[130] = (uint8_t)argument;
    } else {
        expected = 128;
        input[128] = '\r';
        input[129] = '\n';
    }
    uint8_t request[64] = {0}, response[24] = {0};
    simple_vector_wr32(request, 64);
    simple_vector_wr32(request + 4, opcode);
    simple_vector_wr64(request + 8, (uintptr_t)input);
    simple_vector_wr64(request + 16, sizeof(input));
    simple_vector_wr64(request + 56, argument);
    if (apply(handle, (uintptr_t)request, (uintptr_t)response) != 0 ||
            simple_vector_rd32(response) != 24 ||
            simple_vector_rd32(response + 4) != SIMPLE_VECTOR_OK ||
            (int64_t)simple_vector_rd64(response + 16) != expected)
        return fail("HTTP vector operation response differs from scalar oracle");
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) return fail("usage: <provider.so> <scenario>");
    const char *path = argv[1], *scenario = argv[2];
    printf("SELF_PID=%ld\n", (long)getpid());
    fflush(stdout);
    if (strcmp(scenario, "no-load") == 0) return 0;

    void *library = NULL;
    query_fn query = NULL;
    apply_fn apply = NULL;
    int64_t handle = 0;
    if (open_provider(path, &library, &query, &apply, &handle) != 0) return 1;
    if (strcmp(scenario, "load-no-call") == 0) {
        if (dlclose(library) != 0) return fail("dlclose failed");
        return 0;
    }

    int result = 0;
    if (strcmp(scenario, "bitmap-tail") == 0)
        result = apply_bitmap(apply, handle, 15, SIMPLE_VECTOR_BITMAP_AND_U32, 0);
    else if (strcmp(scenario, "bitmap-33-and") == 0)
        result = apply_bitmap(apply, handle, 33, SIMPLE_VECTOR_BITMAP_AND_U32, 0);
    else if (strcmp(scenario, "bitmap-33-or") == 0)
        result = apply_bitmap(apply, handle, 33, SIMPLE_VECTOR_BITMAP_OR_U32, 0);
    else if (strcmp(scenario, "http-byte") == 0)
        result = apply_http(apply, handle, SIMPLE_VECTOR_HTTP_FIND_BYTE);
    else if (strcmp(scenario, "http-crlf") == 0)
        result = apply_http(apply, handle, SIMPLE_VECTOR_HTTP_FIND_CRLF);
    else if (strcmp(scenario, "invalid-request") == 0)
        result = apply_bitmap(apply, handle, 4, SIMPLE_VECTOR_BITMAP_AND_U32, 1);
    else if (strcmp(scenario, "forced-no-avx-bitmap") == 0) {
        uint8_t q[64] = {0}, r[24] = {0};
        uint32_t left[33] = {0}, right[33] = {0}, output[33] = {0};
        simple_vector_wr32(q, 64); simple_vector_wr32(q + 4, SIMPLE_VECTOR_BITMAP_AND_U32);
        simple_vector_wr64(q + 8, (uintptr_t)left); simple_vector_wr64(q + 16, sizeof(left));
        simple_vector_wr64(q + 24, (uintptr_t)right); simple_vector_wr64(q + 32, sizeof(right));
        simple_vector_wr64(q + 40, (uintptr_t)output); simple_vector_wr64(q + 48, sizeof(output));
        if (apply(handle, (uintptr_t)q, (uintptr_t)r) != 0 ||
                simple_vector_rd32(r + 4) != SIMPLE_VECTOR_FEATURE_UNAVAILABLE ||
                simple_vector_rd64(r + 8) != 0) result = fail("forced no-AVX bitmap was not refused");
    } else if (strcmp(scenario, "forced-no-avx-http") == 0 ||
            strcmp(scenario, "forced-no-bw-http") == 0) {
        uint8_t input[193], q[64] = {0}, r[24] = {0};
        memset(input, 'x', sizeof(input)); input[130] = 0x7f;
        simple_vector_wr32(q, 64); simple_vector_wr32(q + 4, SIMPLE_VECTOR_HTTP_FIND_BYTE);
        simple_vector_wr64(q + 8, (uintptr_t)input); simple_vector_wr64(q + 16, sizeof(input));
        simple_vector_wr64(q + 56, 0x7f);
        if (apply(handle, (uintptr_t)q, (uintptr_t)r) != 0 ||
                simple_vector_rd32(r + 4) != SIMPLE_VECTOR_FEATURE_UNAVAILABLE ||
                simple_vector_rd64(r + 8) != 0) result = fail("forced HTTP ISA refusal was not reported");
    } else result = fail("unknown scenario");
    if (dlclose(library) != 0) return fail("dlclose failed after apply");
    return result;
}
