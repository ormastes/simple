#include "simple_chromium_primitive_oracle.h"

#include <stdbool.h>
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef uint32_t (*abi_fn)(void);
typedef int64_t (*create_fn)(const uint8_t *, uint64_t);
typedef int32_t (*run_fn)(int64_t, const uint8_t *, uint64_t, uint8_t *, uint64_t, uint64_t *);
typedef int32_t (*error_fn)(int64_t, uint8_t *, uint64_t, uint64_t *);
typedef int32_t (*destroy_fn)(int64_t);

static int require(bool condition, const char *message) {
    if (condition) return 0;
    fprintf(stderr, "fixture failure: %s\n", message);
    return 1;
}

int main(int argc, char **argv) {
    if (argc != 2) return require(false, "library argument missing");
    void *library = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
    if (require(library != NULL, "dlopen")) return 1;
    abi_fn abi = (abi_fn)dlsym(library, "simple_chromium_oracle_abi_version");
    create_fn create = (create_fn)dlsym(library, "simple_chromium_oracle_create");
    run_fn run = (run_fn)dlsym(library, "simple_chromium_oracle_run_json_into");
    error_fn last_error = (error_fn)dlsym(library, "simple_chromium_oracle_last_error_into");
    destroy_fn destroy = (destroy_fn)dlsym(library, "simple_chromium_oracle_destroy");
    if (require(abi && create && run && last_error && destroy, "ABI v1 symbols")) return 1;
    if (require(abi() == SIMPLE_CHROMIUM_ORACLE_ABI_VERSION, "ABI version")) return 1;
    const uint8_t config[] = "{}";
    int64_t handle = create(config, sizeof(config) - 1);
    if (require(handle > 0, "create")) return 1;
    const uint8_t request[] = "{\"requested_primitives\":[\"rect\",\"text\",\"image\",\"pointer\",\"keyboard\",\"scroll\",\"resize\"]}";
    uint8_t short_buffer[4] = {'X', 'X', 'X', 'X'};
    uint64_t response_len = 0;
    if (require(run(handle, request, sizeof(request) - 1, short_buffer, sizeof(short_buffer), &response_len) == SIMPLE_CHROMIUM_ORACLE_BUFFER_TOO_SMALL, "short buffer")) return 1;
    if (require(short_buffer[0] == 'X' && response_len > sizeof(short_buffer), "no partial buffer write")) return 1;
    uint8_t *response = calloc(1, (size_t)response_len + 1);
    if (require(response != NULL, "response allocation")) return 1;
    if (require(run(handle, request, sizeof(request) - 1, response, response_len, &response_len) == SIMPLE_CHROMIUM_ORACLE_OK, "primitive response")) return 1;
    if (require(strstr((char *)response, "fixture-not-chromium") && strstr((char *)response, "web_input") && strstr((char *)response, "web_layout"), "fixture provenance and primitive layers")) return 1;
    const uint8_t bad_request[] = "{}";
    if (require(run(handle, bad_request, sizeof(bad_request) - 1, response, response_len, &response_len) == SIMPLE_CHROMIUM_ORACLE_UNSUPPORTED_PRIMITIVE, "unsupported primitive")) return 1;
    uint8_t error[256] = {0};
    uint64_t error_len = 0;
    if (require(last_error(handle, error, sizeof(error), &error_len) == SIMPLE_CHROMIUM_ORACLE_OK, "last error")) return 1;
    if (require(error_len > 0 && strstr((char *)error, "unsupported primitive"), "bounded last error text")) return 1;
    if (require(destroy(handle) == SIMPLE_CHROMIUM_ORACLE_OK, "destroy")) return 1;
    if (require(destroy(handle) == SIMPLE_CHROMIUM_ORACLE_RELEASED_HANDLE, "exact-once destroy")) return 1;
    free(response);
    dlclose(library);
    puts("CHROMIUM_ORACLE_FIXTURE_DYNLOAD_PASS provenance=fixture-not-chromium gpu=unavailable");
    return 0;
}
