#include "runtime_scv_wasm_ffi.h"

#include "runtime.h"

#include <stddef.h>
#include <stdint.h>
#include <string.h>

#define SCV_WASM_GRAMMAR_MAX_BYTES INT64_C(1048576)
#define SCV_WASM_SOURCE_MAX_BYTES INT64_C(16777216)
#define SCV_WASM_OUTPUT_MAX_BYTES INT64_C(67108864)

typedef int64_t (*scv_wasm_load_fn)(const char *grammar_path);
typedef const char *(*scv_wasm_parse_fn)(int64_t handle,
                                         const char *source,
                                         int64_t source_len);
typedef void (*scv_wasm_free_fn)(int64_t handle);

int64_t spl_scv_wasm_parse_blob_copy(int64_t load_fn, int64_t parse_fn,
                                    int64_t free_fn, const char *grammar_ptr,
                                    int64_t grammar_len, const char *source_ptr,
                                    int64_t source_len) {
    scv_wasm_load_fn load;
    scv_wasm_parse_fn parse;
    scv_wasm_free_fn release;
    char *grammar_copy = NULL;
    char *source_copy = NULL;
    char *output_copy = NULL;
    const char *provider_output = NULL;
    int64_t handle = 0;
    int64_t output_len = 0;
    int64_t result = 0;

    if (load_fn <= 0 || parse_fn <= 0 || free_fn <= 0 ||
        grammar_ptr == NULL || grammar_len < 1 ||
        grammar_len > SCV_WASM_GRAMMAR_MAX_BYTES ||
        source_len < 0 || source_len > SCV_WASM_SOURCE_MAX_BYTES ||
        (source_len > 0 && source_ptr == NULL)) {
        return 0;
    }
    if (memchr(grammar_ptr, '\0', (size_t)grammar_len) != NULL) return 0;

    grammar_copy = (char *)rt_alloc(grammar_len + 1);
    if (grammar_copy == NULL) goto cleanup;
    memcpy(grammar_copy, grammar_ptr, (size_t)grammar_len);
    grammar_copy[grammar_len] = '\0';

    source_copy = (char *)rt_alloc(source_len + 1);
    if (source_copy == NULL) goto cleanup;
    if (source_len > 0) memcpy(source_copy, source_ptr, (size_t)source_len);
    source_copy[source_len] = '\0';

    load = (scv_wasm_load_fn)(uintptr_t)load_fn;
    parse = (scv_wasm_parse_fn)(uintptr_t)parse_fn;
    release = (scv_wasm_free_fn)(uintptr_t)free_fn;

    handle = load(grammar_copy);
    if (handle <= 0) goto cleanup;

    provider_output = parse(handle, source_copy, source_len);
    if (provider_output == NULL) goto release_provider;

    while (output_len <= SCV_WASM_OUTPUT_MAX_BYTES &&
           provider_output[output_len] != '\0') {
        output_len++;
    }
    if (output_len > SCV_WASM_OUTPUT_MAX_BYTES) goto release_provider;

    output_copy = (char *)rt_alloc(output_len + 1);
    if (output_copy == NULL) goto release_provider;
    memcpy(output_copy, provider_output, (size_t)output_len);
    output_copy[output_len] = '\0';
    result = (int64_t)(uintptr_t)output_copy;

release_provider:
    release(handle);
cleanup:
    if (grammar_copy != NULL) rt_free(grammar_copy);
    if (source_copy != NULL) rt_free(source_copy);
    if (result == 0 && output_copy != NULL) rt_free(output_copy);
    return result;
}
