#include "../../../src/runtime/runtime_scv_wasm_ffi.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int runtime_alloc_attempts;
static int runtime_alloc_successes;
static int runtime_free_calls;
static int runtime_alloc_fail_at;

void *rt_alloc(int64_t size) {
    void *allocation;
    runtime_alloc_attempts++;
    if (runtime_alloc_fail_at > 0 &&
        runtime_alloc_attempts == runtime_alloc_fail_at) return NULL;
    if (size <= 0) return NULL;
    allocation = malloc((size_t)size);
    if (allocation != NULL) runtime_alloc_successes++;
    return allocation;
}

void rt_free(void *ptr) {
    if (ptr != NULL) runtime_free_calls++;
    free(ptr);
}

#define GRAMMAR_MAX INT64_C(1048576)
#define SOURCE_MAX INT64_C(16777216)
#define OUTPUT_MAX INT64_C(67108864)

static int load_calls;
static int parse_calls;
static int free_calls;
static int64_t load_result = 7;
static const char *parse_result = "copied-before-free";
static char *provider_output;
static int64_t expected_source_len;
static int source_contract_ok;

static int64_t typed_load(const char *path) {
    load_calls++;
    if (path == NULL || path[0] == '\0') return -90;
    return load_result;
}

static const char *typed_parse(int64_t handle, const char *source,
                               int64_t source_len) {
    parse_calls++;
    source_contract_ok = handle == 7 && source != NULL &&
                         source_len == expected_source_len &&
                         source[source_len] == '\0';
    return parse_result;
}

static void typed_free(int64_t handle) {
    free_calls++;
    if (handle != 7) source_contract_ok = 0;
    if (provider_output != NULL) memset(provider_output, 'X', (size_t)OUTPUT_MAX + 2);
}

static int64_t fn_address_load(void) { return (int64_t)(uintptr_t)&typed_load; }
static int64_t fn_address_parse(void) { return (int64_t)(uintptr_t)&typed_parse; }
static int64_t fn_address_free(void) { return (int64_t)(uintptr_t)&typed_free; }

static int check(int condition, const char *message) {
    if (!condition) fprintf(stderr, "FAIL: %s\n", message);
    return condition;
}

static void reset_calls(void) {
    load_calls = 0;
    parse_calls = 0;
    free_calls = 0;
    source_contract_ok = 0;
    load_result = 7;
    parse_result = "copied-before-free";
    expected_source_len = 0;
}

static void reset_runtime_allocator(int fail_at) {
    runtime_alloc_attempts = 0;
    runtime_alloc_successes = 0;
    runtime_free_calls = 0;
    runtime_alloc_fail_at = fail_at;
}

int main(void) {
    int failures = 0;
    const char grammar[] = "grammar.wasm";
    const char source[] = {'a', '\0', 'b'};
    int64_t result;

    reset_calls();
    expected_source_len = 3;
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result != 0, "valid typed call returns owned copy");
    failures += !check(load_calls == 1 && parse_calls == 1 && free_calls == 1,
                       "success calls load, parse, free exactly once");
    failures += !check(source_contract_ok, "source length and NUL sentinel preserved");
    failures += !check(strcmp((const char *)(uintptr_t)result,
                              "copied-before-free") == 0,
                       "result copied before provider free poisons storage");
    rt_free((void *)(uintptr_t)result);

    reset_calls();
    result = spl_scv_wasm_parse_blob_copy(0, fn_address_parse(), fn_address_free(),
            grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 0 && parse_calls == 0 && free_calls == 0,
                       "invalid function pointer makes no provider call");

    reset_calls();
    load_result = 0;
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 1 && parse_calls == 0 && free_calls == 0,
                       "load failure does not parse or free invalid handle");

    reset_calls();
    parse_result = NULL;
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 1 && parse_calls == 1 && free_calls == 1,
                       "null parse result still frees successful handle once");

    reset_calls();
    {
        char bad_grammar[] = {'a', '\0', 'b'};
        result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
                fn_address_free(), bad_grammar, 3, source, 3);
    }
    failures += !check(result == 0 && load_calls == 0 && parse_calls == 0 && free_calls == 0,
                       "embedded grammar NUL is rejected before callbacks");

    reset_calls();
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, GRAMMAR_MAX + 1, source, 3);
    failures += !check(result == 0 && load_calls == 0,
                       "grammar over maximum rejected before callbacks");
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, SOURCE_MAX + 1);
    failures += !check(result == 0 && load_calls == 0,
                       "source over maximum rejected before callbacks");

    reset_calls();
    {
        char *max_grammar = (char *)malloc((size_t)GRAMMAR_MAX + 1);
        char *max_source = (char *)malloc((size_t)SOURCE_MAX);
        if (max_grammar == NULL || max_source == NULL) {
            failures += !check(0, "allocate exact-boundary inputs");
        } else {
            memset(max_grammar, 'g', (size_t)GRAMMAR_MAX);
            max_grammar[GRAMMAR_MAX] = '\0';
            memset(max_source, 's', (size_t)SOURCE_MAX);
            expected_source_len = SOURCE_MAX;
            result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
                    fn_address_free(), max_grammar, GRAMMAR_MAX, max_source, SOURCE_MAX);
            failures += !check(result != 0 && load_calls == 1 && parse_calls == 1 &&
                               free_calls == 1 && source_contract_ok,
                               "exact grammar and source bounds are admitted");
            if (result != 0) rt_free((void *)(uintptr_t)result);
        }
        free(max_grammar);
        free(max_source);
    }

    reset_calls();
    provider_output = (char *)malloc((size_t)OUTPUT_MAX + 2);
    if (provider_output == NULL) {
        failures += !check(0, "allocate output boundary fixture");
    } else {
        memset(provider_output, 'o', (size_t)OUTPUT_MAX + 1);
        provider_output[OUTPUT_MAX] = '\0';
        parse_result = provider_output;
        result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
                fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
        failures += !check(result != 0 && free_calls == 1,
                           "exact output maximum is accepted and released once");
        if (result != 0) {
            failures += !check(((const char *)(uintptr_t)result)[OUTPUT_MAX] == '\0',
                               "max-size output copy is NUL terminated");
            rt_free((void *)(uintptr_t)result);
        }
        free(provider_output);
        provider_output = NULL;
    }

    reset_calls();
    provider_output = (char *)malloc((size_t)OUTPUT_MAX + 2);
    if (provider_output == NULL) {
        failures += !check(0, "allocate oversized output fixture");
    } else {
        memset(provider_output, 'o', (size_t)OUTPUT_MAX + 2);
        parse_result = provider_output;
        result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
                fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
        failures += !check(result == 0 && load_calls == 1 && parse_calls == 1 && free_calls == 1,
                           "oversized output rejected after exactly one provider free");
        free(provider_output);
        provider_output = NULL;
    }

    reset_calls();
    reset_runtime_allocator(1);
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 0 && parse_calls == 0 &&
                       free_calls == 0 && runtime_alloc_attempts == 1 &&
                       runtime_alloc_successes == 0 && runtime_free_calls == 0,
                       "grammar allocation failure makes no provider calls");
    failures += !check(runtime_alloc_successes == runtime_free_calls,
                       "grammar allocation failure leaves balanced runtime allocations");

    reset_calls();
    reset_runtime_allocator(2);
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 0 && parse_calls == 0 &&
                       free_calls == 0 && runtime_alloc_attempts == 2 &&
                       runtime_alloc_successes == 1 && runtime_free_calls == 1,
                       "source allocation failure frees grammar before provider calls");
    failures += !check(runtime_alloc_successes == runtime_free_calls,
                       "source allocation failure leaves balanced runtime allocations");

    reset_calls();
    reset_runtime_allocator(3);
    result = spl_scv_wasm_parse_blob_copy(fn_address_load(), fn_address_parse(),
            fn_address_free(), grammar, (int64_t)strlen(grammar), source, 3);
    failures += !check(result == 0 && load_calls == 1 && parse_calls == 1 &&
                       free_calls == 1 && runtime_alloc_attempts == 3 &&
                       runtime_alloc_successes == 2 && runtime_free_calls == 2,
                       "output allocation failure releases provider exactly once");
    failures += !check(runtime_alloc_successes == runtime_free_calls,
                       "output allocation failure leaves balanced runtime allocations");

    if (failures != 0) return 1;
    puts("PASS: typed SCV WASM FFI contract");
    return 0;
}
