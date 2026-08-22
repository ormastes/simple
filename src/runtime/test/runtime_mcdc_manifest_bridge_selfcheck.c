#include <assert.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <time.h>

#include "../runtime_mcdc_v1.h"

#ifdef MCDC_SELFCHECK_WRAP_ALLOC
static int track_allocations;
static uint64_t tracked_allocations;
void *__real_malloc(size_t);
void *__real_calloc(size_t, size_t);
void *__real_realloc(void *, size_t);
void *__wrap_malloc(size_t size) {
    if (track_allocations) ++tracked_allocations;
    return __real_malloc(size);
}
void *__wrap_calloc(size_t count, size_t size) {
    if (track_allocations) ++tracked_allocations;
    return __real_calloc(count, size);
}
void *__wrap_realloc(void *old, size_t size) {
    if (track_allocations) ++tracked_allocations;
    return __real_realloc(old, size);
}
#endif

int64_t rt_string_new(const uint8_t *bytes, uint64_t length) {
    uint8_t *copy = (uint8_t *)malloc((size_t)length + 1u);
    assert(copy);
    memcpy(copy, bytes, (size_t)length);
    copy[length] = 0;
    return (int64_t)(uintptr_t)copy;
}

static void put_u32(uint8_t *out, uint32_t value) {
    out[0] = (uint8_t)value;
    out[1] = (uint8_t)(value >> 8);
    out[2] = (uint8_t)(value >> 16);
    out[3] = (uint8_t)(value >> 24);
}

static void put_u64(uint8_t *out, uint64_t value) {
    put_u32(out, (uint32_t)value);
    put_u32(out + 4, (uint32_t)(value >> 32));
}

static size_t make_manifest(uint8_t *wire) {
    memset(wire, 0, 140);
    put_u32(wire, UINT32_C(0x5044434d));
    put_u32(wire + 4, 1);
    put_u64(wire + 8, 1);
    put_u64(wire + 16, 3);
    put_u64(wire + 88, 9);
    put_u64(wire + 96, 99);
    put_u32(wire + 104, 2);
    put_u32(wire + 108, 3);
    put_u64(wire + 112, 0);
    wire[120] = SIMPLE_MCDC_EXPR_CONDITION_V1;
    put_u32(wire + 124, 0);
    wire[128] = SIMPLE_MCDC_EXPR_CONDITION_V1;
    put_u32(wire + 132, 1);
    wire[136] = SIMPLE_MCDC_EXPR_OR_V1;
    put_u32(wire + 140, 0);
    put_u64(wire + 144, 1);
    put_u32(wire + 152, 3);
    memcpy(wire + 156, "sid", 3);
    uint8_t identity[64];
    assert(rt_mcdc_manifest_identity_v1(wire, 159, identity) ==
           SIMPLE_MCDC_V1_OK);
    memcpy(wire + 24, identity, sizeof(identity));
    return 159;
}

static size_t make_empty_manifest(uint8_t *wire) {
    memset(wire, 0, 96);
    put_u32(wire, UINT32_C(0x5044434d));
    put_u32(wire + 4, 1);
    uint8_t identity[64];
    assert(rt_mcdc_manifest_identity_v1(wire, 96, identity) ==
           SIMPLE_MCDC_V1_OK);
    memcpy(wire + 24, identity, sizeof(identity));
    return 96;
}

int main(void) {
    uint8_t wire[160];
    const size_t wire_size = make_manifest(wire);
    SimpleMcdcManifestInfoV1 info;
    assert(rt_mcdc_manifest_requirements_v1(wire, wire_size, &info) ==
           SIMPLE_MCDC_V1_OK);
    assert(info.program_count == 1 && info.token_count == 3 &&
           info.semantic_count == 1 && info.semantic_offset == 144);
    assert(memcmp(info.identity_sha256, wire + 24, 64) == 0);

    uint8_t empty_wire[96];
    assert(make_empty_manifest(empty_wire) == sizeof(empty_wire));
    assert(rt_mcdc_manifest_requirements_v1(empty_wire, sizeof(empty_wire),
                                            &info) == SIMPLE_MCDC_V1_OK);
    assert(info.program_count == 0 && info.token_count == 0);
    assert(memcmp(info.identity_sha256,
                  "aed8c54219a538aba0c6f80905a7bb1e28ccff9e376f4a9f5d00540c4ce8cfc8",
                  64) == 0);

    SimpleMcdcDecisionExprV1 programs[1];
    SimpleMcdcExprTokenV1 tokens[3];
    assert(rt_mcdc_manifest_decode_v1(wire, wire_size, programs, 0,
                                      tokens, 3, &info) ==
           SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL);
    assert(rt_mcdc_manifest_decode_v1(wire, wire_size, programs, 1,
                                      tokens, 3, &info) == SIMPLE_MCDC_V1_OK);
    assert(programs[0].decision_id == 9 && programs[0].source_digest == 99 &&
           programs[0].condition_count == 2 && programs[0].token_count == 3);
    assert(tokens[0].opcode == SIMPLE_MCDC_EXPR_CONDITION_V1 &&
           tokens[1].condition_index == 1 &&
           tokens[2].opcode == SIMPLE_MCDC_EXPR_OR_V1);

    SimpleMcdcVectorV1 events[] = {
        {9, 2, 0, 99, 3, 0, 1, 10, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 11, 1, {0}}
    };
    SimpleMcdcWitnessV1 witnesses[2];
    SimpleMcdcAnalysisV1 analysis;
    assert(rt_mcdc_analyze_masking_mcdp_v1(
               events, 2, wire, wire_size, programs, 1, tokens, 3,
               witnesses, 2, 20, &analysis, &info) == SIMPLE_MCDC_V1_OK);
    assert(analysis.covered_conditions == 1 && witnesses[0].policy == 1);

    /* Every canonical region is cryptographically bound. Structural validity
     * alone must not admit a manifest altered after compiler publication. */
    uint8_t tampered[160];
    memcpy(tampered, wire, wire_size);
    tampered[96] ^= 1u; /* source digest */
    assert(rt_mcdc_manifest_requirements_v1(tampered, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);
    memcpy(tampered, wire, wire_size);
    tampered[132] ^= 1u; /* condition ordinal */
    assert(rt_mcdc_manifest_requirements_v1(tampered, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);
    memcpy(tampered, wire, wire_size);
    tampered[158] ^= 1u; /* semantic identity */
    assert(rt_mcdc_manifest_requirements_v1(tampered, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);
    memcpy(tampered, wire, wire_size);
    tampered[16] ^= 1u; /* header token count */
    assert(rt_mcdc_manifest_requirements_v1(tampered, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);

    SimpleMcdcDecisionExprV1 with_unobserved[] = {
        programs[0], {10, 100, 1, 1, 3}
    };
    SimpleMcdcExprTokenV1 with_unobserved_tokens[] = {
        tokens[0], tokens[1], tokens[2],
        {SIMPLE_MCDC_EXPR_CONDITION_V1, {0}, 0}
    };
    assert(rt_mcdc_analyze_masking_v1(
               events, 2, with_unobserved, 2, with_unobserved_tokens, 4,
               witnesses, 2, 20, &analysis) == SIMPLE_MCDC_V1_OK);
    assert(analysis.decisions == 2 && analysis.gross_conditions == 3 &&
           analysis.covered_conditions == 1);

    wire[121] = 1;
    assert(rt_mcdc_manifest_requirements_v1(wire, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);
    wire[121] = 0;
    wire[158] = 0;
    assert(rt_mcdc_manifest_requirements_v1(wire, wire_size - 1, &info) ==
           SIMPLE_MCDC_V1_INVALID);
    wire[24] = 'A';
    assert(rt_mcdc_manifest_requirements_v1(wire, wire_size, &info) ==
           SIMPLE_MCDC_V1_INVALID);

#ifdef MCDC_SELFCHECK_PERF
    make_manifest(wire);
    const uint64_t iterations = UINT64_C(200000);
    struct timespec start, finish;
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    tracked_allocations = 0;
    track_allocations = 1;
#endif
    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    for (uint64_t i = 0; i < iterations; ++i)
        assert(rt_mcdc_manifest_requirements_v1(wire, wire_size, &info) ==
               SIMPLE_MCDC_V1_OK);
    assert(clock_gettime(CLOCK_MONOTONIC, &finish) == 0);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    track_allocations = 0;
    assert(tracked_allocations == 0);
#endif
    const uint64_t elapsed_ns = (uint64_t)(
        (int64_t)(finish.tv_sec - start.tv_sec) * INT64_C(1000000000) +
        (int64_t)(finish.tv_nsec - start.tv_nsec));
    const uint64_t ns_per_manifest = elapsed_ns / iterations;
    printf("mcdc_manifest_identity_perf iterations=%llu ns_per_manifest=%llu allocations=%llu\n",
           (unsigned long long)iterations,
           (unsigned long long)ns_per_manifest,
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
           (unsigned long long)tracked_allocations
#else
           0ull
#endif
    );
    assert(ns_per_manifest < UINT64_C(100000));
#endif
    return 0;
}
