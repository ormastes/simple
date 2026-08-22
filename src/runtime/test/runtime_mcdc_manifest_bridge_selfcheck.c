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

    /* The report owner is the production join: manifest + sorted process
     * provenance + masking witnesses + governed exclusions + exact gate. */
    SimpleMcdcVectorV1 full_events[] = {
        {9, 2, 0, 99, 3, 2, 2, 3, 1, {0}},
        {9, 2, 0, 99, 3, 0, 1, 1, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 2, 1, {0}}
    };
    SimpleMcdcReportV1 report;
    assert(rt_mcdc_report_mcdp_v1(
               full_events, 3, wire, wire_size, NULL, 0, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_OK);
    assert(report.decisions == 1 && report.gross_conditions == 2 &&
           report.eligible_conditions == 2 &&
           report.covered_eligible_conditions == 2 && report.gate_passed == 1 &&
           report.event_count == 3 && report.witness_count == 2);
    uint8_t provenance[64];
    memcpy(provenance, report.provenance_sha256, sizeof(provenance));
    SimpleMcdcVectorV1 permuted[] = {
        full_events[2], full_events[0], full_events[1]
    };
    assert(rt_mcdc_report_mcdp_v1(
               permuted, 3, wire, wire_size, NULL, 0, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_OK);
    assert(memcmp(provenance, report.provenance_sha256, 64) == 0);

    /* V2 retains V1 behavior while materializing the complete bounded ABI:
       source span, binary identity, decision/condition totals and merge rows. */
    const SimpleMcdcSourceLocationV2 locations[] = {
        {9, 99, UINT64_C(0x55aa), 12, 7}
    };
    uint8_t binary_identity[64];
    memset(binary_identity, 'b', sizeof(binary_identity));
    SimpleMcdcDecisionReportV2 process_rows[2];
    SimpleMcdcReportV2 report_v2;
    SimpleMcdcVectorV1 process_a_events[] = {
        {9, 2, 0, 99, 3, 2, 2, 3, 1, {0}},
        {9, 2, 0, 99, 3, 0, 1, 1, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 2, 1, {0}}
    };
    assert(rt_mcdc_report_mcdp_v2(
               process_a_events, 3, wire, wire_size, binary_identity, NULL, 0,
               locations, 1, 10, SIMPLE_MCDC_REPORT_NORMAL_V1, 101, 1,
               programs, 1, tokens, 3, witnesses, 2, process_rows, 1,
               100, &report_v2) == SIMPLE_MCDC_V1_OK);
    assert(report_v2.gross_decisions == 1 &&
           report_v2.eligible_decisions == 1 &&
           report_v2.covered_decisions == 1 &&
           report_v2.gross_conditions == 2 &&
           report_v2.covered_conditions == 2 &&
           report_v2.witnessed_pairs == 2 && report_v2.process_count == 1);
    assert(process_rows[0].source_file_digest == UINT64_C(0x55aa) &&
           process_rows[0].line == 12 && process_rows[0].column == 7 &&
           process_rows[0].covered_mask == 3 &&
           memcmp(process_rows[0].binary_identity_sha256,
                  binary_identity, 64) == 0);
    SimpleMcdcVectorV1 process_b_events[] = {
        {9, 2, 0, 99, 3, 2, 2, 3, 1, {0}},
        {9, 2, 0, 99, 3, 0, 1, 1, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 2, 1, {0}}
    };
    assert(rt_mcdc_report_mcdp_v2(
               process_b_events, 3, wire, wire_size, binary_identity, NULL, 0,
               locations, 1, 10, SIMPLE_MCDC_REPORT_NORMAL_V1, 102, 1,
               programs, 1, tokens, 3, witnesses, 2, &process_rows[1], 1,
               100, &report_v2) == SIMPLE_MCDC_V1_OK);
    SimpleMcdcDecisionReportV2 merged_rows[1];
    assert(rt_mcdc_merge_reports_v2(process_rows, 2, merged_rows, 1,
                                     &report_v2) == SIMPLE_MCDC_V1_OK);
    assert(report_v2.process_count == 2 && report_v2.gross_decisions == 1 &&
           report_v2.covered_decisions == 1 &&
           report_v2.covered_conditions == 2 &&
           merged_rows[0].process_id == 0);
    SimpleMcdcDecisionReportV2 corrupted_rows[2];
    memcpy(corrupted_rows, process_rows, sizeof(corrupted_rows));
    corrupted_rows[1].covered_mask ^= 1;
    assert(rt_mcdc_merge_reports_v2(corrupted_rows, 2, merged_rows, 1,
                                     &report_v2) == SIMPLE_MCDC_V1_TAMPERED);
    corrupted_rows[1] = corrupted_rows[0];
    assert(rt_mcdc_merge_reports_v2(corrupted_rows, 2, merged_rows, 1,
                                     &report_v2) == SIMPLE_MCDC_V1_DUPLICATE);
    memcpy(corrupted_rows, process_rows, sizeof(corrupted_rows));
    corrupted_rows[1].process_id = 0;
    assert(rt_mcdc_merge_reports_v2(corrupted_rows, 2, merged_rows, 1,
                                     &report_v2) == SIMPLE_MCDC_V1_INVALID);
    memcpy(corrupted_rows, process_rows, sizeof(corrupted_rows));
    memset(corrupted_rows[1].binary_identity_sha256, 0, 64);
    assert(rt_mcdc_merge_reports_v2(corrupted_rows, 2, merged_rows, 1,
                                     &report_v2) == SIMPLE_MCDC_V1_INVALID);
    assert(rt_mcdc_merge_reports_v2(process_rows, 2, merged_rows, 0,
                                     &report_v2) == SIMPLE_MCDC_V1_OUTPUT_TOO_SMALL);

    SimpleMcdcVectorV1 incomplete[] = {
        {9, 2, 0, 99, 3, 0, 1, 1, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 2, 1, {0}}
    };
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, NULL, 0, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_GATE_FAILED);
    assert(report.eligible_conditions == 2 &&
           report.covered_eligible_conditions == 1 && report.gate_passed == 0);
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, NULL, 0, 10,
               SIMPLE_MCDC_REPORT_ALPHA_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_GATE_FAILED);
    assert(report.gate_passed == 0);
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, NULL, 0, 10,
               SIMPLE_MCDC_REPORT_BETA_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_GATE_FAILED);
    assert(report.gate_passed == 0);

    SimpleMcdcExclusionV1 exclusion = {
        .decision_id = 9, .source_digest = 99, .condition_mask = 2,
        .scenario_id = 101, .code_id = 102,
        .predicate_id = SIMPLE_MCDC_PREDICATE_CAPABILITY_UNAVAILABLE_V1,
        .capability_id = 77, .evidence_digest_hi = 123,
        .evidence_digest_lo = 456, .owner_id = 88,
        .observed_epoch = 4,
        .reviewed_epoch = 5, .expires_epoch = 20,
        .condition_count = 2,
        .kind = SIMPLE_MCDC_EXCLUSION_CAPABILITY_UNAVAILABLE_V1,
        .reason_length = 34,
        .reason = "device IRQ cannot be produced here"
    };
    SimpleMcdcExclusionV1 source_exclusion = exclusion;
    assert(rt_mcdc_exclusion_rows_exact_v1(
               &source_exclusion, &exclusion, 1) == SIMPLE_MCDC_V1_OK);
    source_exclusion.owner_id ^= 1u;
    assert(rt_mcdc_exclusion_rows_exact_v1(
               &source_exclusion, &exclusion, 1) == SIMPLE_MCDC_V1_EXCLUSION_INVALID);
    source_exclusion = exclusion;
    source_exclusion.reason[0] ^= 1u;
    assert(rt_mcdc_exclusion_rows_exact_v1(
               &source_exclusion, &exclusion, 1) == SIMPLE_MCDC_V1_EXCLUSION_INVALID);
    assert(rt_mcdc_exclusion_rows_exact_v1(
               NULL, NULL, 0) == SIMPLE_MCDC_V1_OK);
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_OK);
    assert(report.excluded_conditions == 1 && report.eligible_conditions == 1 &&
           report.covered_eligible_conditions == 1 &&
           report.validated_exclusions == 1 && report.gate_passed == 1);
    const uint32_t kinds[] = {
        SIMPLE_MCDC_EXCLUSION_CAPABILITY_UNAVAILABLE_V1,
        SIMPLE_MCDC_EXCLUSION_FIXTURE_UNAVAILABLE_V1,
        SIMPLE_MCDC_EXCLUSION_PLATFORM_INAPPLICABLE_V1,
        SIMPLE_MCDC_EXCLUSION_SAFETY_PROHIBITED_V1,
        SIMPLE_MCDC_EXCLUSION_UNCONTROLLABLE_NONDETERMINISM_V1
    };
    const uint64_t predicates[] = {
        SIMPLE_MCDC_PREDICATE_CAPABILITY_UNAVAILABLE_V1,
        SIMPLE_MCDC_PREDICATE_FIXTURE_UNAVAILABLE_V1,
        SIMPLE_MCDC_PREDICATE_PLATFORM_INAPPLICABLE_V1,
        SIMPLE_MCDC_PREDICATE_SAFETY_PROHIBITED_V1,
        SIMPLE_MCDC_PREDICATE_UNCONTROLLABLE_NONDETERMINISM_V1
    };
    for (size_t kind_index = 0; kind_index < 5; ++kind_index) {
        exclusion.kind = kinds[kind_index];
        exclusion.predicate_id = predicates[kind_index];
        assert(rt_mcdc_report_mcdp_v1(
                   incomplete, 2, wire, wire_size, &exclusion, 1, 10,
                   SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
                   witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_OK);
    }
    exclusion.predicate_id = SIMPLE_MCDC_PREDICATE_CAPABILITY_UNAVAILABLE_V1;
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EXCLUSION_INVALID);
    exclusion.kind = SIMPLE_MCDC_EXCLUSION_CAPABILITY_UNAVAILABLE_V1;
    exclusion.observed_epoch = 6;
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EXCLUSION_INVALID);
    exclusion.observed_epoch = 4;
    exclusion.expires_epoch = 9;
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EXCLUSION_INVALID);
    exclusion.expires_epoch = 20;
    exclusion.condition_mask = 3;
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EMPTY_DENOMINATOR);
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_ALPHA_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EMPTY_DENOMINATOR);
    assert(rt_mcdc_report_mcdp_v1(
               incomplete, 2, wire, wire_size, &exclusion, 1, 10,
               SIMPLE_MCDC_REPORT_BETA_V1, programs, 1, tokens, 3,
               witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_EMPTY_DENOMINATOR);

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

    const uint64_t report_iterations = UINT64_C(100000);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    tracked_allocations = 0;
    track_allocations = 1;
#endif
    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    for (uint64_t i = 0; i < report_iterations; ++i)
        assert(rt_mcdc_report_mcdp_v1(
                   full_events, 3, wire, wire_size, NULL, 0, 10,
                   SIMPLE_MCDC_REPORT_NORMAL_V1, programs, 1, tokens, 3,
                   witnesses, 2, 100, &report) == SIMPLE_MCDC_V1_OK);
    assert(clock_gettime(CLOCK_MONOTONIC, &finish) == 0);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    track_allocations = 0;
    assert(tracked_allocations == 0);
#endif
    const uint64_t report_elapsed_ns = (uint64_t)(
        (int64_t)(finish.tv_sec - start.tv_sec) * INT64_C(1000000000) +
        (int64_t)(finish.tv_nsec - start.tv_nsec));
    const uint64_t ns_per_report = report_elapsed_ns / report_iterations;
    printf("mcdc_report_perf iterations=%llu ns_per_report=%llu allocations=%llu workspace_bytes=%llu\n",
           (unsigned long long)report_iterations,
           (unsigned long long)ns_per_report,
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
           (unsigned long long)tracked_allocations,
#else
           0ull,
#endif
           (unsigned long long)(sizeof(full_events) + sizeof(programs) +
                                sizeof(tokens) + sizeof(witnesses) + sizeof(report)));
    assert(ns_per_report < UINT64_C(100000));

    const uint64_t v2_iterations = UINT64_C(100000);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    tracked_allocations = 0;
    track_allocations = 1;
#endif
    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    for (uint64_t i = 0; i < v2_iterations; ++i)
        assert(rt_mcdc_report_mcdp_v2(
                   process_a_events, 3, wire, wire_size, binary_identity, NULL, 0,
                   locations, 1, 10, SIMPLE_MCDC_REPORT_NORMAL_V1, 101, 1,
                   programs, 1, tokens, 3, witnesses, 2, process_rows, 1,
                   100, &report_v2) == SIMPLE_MCDC_V1_OK);
    assert(clock_gettime(CLOCK_MONOTONIC, &finish) == 0);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    track_allocations = 0;
    assert(tracked_allocations == 0);
#endif
    const uint64_t v2_report_elapsed_ns = (uint64_t)(
        (int64_t)(finish.tv_sec - start.tv_sec) * INT64_C(1000000000) +
        (int64_t)(finish.tv_nsec - start.tv_nsec));
    printf("mcdc_report_v2_perf iterations=%llu ns_per_report=%llu allocations=%llu workspace_bytes=%llu\n",
           (unsigned long long)v2_iterations,
           (unsigned long long)(v2_report_elapsed_ns / v2_iterations),
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
           (unsigned long long)tracked_allocations,
#else
           0ull,
#endif
           (unsigned long long)(sizeof(process_a_events) + sizeof(programs) +
                                sizeof(tokens) + sizeof(witnesses) +
                                sizeof(process_rows[0]) + sizeof(report_v2)));
    assert(v2_report_elapsed_ns / v2_iterations < UINT64_C(100000));
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    tracked_allocations = 0;
    track_allocations = 1;
#endif
    assert(clock_gettime(CLOCK_MONOTONIC, &start) == 0);
    for (uint64_t i = 0; i < v2_iterations; ++i)
        assert(rt_mcdc_merge_reports_v2(process_rows, 2, merged_rows, 1,
                                         &report_v2) == SIMPLE_MCDC_V1_OK);
    assert(clock_gettime(CLOCK_MONOTONIC, &finish) == 0);
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
    track_allocations = 0;
    assert(tracked_allocations == 0);
#endif
    const uint64_t v2_elapsed_ns = (uint64_t)(
        (int64_t)(finish.tv_sec - start.tv_sec) * INT64_C(1000000000) +
        (int64_t)(finish.tv_nsec - start.tv_nsec));
    printf("mcdc_report_v2_merge_perf iterations=%llu ns_per_merge=%llu allocations=%llu workspace_bytes=%llu\n",
           (unsigned long long)v2_iterations,
           (unsigned long long)(v2_elapsed_ns / v2_iterations),
#ifdef MCDC_SELFCHECK_WRAP_ALLOC
           (unsigned long long)tracked_allocations,
#else
           0ull,
#endif
           (unsigned long long)(sizeof(process_rows) + sizeof(merged_rows) +
                                sizeof(report_v2)));
    assert(v2_elapsed_ns / v2_iterations < UINT64_C(100000));
#endif
    return 0;
}
