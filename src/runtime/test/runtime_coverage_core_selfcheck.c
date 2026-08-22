#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "../runtime_mcdc_v1.h"

bool rt_coverage_enabled(void);
void rt_coverage_decision_probe(uint32_t, bool, const char *, uint32_t, uint32_t);
void rt_coverage_condition_probe(uint32_t, uint32_t, bool, const char *, uint32_t, uint32_t);
char *rt_coverage_dump_sdn_cstr(void);
int64_t rt_coverage_dump_sdn(void);
void rt_coverage_free_sdn(char *);
void rt_coverage_clear(void);

/* The focused object self-check intentionally links no full runtime provider.
 * Model the one text-construction ABI dependency and retain an owned copy so
 * the public wrapper can be exercised after it releases its temporary C text. */
int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    char *copy = (char *)malloc((size_t)len + 1U);
    assert(copy);
    if (len > 0) memcpy(copy, bytes, (size_t)len);
    copy[len] = '\0';
    return (int64_t)(uintptr_t)copy;
}

int main(void) {
    SimpleMcdcVectorV1 storage[2];
    SimpleMcdcVectorV1 vectors[2];
    SimpleMcdcSnapshotV1 snapshot;
    assert(rt_mcdc_dynamic_vector_patchpoint_v1(9, 2, 99, 3, 1, 0) == 0);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 1, 1, 0, 0) == 1);
    assert(rt_mcdc_collector_init_v1(storage, sizeof(storage), 7) == 0);
    assert(rt_mcdc_collector_init_v1(storage, sizeof(storage), 8) == 7);
    assert(rt_mcdc_claim_interpreter_owner_v1(7, 1) == 0);
    assert(rt_mcdc_claim_interpreter_owner_v1(7, 2) == 7);
    assert(rt_mcdc_configure_compiled_owner_v1(8, 4) == 5);
    assert(rt_mcdc_configure_compiled_owner_v1(7, 4) == 0);
    assert(rt_mcdc_collector_reset_checked_v1() == 7);
    assert(rt_mcdc_configure_compiled_owner_v1(7, 5) == 7);
    assert(rt_mcdc_record_vector_v1(8, 9, 2, 99, 3, 1, 1, 0, 0) == 5);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 1, 1, 0, 0) == 0);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 3, 1, 1, 1) == 0);
    assert(rt_mcdc_record_compiled_vector_v1(10, 2, 99, 3, 2, 1) == 3);
    assert(rt_mcdc_compiled_last_status_v1() == 3);
    uint64_t compiled_target = rt_mcdc_compiled_target_v1();
    assert(rt_mcdc_dynamic_bind_v1(compiled_target) == 0);
    assert(rt_mcdc_dynamic_bind_v1(compiled_target) == 7);
    assert(rt_mcdc_dynamic_vector_patchpoint_v1(10, 2, 99, 3, 2, 1) == 3);
    assert(rt_mcdc_dynamic_unbind_v1(compiled_target) == 0);
    assert(rt_mcdc_dynamic_settled_v1() == 0);
    assert(rt_mcdc_dynamic_vector_patchpoint_v1(10, 2, 99, 3, 2, 1) == 0);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 4, 0, 1, 2, 0) == 2);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 0, 1, 2, 0) == 3);
    assert(rt_mcdc_collector_seal_v1(7) == 0);
    assert(rt_mcdc_snapshot_v1(vectors, 2, &snapshot) == 0);
    assert(snapshot.written == 2 && snapshot.overflowed &&
           snapshot.overflow_first == 2 && snapshot.overflow_count == 3);
    assert(vectors[0].decision_id == 9 && vectors[0].source_digest == 99 &&
           vectors[0].evaluated_mask == 3);
    assert(vectors[1].owner_sequence == 1 && vectors[1].outcome == 1);
    SimpleMcdcWitnessV1 witnesses[2];
    SimpleMcdcAnalysisV1 analysis;
    SimpleMcdcVectorV1 swap = vectors[0]; vectors[0] = vectors[1]; vectors[1] = swap;
    assert(rt_mcdc_sort_vectors_v1(vectors, 2) == 0);
    assert(rt_mcdc_analyze_unique_v1(vectors, 2, witnesses, 2, 100, &analysis) == 0);
    assert(analysis.decisions == 1 && analysis.gross_conditions == 2);
    assert(analysis.covered_conditions == 1 && analysis.witness_count == 1);
    assert(analysis.pair_checks == 1 && analysis.pair_budget == 100);
    assert(witnesses[0].condition_index == 1 && witnesses[0].policy == 0);
    assert(witnesses[0].owner_a == 1 && witnesses[0].sequence_a == 0);
    assert(rt_mcdc_analyze_unique_v1(vectors, 2, NULL, 0, 100, &analysis) == 4);
    assert(analysis.covered_conditions == 1 && analysis.witness_count == 1);
    assert(rt_mcdc_analyze_unique_v1(vectors, 2, witnesses, 2, 0, &analysis) == 8);
    assert(analysis.pair_checks == 0);
    /* A || B: B is short-circuit unevaluated in the true observation.  The
       analyzer proves both completions of B preserve that outcome. */
    SimpleMcdcExprTokenV1 expression[] = {
        {SIMPLE_MCDC_EXPR_CONDITION_V1, {0}, 0},
        {SIMPLE_MCDC_EXPR_CONDITION_V1, {0}, 1},
        {SIMPLE_MCDC_EXPR_OR_V1, {0}, 0}
    };
    SimpleMcdcDecisionExprV1 program = {9, 99, 2, 3, 0};
    SimpleMcdcVectorV1 masking[] = {
        {9, 2, 0, 99, 3, 0, 1, 10, 0, {0}},
        {9, 2, 0, 99, 1, 1, 1, 11, 1, {0}}
    };
    assert(rt_mcdc_analyze_masking_v1(masking, 2, &program, 1,
                                      expression, 3, witnesses, 2, 20,
                                      &analysis) == 0);
    assert(analysis.covered_conditions == 1 && analysis.witness_count == 1);
    assert(witnesses[0].condition_index == 0 && witnesses[0].policy == 1);
    assert(rt_mcdc_analyze_masking_v1(masking, 2, &program, 1,
                                      expression, 3, witnesses, 2, 1,
                                      &analysis) == 8);
    SimpleMcdcExprTokenV1 bad_expression[3];
    memcpy(bad_expression, expression, sizeof(expression));
    bad_expression[2].opcode = 99;
    assert(rt_mcdc_analyze_masking_v1(masking, 2, &program, 1,
                                      bad_expression, 3, witnesses, 2, 20,
                                      &analysis) == 2);
    SimpleMcdcVectorV1 malformed[2] = {vectors[0], vectors[1]};
    malformed[1].condition_count = 3;
    assert(rt_mcdc_analyze_unique_v1(malformed, 2, witnesses, 2, 100, &analysis) == 2);
    malformed[1] = vectors[1];
    malformed[1].reserved[0] = 1;
    assert(rt_mcdc_sort_vectors_v1(malformed, 2) == 2);
    assert(rt_mcdc_release_interpreter_owner_v1(7, 1) == 0);
    assert(rt_mcdc_release_compiled_owner_v1(7, 4) == 0);
    assert(rt_mcdc_collector_reset_checked_v1() == 0);
    assert(setenv("SIMPLE_COVERAGE", "1", 1) == 0);
    rt_coverage_clear();
    rt_coverage_decision_probe(9, true, "z.spl", 3, 4);
    rt_coverage_decision_probe(9, false, "z.spl", 3, 4);
    rt_coverage_decision_probe(2, false, "a,spl", 1, 2);
    rt_coverage_decision_probe(2, true, "a%2Cspl", 1, 2);
    rt_coverage_condition_probe(9, 7, true, "z.spl", 3, 5);
    rt_coverage_condition_probe(9, 7, false, "z.spl", 3, 5);
    char *first = rt_coverage_dump_sdn_cstr();
    char *second = rt_coverage_dump_sdn_cstr();
    assert(first && second && strcmp(first, second) == 0);
    assert(strstr(first, "coverage_extension: decision-condition-v1\n"));
    assert(strstr(first, "    2, a%2Cspl, 1, 2, 0, 1\n"));
    assert(strstr(first, "    2, a%252Cspl, 1, 2, 1, 0\n"));
    /* One exact source identity must retain both outcomes for decisions and
       conditions.  Separate-path hits could otherwise make coverage appear
       complete while no owner/span row is actually branch-complete. */
    assert(strstr(first, "    9, z.spl, 3, 4, 1, 1\n"));
    assert(strstr(first, "    9, 7, z.spl, 3, 5, 1, 1\n"));
    assert(strstr(first, "    2,") < strstr(first, "    9,"));
    char *wrapped = (char *)(uintptr_t)rt_coverage_dump_sdn();
    assert(wrapped && strcmp(first, wrapped) == 0);
    free(wrapped);
    rt_coverage_free_sdn(first);
    rt_coverage_free_sdn(second);
    rt_coverage_clear();
    assert(setenv("SIMPLE_COVERAGE", "0", 1) == 0);
    rt_coverage_decision_probe(1, true, "disabled.spl", 1, 1);
    first = rt_coverage_dump_sdn_cstr();
    assert(first && !strstr(first, "disabled.spl"));
    rt_coverage_free_sdn(first);
    return 0;
}
