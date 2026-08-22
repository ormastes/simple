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
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 1, 1, 0, 0) == 1);
    assert(rt_mcdc_collector_init_v1(storage, sizeof(storage), 7) == 0);
    assert(rt_mcdc_collector_init_v1(storage, sizeof(storage), 8) == 7);
    assert(rt_mcdc_claim_interpreter_owner_v1(7, 1) == 0);
    assert(rt_mcdc_claim_interpreter_owner_v1(7, 2) == 7);
    assert(rt_mcdc_record_vector_v1(8, 9, 2, 99, 3, 1, 1, 0, 0) == 5);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 1, 1, 0, 0) == 0);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 3, 1, 1, 1) == 0);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 4, 0, 1, 2, 0) == 2);
    assert(rt_mcdc_record_vector_v1(7, 9, 2, 99, 3, 0, 1, 2, 0) == 3);
    assert(rt_mcdc_collector_seal_v1(7) == 0);
    assert(rt_mcdc_snapshot_v1(vectors, 2, &snapshot) == 0);
    assert(snapshot.written == 2 && snapshot.overflowed &&
           snapshot.overflow_first == 2 && snapshot.overflow_count == 1);
    assert(vectors[0].decision_id == 9 && vectors[0].source_digest == 99 &&
           vectors[0].evaluated_mask == 3);
    assert(vectors[1].owner_sequence == 1 && vectors[1].outcome == 1);
    assert(rt_mcdc_release_interpreter_owner_v1(7, 1) == 0);
    rt_mcdc_collector_reset_v1();
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
