#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

bool rt_coverage_enabled(void);
void rt_coverage_decision_probe(uint32_t, bool, const char *, uint32_t, uint32_t);
void rt_coverage_condition_probe(uint32_t, uint32_t, bool, const char *, uint32_t, uint32_t);
char *rt_coverage_dump_sdn(void);
void rt_coverage_free_sdn(char *);
void rt_coverage_clear(void);

int main(void) {
    assert(setenv("SIMPLE_COVERAGE", "1", 1) == 0);
    rt_coverage_clear();
    rt_coverage_decision_probe(9, true, "z.spl", 3, 4);
    rt_coverage_decision_probe(2, false, "a,spl", 1, 2);
    rt_coverage_decision_probe(2, true, "a%2Cspl", 1, 2);
    rt_coverage_condition_probe(9, 7, true, "z.spl", 3, 5);
    char *first = rt_coverage_dump_sdn();
    char *second = rt_coverage_dump_sdn();
    assert(first && second && strcmp(first, second) == 0);
    assert(strstr(first, "coverage_extension: decision-condition-v1\n"));
    assert(strstr(first, "    2, a%2Cspl, 1, 2, 0, 1\n"));
    assert(strstr(first, "    2, a%252Cspl, 1, 2, 1, 0\n"));
    assert(strstr(first, "    9, z.spl, 3, 4, 1, 0\n"));
    assert(strstr(first, "    9, 7, z.spl, 3, 5, 1, 0\n"));
    assert(strstr(first, "    2,") < strstr(first, "    9,"));
    rt_coverage_free_sdn(first);
    rt_coverage_free_sdn(second);
    rt_coverage_clear();
    assert(setenv("SIMPLE_COVERAGE", "0", 1) == 0);
    rt_coverage_decision_probe(1, true, "disabled.spl", 1, 1);
    first = rt_coverage_dump_sdn();
    assert(first && !strstr(first, "disabled.spl"));
    rt_coverage_free_sdn(first);
    return 0;
}
