/* Regression for transient_empty_scope_highwater_scan_2026_10_12.
 *
 * After one scope allocates and reclaims a 750,000-object cohort, the
 * transient raw-allocation table keeps its high-water capacity (~2M slots)
 * with zero live entries. An empty begin/end scope must not rescan that
 * capacity. Built against the real owner1 runtime_native.c/runtime_memory.c
 * (see run_transient_empty_scope_test.shs).
 *
 * Measured on Linux x86_64, 2026-11-26: fixed runtime p95 ~0.05 us per empty
 * scope; with the early return in rt_core_reclaim_transient_raw disabled,
 * p95 ~13,400 us. The 50 us bound leaves >1000x margin either way, so it is
 * not timing-flaky but still fails on any return of the high-water scan. */
#include "runtime.h"
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define COHORT 750000
#define SAMPLES 21
#define SCOPES_PER_SAMPLE 10
#define P95_LIMIT_US 50.0

static int compare_double(const void* a, const void* b) {
    double x = *(const double*)a;
    double y = *(const double*)b;
    return (x > y) - (x < y);
}

static double now_us(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (double)t.tv_sec * 1e6 + (double)t.tv_nsec / 1e3;
}

int main(void) {
    if (!rt_transient_array_scope_begin()) return 2;
    for (int i = 0; i < COHORT; i++) {
        if (rt_alloc(8) == NULL) return 3;
    }
    if (!rt_transient_array_scope_end()) return 4;

    double per_scope_us[SAMPLES];
    for (int s = 0; s < SAMPLES; s++) {
        double start = now_us();
        for (int k = 0; k < SCOPES_PER_SAMPLE; k++) {
            if (!rt_transient_array_scope_begin()) return 5;
            if (!rt_transient_array_scope_end()) return 6;
        }
        per_scope_us[s] = (now_us() - start) / SCOPES_PER_SAMPLE;
    }
    qsort(per_scope_us, SAMPLES, sizeof(double), compare_double);
    double p50 = per_scope_us[SAMPLES / 2];
    double p95 = per_scope_us[SAMPLES - 2];
    printf("empty transient scope after %d-object cohort: p50=%.3fus p95=%.3fus\n",
           COHORT, p50, p95);
    if (p95 >= P95_LIMIT_US) {
        printf("FAIL empty scope p95 %.3fus >= %.1fus (high-water scan regressed)\n",
               p95, P95_LIMIT_US);
        return 1;
    }
    puts("PASS empty transient scopes skip the high-water scan");
    return 0;
}
