/* bench_2d_tiered.c — C reference with 2-loop structure for fair JIT comparison
 *
 * Loop 1 (warmup): simulates interpreter startup — unoptimized (-O0) path
 * Loop 2 (measured): simulates JIT-compiled native — optimized path
 *
 * Both loops compute the same work (sum of squares). The warmup loop
 * has volatile annotations to prevent compiler optimization, simulating
 * interpreted overhead. The measured loop is fully optimized.
 *
 * Compile:
 *   gcc -O2 -o bench_2d_tiered bench_2d_tiered.c -lm
 */
#define _POSIX_C_SOURCE 199309L

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#define WARMUP_CALLS   128
#define MEASURED_CALLS 2000
#define WORK_SIZE      1000

static double now_seconds(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

/* Unoptimized path — volatile prevents most optimization, simulating interpreter */
static int64_t __attribute__((noinline)) hot_compute_interp(int64_t n) {
    volatile int64_t sum = 0;
    volatile int64_t i = 0;
    while (i < n) {
        sum = sum + i * i;
        i = i + 1;
    }
    return sum;
}

/* Fully optimized path — simulates JIT-compiled native */
static int64_t __attribute__((noinline)) hot_compute_native(int64_t n) {
    int64_t sum = 0;
    for (int64_t i = 0; i < n; i++) {
        sum += i * i;
    }
    return sum;
}

int main(void) {
    printf("=== C Reference: 2-Loop JIT Comparison ===\n\n");

    /* Loop 1: Warmup (simulated interpreter) */
    printf("--- Loop 1: Warmup (volatile/unoptimized) ---\n");
    double t0 = now_seconds();
    volatile int64_t sink = 0;
    for (int i = 0; i < WARMUP_CALLS; i++) {
        sink += hot_compute_interp(WORK_SIZE);
    }
    double t1 = now_seconds();
    double warmup_ms = (t1 - t0) * 1000.0;
    printf("  Warmup: %d calls in %.3f ms\n", WARMUP_CALLS, warmup_ms);

    /* Loop 2: Measured (simulated native) */
    printf("\n--- Loop 2: Measured (fully optimized) ---\n");
    double t2 = now_seconds();
    for (int i = 0; i < MEASURED_CALLS; i++) {
        sink += hot_compute_native(WORK_SIZE);
    }
    double t3 = now_seconds();
    double measured_ms = (t3 - t2) * 1000.0;
    printf("  Measured: %d calls in %.3f ms\n", MEASURED_CALLS, measured_ms);

    /* Results */
    printf("\n--- Results ---\n");
    double per_call_warmup_us = warmup_ms * 1000.0 / WARMUP_CALLS;
    double per_call_measured_us = measured_ms * 1000.0 / MEASURED_CALLS;
    printf("  Per-call warmup (unoptimized): %.3f us\n", per_call_warmup_us);
    printf("  Per-call measured (optimized): %.3f us\n", per_call_measured_us);
    if (per_call_measured_us > 0.0) {
        printf("  Ratio (warmup/measured): %.2fx\n", per_call_warmup_us / per_call_measured_us);
    }
    printf("  (sink=%ld to prevent DCE)\n", (long)sink);

    return 0;
}
