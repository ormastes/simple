/*
 * C reference benchmark for ctype functions.
 * Mirrors bench_ctype.spl exactly so ops_per_ms values are directly comparable.
 *
 * Build:
 *   gcc -O2 -o build/bench_ctype_ref test/perf/ctype/bench_ctype_ref.c && ./build/bench_ctype_ref
 *
 * Comparison workflow:
 *   1. Run this binary  → captures C ops_per_ms per function
 *   2. Run:  bin/simple run test/perf/ctype/bench_ctype.spl
 *             → captures Simple interpreter ops_per_ms
 *   3. Run:  bin/simple build && <native output>
 *             → captures Simple native ops_per_ms
 *   4. Divide Simple / C to get the ratio (target: ≥ 0.50 native).
 *
 * The run_ctype_benchmarks.shs script automates steps 1-4.
 */

#include <stdio.h>
#include <stdint.h>
#include <time.h>

/* ---- timing ---- */
static int64_t now_micros(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000LL + (int64_t)ts.tv_nsec / 1000LL;
}

/* ---- ctype (mirrors runtime_ctype.c semantics, plain C, no <ctype.h> locale) ---- */
static int c_is_digit(int ch)  { return ch >= 48 && ch <= 57; }
static int c_is_upper(int ch)  { return ch >= 65 && ch <= 90; }
static int c_is_lower(int ch)  { return ch >= 97 && ch <= 122; }
static int c_is_alpha(int ch)  { return c_is_upper(ch) || c_is_lower(ch); }
static int c_is_alnum(int ch)  { return c_is_alpha(ch) || c_is_digit(ch); }
static int c_is_xdigit(int ch) {
    return c_is_digit(ch) || (ch >= 65 && ch <= 70) || (ch >= 97 && ch <= 102);
}
static int c_is_space(int ch)  {
    return ch == 32 || ch == 9 || ch == 10 || ch == 13 || ch == 11 || ch == 12;
}
static int c_to_lower(int ch)  { return c_is_upper(ch) ? ch + 32 : ch; }
static int c_to_upper(int ch)  { return c_is_lower(ch) ? ch - 32 : ch; }

/* ---- report ---- */
static void report(const char *bench, int64_t ops, int64_t micros, int64_t checksum) {
    if (micros <= 0) micros = 1;
    int64_t ops_per_ms = (ops * 1000LL) / micros;
    printf("[ctypebench] lang=c bench=%s ops=%lld micros=%lld ops_per_ms=%lld checksum=%lld\n",
           bench, (long long)ops, (long long)micros, (long long)ops_per_ms, (long long)checksum);
}

/* ---- benchmark helpers ---- */
#ifndef ITERS
#define ITERS     1000
#endif
#define ASCII_RANGE 128
#define TOTAL_OPS ((int64_t)ITERS * ASCII_RANGE)

#define BENCH_CLASSIFY(name, fn_expr) \
    static void bench_##name(void) { \
        int64_t chk = 0; \
        int64_t start = now_micros(); \
        for (int i = 0; i < ITERS; i++) { \
            for (int ch = 0; ch < ASCII_RANGE; ch++) { \
                if (fn_expr) chk++; \
            } \
        } \
        int64_t elapsed = now_micros() - start; \
        report(#name, TOTAL_OPS, elapsed, chk); \
    }

#define BENCH_MAP(name, fn_expr) \
    static void bench_##name(void) { \
        int64_t chk = 0; \
        int64_t start = now_micros(); \
        for (int i = 0; i < ITERS; i++) { \
            for (int ch = 0; ch < ASCII_RANGE; ch++) { \
                chk += fn_expr; \
            } \
        } \
        int64_t elapsed = now_micros() - start; \
        report(#name, TOTAL_OPS, elapsed, chk); \
    }

BENCH_CLASSIFY(is_digit,  c_is_digit(ch))
BENCH_CLASSIFY(is_upper,  c_is_upper(ch))
BENCH_CLASSIFY(is_lower,  c_is_lower(ch))
BENCH_CLASSIFY(is_alpha,  c_is_alpha(ch))
BENCH_CLASSIFY(is_alnum,  c_is_alnum(ch))
BENCH_CLASSIFY(is_xdigit, c_is_xdigit(ch))
BENCH_CLASSIFY(is_space,  c_is_space(ch))
BENCH_MAP(to_lower, c_to_lower(ch))
BENCH_MAP(to_upper, c_to_upper(ch))

int main(void) {
    printf("=== ctype microbenchmark: C reference (O2) ===\n");
    printf("iters=%d x ascii_range=%d = %lld calls per function\n\n",
           ITERS, ASCII_RANGE, (long long)TOTAL_OPS);

    bench_is_digit();
    bench_is_upper();
    bench_is_lower();
    bench_is_alpha();
    bench_is_alnum();
    bench_is_xdigit();
    bench_is_space();
    bench_to_lower();
    bench_to_upper();

    printf("\nDone. Output format: [ctypebench] lang=c bench=<name> ops=<n> micros=<us> ops_per_ms=<n> checksum=<n>\n");
    return 0;
}
