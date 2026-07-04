/*
 * accelerator_perf_smoke.c — native SciLib accelerator performance smoke.
 *
 * This replaces the Python ctypes runner in check-scilib-accelerator-perf.shs.
 * The shell script still builds optional backends; this helper loads them,
 * validates small deterministic fixtures, records timings, and emits key=value
 * evidence for the gate.
 */

#define _POSIX_C_SOURCE 200809L

#include <ctype.h>
#include <dlfcn.h>
#include <math.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>

struct report_state {
    char failures[8192];
};

static double monotonic_ms(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
        return 0.0;
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1000000.0;
}

static int64_t f64_to_bits(double value)
{
    int64_t bits = 0;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

static double bits_to_f64(int64_t bits)
{
    double value = 0.0;
    memcpy(&value, &bits, sizeof(value));
    return value;
}

static void add_failure(struct report_state *state, const char *failure)
{
    if (state->failures[0] != '\0')
        strncat(state->failures, ",", sizeof(state->failures) - strlen(state->failures) - 1);
    strncat(state->failures, failure, sizeof(state->failures) - strlen(state->failures) - 1);
}

static bool close_enough(double got, double want, double eps)
{
    return fabs(got - want) <= eps;
}

static bool require_close(char *error, size_t error_len, const char *label, double got, double want, double eps)
{
    if (close_enough(got, want, eps))
        return true;
    snprintf(error, error_len, "%s:got %.17g expected %.17g", label, got, want);
    return false;
}

static double scalar_dot(const double *x, const double *y, int64_t n)
{
    double total = 0.0;
    for (int64_t i = 0; i < n; ++i)
        total += x[i] * y[i];
    return total;
}

static void scalar_gemv(const double *a, const double *x, const double *y,
                        double *out, int64_t rows, int64_t cols,
                        double alpha, double beta)
{
    for (int64_t row = 0; row < rows; ++row) {
        double total = beta * y[row];
        for (int64_t col = 0; col < cols; ++col)
            total += alpha * a[row * cols + col] * x[col];
        out[row] = total;
    }
}

static void scalar_gemm(const double *a, const double *b, double *out,
                        int64_t rows, int64_t cols, int64_t inner)
{
    for (int64_t row = 0; row < rows; ++row) {
        for (int64_t col = 0; col < cols; ++col) {
            double total = 0.0;
            for (int64_t k = 0; k < inner; ++k)
                total += a[row * inner + k] * b[k * cols + col];
            out[row * cols + col] = total;
        }
    }
}

static bool scalar_solve(const double *a, const double *b, double *out, int64_t n)
{
    double *mat = (double *)malloc((size_t)(n * n) * sizeof(double));
    double *rhs = (double *)malloc((size_t)n * sizeof(double));
    if (mat == NULL || rhs == NULL) {
        free(mat);
        free(rhs);
        return false;
    }
    memcpy(mat, a, (size_t)(n * n) * sizeof(double));
    memcpy(rhs, b, (size_t)n * sizeof(double));

    for (int64_t pivot = 0; pivot < n; ++pivot) {
        int64_t pivot_row = pivot;
        double pivot_abs = fabs(mat[pivot * n + pivot]);
        for (int64_t row = pivot + 1; row < n; ++row) {
            double candidate = fabs(mat[row * n + pivot]);
            if (candidate > pivot_abs) {
                pivot_abs = candidate;
                pivot_row = row;
            }
        }
        if (pivot_abs == 0.0) {
            free(mat);
            free(rhs);
            return false;
        }
        if (pivot_row != pivot) {
            for (int64_t col = 0; col < n; ++col) {
                double tmp = mat[pivot * n + col];
                mat[pivot * n + col] = mat[pivot_row * n + col];
                mat[pivot_row * n + col] = tmp;
            }
            double tmp_rhs = rhs[pivot];
            rhs[pivot] = rhs[pivot_row];
            rhs[pivot_row] = tmp_rhs;
        }
        for (int64_t row = pivot + 1; row < n; ++row) {
            double factor = mat[row * n + pivot] / mat[pivot * n + pivot];
            for (int64_t col = pivot; col < n; ++col)
                mat[row * n + col] -= factor * mat[pivot * n + col];
            rhs[row] -= factor * rhs[pivot];
        }
    }

    for (int64_t row = n - 1; row >= 0; --row) {
        double total = rhs[row];
        for (int64_t col = row + 1; col < n; ++col)
            total -= mat[row * n + col] * out[col];
        out[row] = total / mat[row * n + row];
    }
    free(mat);
    free(rhs);
    return true;
}

static bool scalar_inverse(const double *a, double *out, int64_t n)
{
    double *rhs = (double *)calloc((size_t)n, sizeof(double));
    double *solved = (double *)calloc((size_t)n, sizeof(double));
    if (rhs == NULL || solved == NULL) {
        free(rhs);
        free(solved);
        return false;
    }
    for (int64_t col = 0; col < n; ++col) {
        memset(rhs, 0, (size_t)n * sizeof(double));
        memset(solved, 0, (size_t)n * sizeof(double));
        rhs[col] = 1.0;
        if (!scalar_solve(a, rhs, solved, n)) {
            free(rhs);
            free(solved);
            return false;
        }
        for (int64_t row = 0; row < n; ++row)
            out[row * n + col] = solved[row];
    }
    free(rhs);
    free(solved);
    return true;
}

static void fill_periodic(double *values, int64_t n, int mod, int shift, double scale)
{
    for (int64_t i = 0; i < n; ++i)
        values[i] = (double)(i % mod - shift) * scale;
}

static void fill_solve_fixture(double *a, int64_t n)
{
    for (int64_t row = 0; row < n; ++row) {
        for (int64_t col = 0; col < n; ++col)
            a[row * n + col] = row == col ? 2.0 : 1.0 / (double)(1 + row + col);
        a[row * n + row] += (double)n;
    }
}

typedef void (*timed_fn)(void *);

static double time_loop(int count, timed_fn fn, void *ctx)
{
    double start = monotonic_ms();
    for (int i = 0; i < count; ++i)
        fn(ctx);
    return (monotonic_ms() - start) * 1000.0 / (double)count;
}

struct dot_ctx {
    const double *x;
    const double *y;
    int64_t n;
    double sink;
};

static void time_scalar_dot(void *raw)
{
    struct dot_ctx *ctx = (struct dot_ctx *)raw;
    ctx->sink += scalar_dot(ctx->x, ctx->y, ctx->n);
}

struct gemv_ctx {
    const double *a;
    const double *x;
    const double *y;
    double *out;
    int64_t rows;
    int64_t cols;
};

static void time_scalar_gemv(void *raw)
{
    struct gemv_ctx *ctx = (struct gemv_ctx *)raw;
    scalar_gemv(ctx->a, ctx->x, ctx->y, ctx->out, ctx->rows, ctx->cols, 2.0, 3.0);
}

struct gemm_ctx {
    const double *a;
    const double *b;
    double *out;
    int64_t rows;
    int64_t cols;
    int64_t inner;
};

static void time_scalar_gemm(void *raw)
{
    struct gemm_ctx *ctx = (struct gemm_ctx *)raw;
    scalar_gemm(ctx->a, ctx->b, ctx->out, ctx->rows, ctx->cols, ctx->inner);
}

struct solve_ctx {
    const double *a;
    const double *b;
    double *out;
    int64_t n;
};

static void time_scalar_solve(void *raw)
{
    struct solve_ctx *ctx = (struct solve_ctx *)raw;
    memset(ctx->out, 0, (size_t)ctx->n * sizeof(double));
    (void)scalar_solve(ctx->a, ctx->b, ctx->out, ctx->n);
}

struct inverse_ctx {
    const double *a;
    double *out;
    int64_t n;
};

static void time_scalar_inverse(void *raw)
{
    struct inverse_ctx *ctx = (struct inverse_ctx *)raw;
    (void)scalar_inverse(ctx->a, ctx->out, ctx->n);
}

static void run_scalar_baseline(void)
{
    int64_t n = 4096;
    double *x = (double *)malloc((size_t)n * sizeof(double));
    double *y = (double *)malloc((size_t)n * sizeof(double));
    fill_periodic(x, n, 17, 8, 0.25);
    fill_periodic(y, n, 13, 6, 0.5);
    struct dot_ctx dot = {x, y, n, 0.0};
    double dot_us = time_loop(10, time_scalar_dot, &dot);

    int64_t gemv_rows = 64;
    int64_t gemv_cols = 32;
    double gemv_a[64 * 32];
    double gemv_x[32];
    double gemv_y[64];
    double gemv_out[64];
    fill_periodic(gemv_a, gemv_rows * gemv_cols, 19, 9, 0.0625);
    fill_periodic(gemv_x, gemv_cols, 17, 8, 0.125);
    fill_periodic(gemv_y, gemv_rows, 5, 2, 0.25);
    struct gemv_ctx gemv = {gemv_a, gemv_x, gemv_y, gemv_out, gemv_rows, gemv_cols};
    double gemv_us = time_loop(10, time_scalar_gemv, &gemv);

    int64_t rows = 32;
    int64_t cols = 32;
    int64_t inner = 32;
    double a[32 * 32];
    double b[32 * 32];
    double c[32 * 32];
    fill_periodic(a, rows * inner, 11, 5, 0.125);
    fill_periodic(b, inner * cols, 7, 3, 0.25);
    struct gemm_ctx gemm = {a, b, c, rows, cols, inner};
    double gemm_us = time_loop(3, time_scalar_gemm, &gemm);

    int64_t solve_n = 16;
    double solve_a[16 * 16];
    double solve_b[16];
    double solve_out[16];
    double inv_out[16 * 16];
    fill_solve_fixture(solve_a, solve_n);
    fill_periodic(solve_b, solve_n, 9, 4, 0.5);
    struct solve_ctx solve = {solve_a, solve_b, solve_out, solve_n};
    struct inverse_ctx inv = {solve_a, inv_out, solve_n};
    double solve_us = time_loop(10, time_scalar_solve, &solve);
    double inv_us = time_loop(3, time_scalar_inverse, &inv);

    printf("scalar_fallback_perf_available=true\n");
    printf("scalar_dot_4096_us=%.3f\n", dot_us);
    printf("scalar_gemv_64x32_us=%.3f\n", gemv_us);
    printf("scalar_gemm_32x32_us=%.3f\n", gemm_us);
    printf("scalar_solve_16_us=%.3f\n", solve_us);
    printf("scalar_inv_16_us=%.3f\n", inv_us);
    free(x);
    free(y);
}

static bool cpuinfo_contains(const char *needle)
{
    FILE *file = fopen("/proc/cpuinfo", "r");
    if (file == NULL)
        return false;
    char line[4096];
    bool found = false;
    while (fgets(line, sizeof(line), file) != NULL) {
        for (char *p = line; *p != '\0'; ++p)
            *p = (char)tolower((unsigned char)*p);
        if (strstr(line, needle) != NULL) {
            found = true;
            break;
        }
    }
    fclose(file);
    return found;
}

static void run_simd(struct report_state *state, double max_spec_ms, int64_t max_op_ns)
{
    const char *profiles[] = {"avx512", "avx2", "sse2", "neon", "asimd", "rvv"};
    char profile_text[128] = "";
    for (size_t i = 0; i < sizeof(profiles) / sizeof(profiles[0]); ++i) {
        if (cpuinfo_contains(profiles[i])) {
            if (profile_text[0] != '\0')
                strncat(profile_text, ",", sizeof(profile_text) - strlen(profile_text) - 1);
            strncat(profile_text, profiles[i], sizeof(profile_text) - strlen(profile_text) - 1);
        }
    }
    if (profile_text[0] == '\0') {
        printf("simd_perf_available=false\n");
        printf("simd_perf_reason=no known SIMD cpu profile detected\n");
        return;
    }
    printf("simd_perf_available=true\n");
    printf("simd_profile=%s\n", profile_text);

    const char *specs[] = {
        "test/03_system/feature/scilib/linalg_simd_spec.spl",
        "test/03_system/feature/scilib/simd_f32_spec.spl",
    };
    const char *keys[] = {"linalg_simd", "simd_f32"};
    double total_ms = 0.0;
    for (size_t i = 0; i < sizeof(specs) / sizeof(specs[0]); ++i) {
        char cmd[512];
        snprintf(cmd, sizeof(cmd), "bin/simple test %s --mode=interpreter --no-cache >/dev/null 2>&1", specs[i]);
        double start = monotonic_ms();
        int rc = system(cmd);
        double elapsed_ms = monotonic_ms() - start;
        total_ms += elapsed_ms;
        printf("simd_%s_spec_ms=%.3f\n", keys[i], elapsed_ms);
        if (rc != 0) {
            char failure[128];
            snprintf(failure, sizeof(failure), "simd_%s_spec_failed", keys[i]);
            add_failure(state, failure);
        }
    }
    printf("simd_spec_total_ms=%.3f\n", total_ms);
    if (total_ms > max_spec_ms) {
        char failure[128];
        snprintf(failure, sizeof(failure), "simd_spec_total_ms>%.3f", max_spec_ms);
        add_failure(state, failure);
    }

    const char *expected[] = {
        "simd_f64_dot_avg_ns",
        "simd_f64_axpy_avg_ns",
        "simd_f32_dot_avg_ns",
        "simd_f32_axpy_avg_ns",
        "simd_ndarray_f64_add_avg_ns",
        "simd_ndarray_f64_sum_avg_ns",
        "simd_ndarray_f64_square_avg_ns",
        "simd_ndarray_f64_abs_avg_ns",
        "simd_ndarray_f64_scalar_mul_avg_ns",
        "simd_ndarray_f32_sum_avg_ns",
        "simd_ndarray_f32_scalar_mul_avg_ns",
        "simd_ndarray_f32_scalar_div_avg_ns",
        "simd_ndarray_f32_square_avg_ns",
        "simd_ndarray_f32_abs_avg_ns",
    };
    bool observed[sizeof(expected) / sizeof(expected[0])];
    memset(observed, 0, sizeof(observed));

    FILE *pipe = popen("bin/simple run test/05_perf/scilib_simd_ops_perf_spec.spl --mode=interpreter 2>&1", "r");
    if (pipe == NULL) {
        add_failure(state, "simd_ops_perf_spec_failed");
        return;
    }
    char line[512];
    while (fgets(line, sizeof(line), pipe) != NULL) {
        char *start = line;
        while (*start == ' ' || *start == '\t')
            ++start;
        char *eq = strchr(start, '=');
        if (eq == NULL || strncmp(start, "simd_", 5) != 0 || strstr(start, "_avg_ns=") == NULL)
            continue;
        *eq = '\0';
        char *value_text = eq + 1;
        value_text[strcspn(value_text, "\r\n")] = '\0';
        for (size_t i = 0; i < sizeof(expected) / sizeof(expected[0]); ++i) {
            if (strcmp(start, expected[i]) != 0)
                continue;
            char *end = NULL;
            long long value = strtoll(value_text, &end, 10);
            if (end == value_text || *end != '\0') {
                char failure[128];
                snprintf(failure, sizeof(failure), "%s_not_numeric", expected[i]);
                add_failure(state, failure);
                continue;
            }
            observed[i] = true;
            printf("%s=%lld\n", expected[i], value);
            if (value <= 0) {
                char failure[128];
                snprintf(failure, sizeof(failure), "%s<=0", expected[i]);
                add_failure(state, failure);
            }
            if (value > max_op_ns) {
                char failure[128];
                snprintf(failure, sizeof(failure), "%s>%lld", expected[i], (long long)max_op_ns);
                add_failure(state, failure);
            }
        }
    }
    int rc = pclose(pipe);
    if (rc != 0) {
        add_failure(state, "simd_ops_perf_spec_failed");
        return;
    }
    for (size_t i = 0; i < sizeof(expected) / sizeof(expected[0]); ++i) {
        if (!observed[i]) {
            char failure[128];
            snprintf(failure, sizeof(failure), "missing_%s", expected[i]);
            add_failure(state, failure);
        }
    }
}

#include "accelerator_perf_smoke_cuda.inc"
#include "accelerator_perf_smoke_torch.inc"

int main(int argc, char **argv)
{
    if (argc != 7) {
        fprintf(stderr, "usage: accelerator_perf_smoke BUILD_DIR MAX_LOAD_MS MAX_OP_US MAX_RSS_KB SIMD_MAX_SPEC_MS SIMD_MAX_OP_NS\n");
        return 2;
    }

    const char *build_dir = argv[1];
    double max_load_ms = atof(argv[2]);
    double max_op_us = atof(argv[3]);
    long max_rss_kb = atol(argv[4]);
    double simd_max_spec_ms = atof(argv[5]);
    int64_t simd_max_op_ns = atoll(argv[6]);

    struct report_state state;
    memset(&state, 0, sizeof(state));

    run_scalar_baseline();
    run_simd(&state, simd_max_spec_ms, simd_max_op_ns);
    run_cuda(&state, build_dir, max_load_ms, max_op_us);
    run_torch(&state, build_dir, max_load_ms, max_op_us);

    struct rusage usage;
    memset(&usage, 0, sizeof(usage));
    getrusage(RUSAGE_SELF, &usage);
    printf("accelerator_perf_max_rss_kb=%ld\n", usage.ru_maxrss);
    if (usage.ru_maxrss > max_rss_kb)
        add_failure(&state, "accelerator_perf_max_rss_kb>threshold");

    if (state.failures[0] != '\0') {
        printf("accelerator_perf_status=fail\n");
        printf("accelerator_perf_failures=%s\n", state.failures);
    } else {
        printf("accelerator_perf_status=pass\n");
    }
    return 0;
}
