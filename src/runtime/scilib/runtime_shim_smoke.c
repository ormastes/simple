/*
 * runtime_shim_smoke.c — runtime smoke for scilib mock/OpenBLAS shims.
 *
 * This replaces the Python ctypes smoke in check-scilib-runtime-shims.shs so
 * the check path stays within repo-native source plus the system C toolchain.
 */

#define _POSIX_C_SOURCE 200809L

#include <dlfcn.h>
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>

typedef int (*scilib_is_real_fn)(void);
typedef double (*blas_ddot_fn)(int64_t, const double *, int64_t, const double *, int64_t);
typedef void (*blas_dgemm_fn)(int, int, int64_t, int64_t, int64_t, double,
                              const double *, int64_t, const double *, int64_t,
                              double, double *, int64_t);
typedef void (*lapack_dgesv_fn)(int64_t, int64_t, double *, int64_t, int64_t *,
                                double *, int64_t, int64_t *);

struct scilib_api {
    void *handle;
    scilib_is_real_fn is_real;
    blas_ddot_fn ddot;
    blas_dgemm_fn dgemm;
    lapack_dgesv_fn dgesv;
};

struct compute_result {
    double ddot;
    double gemm[4];
    double gesv[3];
};

static double monotonic_ms(void)
{
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0)
        return 0.0;
    return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1000000.0;
}

static void fail_msg(const char *label)
{
    fprintf(stderr, "%s\n", label);
    exit(1);
}

static void require_close(const char *label, double got, double expected, double eps)
{
    if (fabs(got - expected) > eps) {
        fprintf(stderr, "%s: got %.17g, expected %.17g\n", label, got, expected);
        exit(1);
    }
}

static void require_array(const char *label, const double *got, const double *expected, size_t len, double eps)
{
    for (size_t i = 0; i < len; ++i) {
        if (fabs(got[i] - expected[i]) > eps) {
            fprintf(stderr, "%s[%zu]: got %.17g, expected %.17g\n", label, i, got[i], expected[i]);
            exit(1);
        }
    }
}

static void *required_symbol(void *handle, const char *name)
{
    dlerror();
    void *sym = dlsym(handle, name);
    const char *err = dlerror();
    if (err != NULL || sym == NULL) {
        fprintf(stderr, "missing symbol %s: %s\n", name, err == NULL ? "null" : err);
        exit(1);
    }
    return sym;
}

static struct scilib_api load_api(const char *path)
{
    struct scilib_api api;
    memset(&api, 0, sizeof(api));
    api.handle = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    if (api.handle == NULL) {
        fprintf(stderr, "dlopen %s failed: %s\n", path, dlerror());
        exit(1);
    }
    api.is_real = (scilib_is_real_fn)required_symbol(api.handle, "rt_scilib_is_real");
    api.ddot = (blas_ddot_fn)required_symbol(api.handle, "rt_blas_ddot");
    api.dgemm = (blas_dgemm_fn)required_symbol(api.handle, "rt_blas_dgemm");
    api.dgesv = (lapack_dgesv_fn)required_symbol(api.handle, "rt_lapack_dgesv");
    return api;
}

static struct compute_result compute_once(struct scilib_api *api)
{
    struct compute_result result;
    memset(&result, 0, sizeof(result));

    double x[3] = {1.0, 2.0, 3.0};
    double y[3] = {4.0, 5.0, 6.0};
    result.ddot = api->ddot(3, x, 1, y, 1);

    double a[6] = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
    double b[6] = {7.0, 8.0, 9.0, 10.0, 11.0, 12.0};
    api->dgemm(0, 0, 2, 2, 3, 1.0, a, 3, b, 2, 0.0, result.gemm, 2);

    double lu[9] = {
        2.0, 0.0, 0.0,
        1.0, 2.0, 0.0,
        1.0, 1.0, 3.0,
    };
    double rhs[3] = {2.0, 5.0, 14.0};
    int64_t piv[3] = {0, 0, 0};
    int64_t info = 0;
    api->dgesv(3, 1, lu, 3, piv, rhs, 1, &info);
    if (info != 0) {
        fprintf(stderr, "dgesv info=%lld\n", (long long)info);
        exit(1);
    }
    memcpy(result.gesv, rhs, sizeof(result.gesv));
    return result;
}

int main(int argc, char **argv)
{
    if (argc != 3)
        fail_msg("usage: runtime_shim_smoke MOCK_SO OPENBLAS_SO");

    double load_start = monotonic_ms();
    struct scilib_api mock = load_api(argv[1]);
    struct scilib_api lib = load_api(argv[2]);
    double load_ms = monotonic_ms() - load_start;

    struct compute_result mock_once = compute_once(&mock);
    struct compute_result lib_once = compute_once(&lib);
    require_close("parity_ddot", lib_once.ddot, mock_once.ddot, 1e-9);
    require_array("parity_dgemm", lib_once.gemm, mock_once.gemm, 4, 1e-9);
    require_array("parity_dgesv", lib_once.gesv, mock_once.gesv, 3, 1e-9);

    double x[3] = {1.0, 2.0, 3.0};
    double y[3] = {4.0, 5.0, 6.0};
    require_close("ddot", lib.ddot(3, x, 1, y, 1), 32.0, 1e-9);
    double ddot_start = monotonic_ms();
    double ddot_total = 0.0;
    for (int i = 0; i < 10000; ++i)
        ddot_total += lib.ddot(3, x, 1, y, 1);
    double ddot_us = (monotonic_ms() - ddot_start) * 1000.0 / 10000.0;
    require_close("ddot_total", ddot_total, 320000.0, 1e-4);

    double a[6] = {1.0, 2.0, 3.0, 4.0, 5.0, 6.0};
    double b[6] = {7.0, 8.0, 9.0, 10.0, 11.0, 12.0};
    double c[4] = {0.0, 0.0, 0.0, 0.0};
    const double expected_gemm[4] = {58.0, 64.0, 139.0, 154.0};
    lib.dgemm(0, 0, 2, 2, 3, 1.0, a, 3, b, 2, 0.0, c, 2);
    require_array("dgemm", c, expected_gemm, 4, 1e-9);
    double gemm_start = monotonic_ms();
    for (int i = 0; i < 5000; ++i) {
        double loop_c[4] = {0.0, 0.0, 0.0, 0.0};
        lib.dgemm(0, 0, 2, 2, 3, 1.0, a, 3, b, 2, 0.0, loop_c, 2);
    }
    double gemm_us = (monotonic_ms() - gemm_start) * 1000.0 / 5000.0;

    double lu[9] = {
        2.0, 0.0, 0.0,
        1.0, 2.0, 0.0,
        1.0, 1.0, 3.0,
    };
    double rhs[3] = {2.0, 5.0, 14.0};
    int64_t piv[3] = {0, 0, 0};
    int64_t info = 0;
    const double expected_gesv[3] = {1.0, 2.0, 11.0 / 3.0};
    lib.dgesv(3, 1, lu, 3, piv, rhs, 1, &info);
    if (info != 0) {
        fprintf(stderr, "dgesv info=%lld\n", (long long)info);
        return 1;
    }
    require_array("dgesv", rhs, expected_gesv, 3, 1e-9);
    double gesv_start = monotonic_ms();
    for (int i = 0; i < 1000; ++i) {
        double loop_lu[9] = {
            2.0, 0.0, 0.0,
            1.0, 2.0, 0.0,
            1.0, 1.0, 3.0,
        };
        double loop_rhs[3] = {2.0, 5.0, 14.0};
        int64_t loop_piv[3] = {0, 0, 0};
        int64_t loop_info = 0;
        lib.dgesv(3, 1, loop_lu, 3, loop_piv, loop_rhs, 1, &loop_info);
        if (loop_info != 0) {
            fprintf(stderr, "dgesv_loop info=%lld\n", (long long)loop_info);
            return 1;
        }
    }
    double gesv_us = (monotonic_ms() - gesv_start) * 1000.0 / 1000.0;

    struct rusage usage;
    memset(&usage, 0, sizeof(usage));
    getrusage(RUSAGE_SELF, &usage);

    printf("openblas_real=%s\n", lib.is_real() == 1 ? "true" : "false");
    printf("scilib_parity=mock_vs_openblas\n");
    printf("scilib_load_ms=%.3f\n", load_ms);
    printf("scilib_ddot_us=%.3f\n", ddot_us);
    printf("scilib_dgemm_us=%.3f\n", gemm_us);
    printf("scilib_dgesv_us=%.3f\n", gesv_us);
    printf("scilib_max_rss_kb=%ld\n", usage.ru_maxrss);

    dlclose(lib.handle);
    dlclose(mock.handle);
    return 0;
}
