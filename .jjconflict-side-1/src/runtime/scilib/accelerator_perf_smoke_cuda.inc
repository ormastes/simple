static void *load_symbol(void *handle, const char *name)
{
    dlerror();
    void *sym = dlsym(handle, name);
    const char *err = dlerror();
    if (err != NULL || sym == NULL)
        return NULL;
    return sym;
}

typedef int64_t (*cuda_available_fn)(void);
typedef int64_t (*cuda_ddot_fn)(int64_t, int64_t, int64_t);
typedef int64_t (*cuda_dgemm_fn)(int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*cuda_dgemv_fn)(int64_t, int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*cuda_dgesv_fn)(int64_t, int64_t, int64_t, int64_t);
typedef int64_t (*cuda_malloc_fn)(int64_t);
typedef void (*cuda_free_fn)(int64_t);
typedef void (*cuda_htod_fn)(int64_t, const void *, int64_t);
typedef void (*cuda_dtoh_fn)(void *, int64_t, int64_t);

struct cuda_api {
    void *handle;
    cuda_available_fn available;
    cuda_ddot_fn ddot;
    cuda_dgemm_fn dgemm;
    cuda_dgemv_fn dgemv;
    cuda_dgesv_fn dgesv;
    cuda_malloc_fn malloc_device;
    cuda_free_fn free_device;
    cuda_htod_fn memcpy_htod;
    cuda_dtoh_fn memcpy_dtoh;
};

struct cuda_dot_ctx {
    struct cuda_api *api;
    int64_t *x;
    int64_t *y;
    int64_t n;
    int64_t sink;
};

static void time_cuda_dot(void *raw)
{
    struct cuda_dot_ctx *ctx = (struct cuda_dot_ctx *)raw;
    ctx->sink ^= ctx->api->ddot((int64_t)(uintptr_t)ctx->x, ctx->n, (int64_t)(uintptr_t)ctx->y);
}

struct cuda_memcpy_ctx {
    struct cuda_api *api;
    int64_t device;
    int64_t *host;
    int64_t bytes;
};

static void time_cuda_htod(void *raw)
{
    struct cuda_memcpy_ctx *ctx = (struct cuda_memcpy_ctx *)raw;
    ctx->api->memcpy_htod(ctx->device, ctx->host, ctx->bytes);
}

static void time_cuda_dtoh(void *raw)
{
    struct cuda_memcpy_ctx *ctx = (struct cuda_memcpy_ctx *)raw;
    ctx->api->memcpy_dtoh(ctx->host, ctx->device, ctx->bytes);
}

struct cuda_gemm_ctx {
    struct cuda_api *api;
    int64_t *params;
    int64_t *a;
    int64_t *b;
    int64_t *c;
    int64_t *out;
};

static void time_cuda_gemm(void *raw)
{
    struct cuda_gemm_ctx *ctx = (struct cuda_gemm_ctx *)raw;
    (void)ctx->api->dgemm((int64_t)(uintptr_t)ctx->params, (int64_t)(uintptr_t)ctx->a,
                          (int64_t)(uintptr_t)ctx->b, (int64_t)(uintptr_t)ctx->c,
                          (int64_t)(uintptr_t)ctx->out);
}

struct cuda_gemv_ctx {
    struct cuda_api *api;
    int64_t *params;
    int64_t *a;
    int64_t *x;
    int64_t *y;
    int64_t *out;
};

static void time_cuda_gemv(void *raw)
{
    struct cuda_gemv_ctx *ctx = (struct cuda_gemv_ctx *)raw;
    (void)ctx->api->dgemv((int64_t)(uintptr_t)ctx->params, (int64_t)(uintptr_t)ctx->a,
                          (int64_t)(uintptr_t)ctx->x, (int64_t)(uintptr_t)ctx->y,
                          (int64_t)(uintptr_t)ctx->out);
}

struct cuda_dgesv_ctx {
    struct cuda_api *api;
    int64_t *params;
    int64_t *a;
    int64_t *b;
    int64_t *out;
};

static void time_cuda_dgesv(void *raw)
{
    struct cuda_dgesv_ctx *ctx = (struct cuda_dgesv_ctx *)raw;
    (void)ctx->api->dgesv((int64_t)(uintptr_t)ctx->params, (int64_t)(uintptr_t)ctx->a,
                          (int64_t)(uintptr_t)ctx->b, (int64_t)(uintptr_t)ctx->out);
}

static bool load_cuda_api(const char *path, struct cuda_api *api, double *load_ms)
{
    memset(api, 0, sizeof(*api));
    double start = monotonic_ms();
    api->handle = dlopen(path, RTLD_LAZY | RTLD_LOCAL);
    *load_ms = monotonic_ms() - start;
    if (api->handle == NULL)
        return false;
    api->available = (cuda_available_fn)load_symbol(api->handle, "rt_scilib_cuda_available");
    api->ddot = (cuda_ddot_fn)load_symbol(api->handle, "rt_scilib_cuda_ddot_bits");
    api->dgemm = (cuda_dgemm_fn)load_symbol(api->handle, "rt_scilib_cuda_dgemm_bits");
    api->dgemv = (cuda_dgemv_fn)load_symbol(api->handle, "rt_scilib_cuda_dgemv_bits");
    api->dgesv = (cuda_dgesv_fn)load_symbol(api->handle, "rt_scilib_cuda_dgesv_bits");
    api->malloc_device = (cuda_malloc_fn)load_symbol(api->handle, "rt_cuda_malloc");
    api->free_device = (cuda_free_fn)load_symbol(api->handle, "rt_cuda_free");
    api->memcpy_htod = (cuda_htod_fn)load_symbol(api->handle, "rt_cuda_memcpy_htod");
    api->memcpy_dtoh = (cuda_dtoh_fn)load_symbol(api->handle, "rt_cuda_memcpy_dtoh");
    return api->available && api->ddot && api->dgemm && api->dgemv && api->dgesv &&
           api->malloc_device && api->free_device && api->memcpy_htod && api->memcpy_dtoh;
}

static void run_cuda(struct report_state *state, const char *build_dir, double max_load_ms, double max_op_us)
{
    char path[1024];
    snprintf(path, sizeof(path), "%s/libspl_scilib.so", build_dir);
    if (access(path, R_OK) != 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_reason=libspl_scilib.so not built\n");
        return;
    }

    struct cuda_api api;
    double load_ms = 0.0;
    if (!load_cuda_api(path, &api, &load_ms)) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=dlopen_or_symbol_failed\n");
        return;
    }
    if (api.available() == 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_reason=rt_scilib_cuda_available returned false\n");
        dlclose(api.handle);
        return;
    }

    char error[256] = "";
    int64_t n = 4096;
    double *x = (double *)malloc((size_t)n * sizeof(double));
    double *y = (double *)malloc((size_t)n * sizeof(double));
    int64_t *x_bits = (int64_t *)malloc((size_t)n * sizeof(int64_t));
    int64_t *y_bits = (int64_t *)malloc((size_t)n * sizeof(int64_t));
    int64_t *transfer_out = (int64_t *)calloc((size_t)n, sizeof(int64_t));
    if (x == NULL || y == NULL || x_bits == NULL || y_bits == NULL || transfer_out == NULL) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=allocation_failed\n");
        goto cleanup;
    }
    fill_periodic(x, n, 17, 8, 0.25);
    fill_periodic(y, n, 13, 6, 0.5);
    for (int64_t i = 0; i < n; ++i) {
        x_bits[i] = f64_to_bits(x[i]);
        y_bits[i] = f64_to_bits(y[i]);
    }

    int64_t transfer_bytes = n * (int64_t)sizeof(int64_t);
    int64_t transfer_device = api.malloc_device(transfer_bytes);
    if (transfer_device == 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=transfer_fixture_allocation_failed\n");
        goto cleanup;
    }
    struct cuda_memcpy_ctx memcpy_ctx = {&api, transfer_device, x_bits, transfer_bytes};
    double htod_us = time_loop(25, time_cuda_htod, &memcpy_ctx);
    memcpy_ctx.host = transfer_out;
    double dtoh_us = time_loop(25, time_cuda_dtoh, &memcpy_ctx);
    api.free_device(transfer_device);

    double dot_got = bits_to_f64(api.ddot((int64_t)(uintptr_t)x_bits, n, (int64_t)(uintptr_t)y_bits));
    if (!require_close(error, sizeof(error), "cuda_dot", dot_got, scalar_dot(x, y, n), 1e-6)) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=%s\n", error);
        goto cleanup;
    }
    struct cuda_dot_ctx dot_ctx = {&api, x_bits, y_bits, n, 0};
    double dot_us = time_loop(25, time_cuda_dot, &dot_ctx);

    int64_t rows = 32;
    int64_t cols = 32;
    int64_t inner = 32;
    double a[32 * 32];
    double b[32 * 32];
    double c[32 * 32];
    double expected[32 * 32];
    int64_t a_bits[32 * 32];
    int64_t b_bits[32 * 32];
    int64_t c_bits[32 * 32];
    int64_t out_bits[32 * 32];
    int64_t params[5] = {rows, cols, inner, f64_to_bits(1.0), f64_to_bits(0.0)};
    fill_periodic(a, rows * inner, 11, 5, 0.125);
    fill_periodic(b, inner * cols, 7, 3, 0.25);
    memset(c, 0, sizeof(c));
    scalar_gemm(a, b, expected, rows, cols, inner);
    for (int64_t i = 0; i < rows * inner; ++i)
        a_bits[i] = f64_to_bits(a[i]);
    for (int64_t i = 0; i < inner * cols; ++i)
        b_bits[i] = f64_to_bits(b[i]);
    for (int64_t i = 0; i < rows * cols; ++i)
        c_bits[i] = f64_to_bits(c[i]);
    if (api.dgemm((int64_t)(uintptr_t)params, (int64_t)(uintptr_t)a_bits, (int64_t)(uintptr_t)b_bits,
                  (int64_t)(uintptr_t)c_bits, (int64_t)(uintptr_t)out_bits) == 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=cuda_gemm returned failure\n");
        goto cleanup;
    }
    for (int64_t i = 0; i < rows * cols; ++i) {
        if (!require_close(error, sizeof(error), "cuda_gemm", bits_to_f64(out_bits[i]), expected[i], 1e-6)) {
            printf("cuda_perf_available=false\n");
            printf("cuda_perf_error=%s\n", error);
            goto cleanup;
        }
    }
    struct cuda_gemm_ctx gemm_ctx = {&api, params, a_bits, b_bits, c_bits, out_bits};
    double gemm_us = time_loop(10, time_cuda_gemm, &gemm_ctx);

    int64_t gemv_rows = 64;
    int64_t gemv_cols = 32;
    double gemv_a[64 * 32];
    double gemv_x[32];
    double gemv_y[64];
    double gemv_expected[64];
    int64_t gemv_a_bits[64 * 32];
    int64_t gemv_x_bits[32];
    int64_t gemv_y_bits[64];
    int64_t gemv_out_bits[64];
    int64_t gemv_params[4] = {gemv_rows, gemv_cols, f64_to_bits(2.0), f64_to_bits(3.0)};
    fill_periodic(gemv_a, gemv_rows * gemv_cols, 19, 9, 0.0625);
    fill_periodic(gemv_x, gemv_cols, 17, 8, 0.125);
    fill_periodic(gemv_y, gemv_rows, 5, 2, 0.25);
    scalar_gemv(gemv_a, gemv_x, gemv_y, gemv_expected, gemv_rows, gemv_cols, 2.0, 3.0);
    for (int64_t i = 0; i < gemv_rows * gemv_cols; ++i)
        gemv_a_bits[i] = f64_to_bits(gemv_a[i]);
    for (int64_t i = 0; i < gemv_cols; ++i)
        gemv_x_bits[i] = f64_to_bits(gemv_x[i]);
    for (int64_t i = 0; i < gemv_rows; ++i)
        gemv_y_bits[i] = f64_to_bits(gemv_y[i]);
    if (api.dgemv((int64_t)(uintptr_t)gemv_params, (int64_t)(uintptr_t)gemv_a_bits,
                  (int64_t)(uintptr_t)gemv_x_bits, (int64_t)(uintptr_t)gemv_y_bits,
                  (int64_t)(uintptr_t)gemv_out_bits) == 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=cuda_gemv returned failure\n");
        goto cleanup;
    }
    for (int64_t i = 0; i < gemv_rows; ++i) {
        if (!require_close(error, sizeof(error), "cuda_gemv", bits_to_f64(gemv_out_bits[i]), gemv_expected[i], 1e-6)) {
            printf("cuda_perf_available=false\n");
            printf("cuda_perf_error=%s\n", error);
            goto cleanup;
        }
    }
    struct cuda_gemv_ctx gemv_ctx = {&api, gemv_params, gemv_a_bits, gemv_x_bits, gemv_y_bits, gemv_out_bits};
    double gemv_us = time_loop(10, time_cuda_gemv, &gemv_ctx);

    int64_t solve_n = 16;
    double solve_a[16 * 16];
    double solve_b[16];
    double solve_expected[16];
    int64_t solve_a_bits[16 * 16];
    int64_t solve_b_bits[16];
    int64_t solve_out_bits[16];
    int64_t solve_params[2] = {solve_n, 1};
    fill_solve_fixture(solve_a, solve_n);
    fill_periodic(solve_b, solve_n, 9, 4, 0.5);
    (void)scalar_solve(solve_a, solve_b, solve_expected, solve_n);
    for (int64_t i = 0; i < solve_n * solve_n; ++i)
        solve_a_bits[i] = f64_to_bits(solve_a[i]);
    for (int64_t i = 0; i < solve_n; ++i)
        solve_b_bits[i] = f64_to_bits(solve_b[i]);
    int64_t info = api.dgesv((int64_t)(uintptr_t)solve_params, (int64_t)(uintptr_t)solve_a_bits,
                             (int64_t)(uintptr_t)solve_b_bits, (int64_t)(uintptr_t)solve_out_bits);
    if (info != 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=cuda_solve info=%lld\n", (long long)info);
        goto cleanup;
    }
    for (int64_t i = 0; i < solve_n; ++i) {
        if (!require_close(error, sizeof(error), "cuda_solve", bits_to_f64(solve_out_bits[i]), solve_expected[i], 1e-6)) {
            printf("cuda_perf_available=false\n");
            printf("cuda_perf_error=%s\n", error);
            goto cleanup;
        }
    }
    struct cuda_dgesv_ctx solve_ctx = {&api, solve_params, solve_a_bits, solve_b_bits, solve_out_bits};
    double solve_us = time_loop(10, time_cuda_dgesv, &solve_ctx);

    double inv_rhs[16 * 16];
    int64_t inv_rhs_bits[16 * 16];
    int64_t inv_out_bits[16 * 16];
    int64_t inv_params[2] = {solve_n, solve_n};
    memset(inv_rhs, 0, sizeof(inv_rhs));
    for (int64_t row = 0; row < solve_n; ++row)
        inv_rhs[row * solve_n + row] = 1.0;
    for (int64_t i = 0; i < solve_n * solve_n; ++i) {
        solve_a_bits[i] = f64_to_bits(solve_a[i]);
        inv_rhs_bits[i] = f64_to_bits(inv_rhs[i]);
    }
    info = api.dgesv((int64_t)(uintptr_t)inv_params, (int64_t)(uintptr_t)solve_a_bits,
                     (int64_t)(uintptr_t)inv_rhs_bits, (int64_t)(uintptr_t)inv_out_bits);
    if (info != 0) {
        printf("cuda_perf_available=false\n");
        printf("cuda_perf_error=cuda_inv info=%lld\n", (long long)info);
        goto cleanup;
    }
    for (int64_t row = 0; row < solve_n; ++row) {
        for (int64_t col = 0; col < solve_n; ++col) {
            double total = 0.0;
            for (int64_t k = 0; k < solve_n; ++k)
                total += solve_a[row * solve_n + k] * bits_to_f64(inv_out_bits[k * solve_n + col]);
            if (!require_close(error, sizeof(error), "cuda_inv_identity", total, row == col ? 1.0 : 0.0, 1e-5)) {
                printf("cuda_perf_available=false\n");
                printf("cuda_perf_error=%s\n", error);
                goto cleanup;
            }
        }
    }
    struct cuda_dgesv_ctx inv_ctx = {&api, inv_params, solve_a_bits, inv_rhs_bits, inv_out_bits};
    double inv_us = time_loop(10, time_cuda_dgesv, &inv_ctx);

    printf("cuda_perf_available=true\n");
    printf("cuda_load_ms=%.3f\n", load_ms);
    printf("cuda_htod_4096_f64_us=%.3f\n", htod_us);
    printf("cuda_dtoh_4096_f64_us=%.3f\n", dtoh_us);
    printf("cuda_dot_4096_us=%.3f\n", dot_us);
    printf("cuda_gemv_64x32_us=%.3f\n", gemv_us);
    printf("cuda_gemm_32x32_us=%.3f\n", gemm_us);
    printf("cuda_solve_16_us=%.3f\n", solve_us);
    printf("cuda_inv_16_us=%.3f\n", inv_us);
    if (load_ms > max_load_ms)
        add_failure(state, "cuda_load_ms>threshold");
    if (dot_us > max_op_us)
        add_failure(state, "cuda_dot_4096_us>threshold");
    if (htod_us > max_op_us)
        add_failure(state, "cuda_htod_4096_f64_us>threshold");
    if (dtoh_us > max_op_us)
        add_failure(state, "cuda_dtoh_4096_f64_us>threshold");
    if (gemv_us > max_op_us)
        add_failure(state, "cuda_gemv_64x32_us>threshold");
    if (gemm_us > max_op_us)
        add_failure(state, "cuda_gemm_32x32_us>threshold");
    if (solve_us > max_op_us)
        add_failure(state, "cuda_solve_16_us>threshold");
    if (inv_us > max_op_us)
        add_failure(state, "cuda_inv_16_us>threshold");

cleanup:
    free(x);
    free(y);
    free(x_bits);
    free(y_bits);
    free(transfer_out);
    if (api.handle != NULL)
        dlclose(api.handle);
}

