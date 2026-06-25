typedef bool (*torch_available_fn)(void);
typedef int64_t (*torch_from_bits_1d_fn)(const int64_t *, int64_t);
typedef int64_t (*torch_from_bits_2d_fn)(const int64_t *, int64_t, int64_t);
typedef int64_t (*torch_copy_bits_fn)(int64_t, int64_t *, int64_t);
typedef int64_t (*torch_binary_tensor_fn)(int64_t, int64_t);
typedef int64_t (*torch_unary_tensor_fn)(int64_t);
typedef int64_t (*torch_sum_bits_fn)(int64_t);
typedef void (*torch_free_fn)(int64_t);

struct torch_api {
    void *handle;
    torch_available_fn available;
    torch_from_bits_1d_fn from_bits_1d;
    torch_from_bits_2d_fn from_bits_2d;
    torch_copy_bits_fn copy_bits;
    torch_binary_tensor_fn dot;
    torch_binary_tensor_fn matmul;
    torch_binary_tensor_fn solve;
    torch_unary_tensor_fn inverse;
    torch_sum_bits_fn sum_bits;
    torch_free_fn free_tensor;
};

static bool load_torch_api(const char *path, struct torch_api *api, double *load_ms)
{
    memset(api, 0, sizeof(*api));
    double start = monotonic_ms();
    api->handle = dlopen(path, RTLD_LAZY | RTLD_LOCAL);
    *load_ms = monotonic_ms() - start;
    if (api->handle == NULL)
        return false;
    api->available = (torch_available_fn)load_symbol(api->handle, "rt_torch_available");
    api->from_bits_1d = (torch_from_bits_1d_fn)load_symbol(api->handle, "rt_dyn_torch_tensor_from_bits_1d");
    api->from_bits_2d = (torch_from_bits_2d_fn)load_symbol(api->handle, "rt_dyn_torch_tensor_from_bits_2d");
    api->copy_bits = (torch_copy_bits_fn)load_symbol(api->handle, "rt_dyn_torch_tensor_copy_bits");
    api->dot = (torch_binary_tensor_fn)load_symbol(api->handle, "rt_torch_torchtensor_dot");
    api->matmul = (torch_binary_tensor_fn)load_symbol(api->handle, "rt_torch_torchtensor_matmul");
    api->solve = (torch_binary_tensor_fn)load_symbol(api->handle, "rt_torch_torchtensor_linalg_solve");
    api->inverse = (torch_unary_tensor_fn)load_symbol(api->handle, "rt_torch_torchtensor_inverse");
    api->sum_bits = (torch_sum_bits_fn)load_symbol(api->handle, "rt_torch_torchtensor_sum_bits");
    api->free_tensor = (torch_free_fn)load_symbol(api->handle, "rt_torch_torchtensor_free");
    return api->available && api->from_bits_1d && api->from_bits_2d && api->copy_bits &&
           api->dot && api->matmul && api->solve && api->inverse && api->sum_bits && api->free_tensor;
}

struct torch_from_bits_ctx {
    struct torch_api *api;
    int64_t *bits;
    int64_t n;
};

static void time_torch_from_bits(void *raw)
{
    struct torch_from_bits_ctx *ctx = (struct torch_from_bits_ctx *)raw;
    int64_t handle = ctx->api->from_bits_1d(ctx->bits, ctx->n);
    if (handle != 0)
        ctx->api->free_tensor(handle);
}

struct torch_copy_ctx {
    struct torch_api *api;
    int64_t handle;
    int64_t *out;
    int64_t n;
};

static void time_torch_copy(void *raw)
{
    struct torch_copy_ctx *ctx = (struct torch_copy_ctx *)raw;
    (void)ctx->api->copy_bits(ctx->handle, ctx->out, ctx->n);
}

struct torch_binary_ctx {
    struct torch_api *api;
    torch_binary_tensor_fn fn;
    int64_t left;
    int64_t right;
};

static void time_torch_binary(void *raw)
{
    struct torch_binary_ctx *ctx = (struct torch_binary_ctx *)raw;
    int64_t handle = ctx->fn(ctx->left, ctx->right);
    if (handle != 0)
        ctx->api->free_tensor(handle);
}

struct torch_unary_ctx {
    struct torch_api *api;
    torch_unary_tensor_fn fn;
    int64_t handle;
};

static void time_torch_unary(void *raw)
{
    struct torch_unary_ctx *ctx = (struct torch_unary_ctx *)raw;
    int64_t handle = ctx->fn(ctx->handle);
    if (handle != 0)
        ctx->api->free_tensor(handle);
}

static void run_torch(struct report_state *state, const char *build_dir, double max_load_ms, double max_op_us)
{
    char path[1024];
    snprintf(path, sizeof(path), "%s/libspl_torch.so", build_dir);
    if (access(path, R_OK) != 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_reason=libspl_torch.so not built\n");
        return;
    }

    struct torch_api api;
    double load_ms = 0.0;
    if (!load_torch_api(path, &api, &load_ms)) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=dlopen_or_symbol_failed\n");
        return;
    }
    if (!api.available()) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_reason=rt_torch_available returned false\n");
        dlclose(api.handle);
        return;
    }

    char error[256] = "";
    int64_t n = 4096;
    double *x = (double *)malloc((size_t)n * sizeof(double));
    double *y = (double *)malloc((size_t)n * sizeof(double));
    int64_t *x_bits = (int64_t *)malloc((size_t)n * sizeof(int64_t));
    int64_t *y_bits = (int64_t *)malloc((size_t)n * sizeof(int64_t));
    int64_t *copy_out = (int64_t *)calloc((size_t)n, sizeof(int64_t));
    if (x == NULL || y == NULL || x_bits == NULL || y_bits == NULL || copy_out == NULL) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=allocation_failed\n");
        goto cleanup;
    }
    fill_periodic(x, n, 17, 8, 0.25);
    fill_periodic(y, n, 13, 6, 0.5);
    for (int64_t i = 0; i < n; ++i) {
        x_bits[i] = f64_to_bits(x[i]);
        y_bits[i] = f64_to_bits(y[i]);
    }
    int64_t xh = api.from_bits_1d(x_bits, n);
    int64_t yh = api.from_bits_1d(y_bits, n);
    int64_t transfer = api.from_bits_1d(x_bits, n);
    if (xh == 0 || yh == 0 || transfer == 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=tensor_fixture_creation_failed\n");
        goto cleanup;
    }
    struct torch_from_bits_ctx from_ctx = {&api, x_bits, n};
    struct torch_copy_ctx copy_ctx = {&api, transfer, copy_out, n};
    double from_bits_us = time_loop(25, time_torch_from_bits, &from_ctx);
    double copy_bits_us = time_loop(25, time_torch_copy, &copy_ctx);
    api.free_tensor(transfer);

    int64_t dh = api.dot(xh, yh);
    if (dh == 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=pytorch_dot returned failure\n");
        goto cleanup;
    }
    double dot_got = bits_to_f64(api.sum_bits(dh));
    api.free_tensor(dh);
    if (!require_close(error, sizeof(error), "pytorch_dot", dot_got, scalar_dot(x, y, n), 1e-6)) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=%s\n", error);
        goto cleanup;
    }
    struct torch_binary_ctx dot_ctx = {&api, api.dot, xh, yh};
    double dot_us = time_loop(100, time_torch_binary, &dot_ctx);
    api.free_tensor(xh);
    api.free_tensor(yh);

    int64_t rows = 32;
    int64_t cols = 32;
    int64_t inner = 32;
    double a[32 * 32];
    double b[32 * 32];
    double expected[32 * 32];
    int64_t a_bits[32 * 32];
    int64_t b_bits[32 * 32];
    int64_t out_bits[32 * 32];
    fill_periodic(a, rows * inner, 11, 5, 0.125);
    fill_periodic(b, inner * cols, 7, 3, 0.25);
    scalar_gemm(a, b, expected, rows, cols, inner);
    for (int64_t i = 0; i < rows * inner; ++i)
        a_bits[i] = f64_to_bits(a[i]);
    for (int64_t i = 0; i < inner * cols; ++i)
        b_bits[i] = f64_to_bits(b[i]);
    int64_t ah = api.from_bits_2d(a_bits, rows, inner);
    int64_t bh = api.from_bits_2d(b_bits, inner, cols);
    int64_t mh = api.matmul(ah, bh);
    if (ah == 0 || bh == 0 || mh == 0 || api.copy_bits(mh, out_bits, rows * cols) == 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=pytorch_gemm failed\n");
        goto cleanup;
    }
    for (int64_t i = 0; i < rows * cols; ++i) {
        if (!require_close(error, sizeof(error), "pytorch_gemm", bits_to_f64(out_bits[i]), expected[i], 1e-6)) {
            printf("pytorch_perf_available=false\n");
            printf("pytorch_perf_error=%s\n", error);
            goto cleanup;
        }
    }
    api.free_tensor(mh);
    struct torch_binary_ctx gemm_ctx = {&api, api.matmul, ah, bh};
    double gemm_us = time_loop(50, time_torch_binary, &gemm_ctx);
    api.free_tensor(ah);
    api.free_tensor(bh);

    int64_t solve_n = 16;
    double solve_a[16 * 16];
    double solve_b[16];
    double solve_expected[16];
    int64_t solve_a_bits[16 * 16];
    int64_t solve_b_bits[16];
    int64_t solve_out_bits[16];
    for (int64_t row = 0; row < solve_n; ++row) {
        for (int64_t col = 0; col < solve_n; ++col)
            solve_a[row * solve_n + col] = row == col ? 2.0 * (double)solve_n : 0.1 * (double)((row + col) % 5 + 1);
        solve_b[row] = (double)(row + 1);
    }
    (void)scalar_solve(solve_a, solve_b, solve_expected, solve_n);
    for (int64_t i = 0; i < solve_n * solve_n; ++i)
        solve_a_bits[i] = f64_to_bits(solve_a[i]);
    for (int64_t i = 0; i < solve_n; ++i)
        solve_b_bits[i] = f64_to_bits(solve_b[i]);
    int64_t sah = api.from_bits_2d(solve_a_bits, solve_n, solve_n);
    int64_t sbh = api.from_bits_1d(solve_b_bits, solve_n);
    int64_t soh = api.solve(sah, sbh);
    if (sah == 0 || sbh == 0 || soh == 0 || api.copy_bits(soh, solve_out_bits, solve_n) == 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=pytorch_solve failed\n");
        goto cleanup;
    }
    for (int64_t i = 0; i < solve_n; ++i) {
        if (!require_close(error, sizeof(error), "pytorch_solve", bits_to_f64(solve_out_bits[i]), solve_expected[i], 1e-6)) {
            printf("pytorch_perf_available=false\n");
            printf("pytorch_perf_error=%s\n", error);
            goto cleanup;
        }
    }
    api.free_tensor(soh);
    struct torch_binary_ctx solve_ctx = {&api, api.solve, sah, sbh};
    double solve_us = time_loop(25, time_torch_binary, &solve_ctx);

    int64_t ih = api.inverse(sah);
    int64_t inv_out_bits[16 * 16];
    if (ih == 0 || api.copy_bits(ih, inv_out_bits, solve_n * solve_n) == 0) {
        printf("pytorch_perf_available=false\n");
        printf("pytorch_perf_error=pytorch_inverse failed\n");
        goto cleanup;
    }
    for (int64_t row = 0; row < solve_n; ++row) {
        for (int64_t col = 0; col < solve_n; ++col) {
            double total = 0.0;
            for (int64_t k = 0; k < solve_n; ++k)
                total += solve_a[row * solve_n + k] * bits_to_f64(inv_out_bits[k * solve_n + col]);
            if (!require_close(error, sizeof(error), "pytorch_inv_identity", total, row == col ? 1.0 : 0.0, 1e-5)) {
                printf("pytorch_perf_available=false\n");
                printf("pytorch_perf_error=%s\n", error);
                goto cleanup;
            }
        }
    }
    api.free_tensor(ih);
    struct torch_unary_ctx inv_ctx = {&api, api.inverse, sah};
    double inv_us = time_loop(25, time_torch_unary, &inv_ctx);
    api.free_tensor(sah);
    api.free_tensor(sbh);

    printf("pytorch_perf_available=true\n");
    printf("pytorch_load_ms=%.3f\n", load_ms);
    printf("pytorch_from_bits_4096_f64_us=%.3f\n", from_bits_us);
    printf("pytorch_copy_bits_4096_f64_us=%.3f\n", copy_bits_us);
    printf("pytorch_dot_4096_us=%.3f\n", dot_us);
    printf("pytorch_gemm_32x32_us=%.3f\n", gemm_us);
    printf("pytorch_solve_16_us=%.3f\n", solve_us);
    printf("pytorch_inv_16_us=%.3f\n", inv_us);
    if (load_ms > max_load_ms)
        add_failure(state, "pytorch_load_ms>threshold");
    if (from_bits_us > max_op_us)
        add_failure(state, "pytorch_from_bits_4096_f64_us>threshold");
    if (copy_bits_us > max_op_us)
        add_failure(state, "pytorch_copy_bits_4096_f64_us>threshold");
    if (dot_us > max_op_us)
        add_failure(state, "pytorch_dot_4096_us>threshold");
    if (gemm_us > max_op_us)
        add_failure(state, "pytorch_gemm_32x32_us>threshold");
    if (solve_us > max_op_us)
        add_failure(state, "pytorch_solve_16_us>threshold");
    if (inv_us > max_op_us)
        add_failure(state, "pytorch_inv_16_us>threshold");

cleanup:
    free(x);
    free(y);
    free(x_bits);
    free(y_bits);
    free(copy_out);
    if (api.handle != NULL)
        dlclose(api.handle);
}

