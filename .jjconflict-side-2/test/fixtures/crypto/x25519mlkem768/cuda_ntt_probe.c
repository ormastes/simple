#define _POSIX_C_SOURCE 200809L

/* Physical CUDA evidence probe for the pure-Simple ML-KEM GPU candidate.
 * This is an independent test harness, not production implementation code.
 */
#include <cuda.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "ntt_fixture.h"

#define N 256
#define BATCH 3
#define Q 3329
#define CANONICAL_MIN_SPEEDUP_MILLI 1250

static const int32_t zetas[128] = {
       1,1729,2580,3289,2642,630,1897,848,1062,1919,193,797,2786,3260,569,1746,
     296,2447,1339,1476,3046,56,2240,1333,1426,2094,535,2882,2393,2879,1974,821,
     289,331,3253,1756,1197,2304,2277,2055,650,1977,2513,632,2865,33,1320,1915,
    2319,1435,807,452,1438,2868,1534,2402,2647,2617,1481,648,2474,3110,1227,910,
      17,2761,583,2649,1637,723,2288,1100,1409,2662,3281,233,756,2156,3015,3050,
    1703,1651,2789,1789,1847,952,1461,2687,939,2308,2437,2388,733,2337,268,641,
    1584,2298,2037,3220,375,2549,2090,1645,1063,319,2773,757,2099,561,2466,2594,
    2804,1092,403,1026,1143,2150,2775,886,1722,1212,1874,1029,2110,2935,885,2154
};

static int32_t modq(int64_t x) {
    int32_t r = (int32_t)(x % Q);
    return r < 0 ? r + Q : r;
}

static void scalar_ntt(int32_t *f) {
    int k = 1;
    for (int len = 128; len >= 2; len >>= 1) {
        for (int start = 0; start < N; start += 2 * len) {
            int32_t zeta = zetas[k++];
            for (int j = start; j < start + len; ++j) {
                int32_t t = modq((int64_t)zeta * f[j + len]);
                int32_t lower = f[j];
                f[j] = modq((int64_t)lower + t);
                f[j + len] = modq((int64_t)lower - t);
            }
        }
    }
}

static void scalar_intt(int32_t *f) {
    int k = 127;
    for (int len = 2; len <= 128; len <<= 1) {
        for (int start = 0; start < N; start += 2 * len) {
            int32_t zeta = zetas[k--];
            for (int j = start; j < start + len; ++j) {
                int32_t lower = f[j], upper = f[j + len];
                f[j] = modq((int64_t)lower + upper);
                f[j + len] = modq((int64_t)zeta * modq((int64_t)upper - lower));
            }
        }
    }
    for (int i = 0; i < N; ++i) f[i] = modq((int64_t)f[i] * 3303);
}

static int cuda_ok(CUresult rc, const char *step) {
    if (rc == CUDA_SUCCESS) return 1;
    const char *name = "unknown";
    const char *message = "unknown";
    cuGetErrorName(rc, &name);
    cuGetErrorString(rc, &message);
    fprintf(stderr, "%s: %s: %s\n", step, name, message);
    return 0;
}

static int monotonic_ns(uint64_t *result, const char *step) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) {
        fprintf(stderr, "monotonic clock read failed step=%s\n", step);
        return 0;
    }
    *result = (uint64_t)value.tv_sec * UINT64_C(1000000000) +
        (uint64_t)value.tv_nsec;
    return 1;
}

static int monotonic_elapsed(uint64_t start, uint64_t *elapsed,
                             uint64_t *stop_out, const char *step) {
    uint64_t stop = 0;
    if (!monotonic_ns(&stop, step)) return 0;
    if (stop < start) {
        fprintf(stderr, "monotonic clock moved backward step=%s start=%llu stop=%llu\n",
                step, (unsigned long long)start, (unsigned long long)stop);
        return 0;
    }
    *elapsed = stop - start;
    if (stop_out) *stop_out = stop;
    return 1;
}

static int compare_u64(const void *left, const void *right) {
    const uint64_t a = *(const uint64_t *)left;
    const uint64_t b = *(const uint64_t *)right;
    return (a > b) - (a < b);
}

static uint64_t percentile(uint64_t *values, int count, int percentile_value) {
    qsort(values, (size_t)count, sizeof(*values), compare_u64);
    int rank = (percentile_value * count + 99) / 100;
    if (rank < 1) rank = 1;
    if (rank > count) rank = count;
    return values[rank - 1];
}

static int run_performance(CUfunction kernel, int ordinal, const char *name,
                           int major, int minor, int samples,
                           int minimum_speedup_milli) {
    static const unsigned batches[] = {1, 3, 8, 16, 32, 64, 128, 256, 512, 1024};
    enum { BATCH_COUNT = sizeof(batches) / sizeof(batches[0]) };
    const int warmups = 5;
    int speedups_milli[BATCH_COUNT];
    unsigned first_gpu_win_batch = 0;
    unsigned promotion_batch = 0;
    int best_speedup_milli = 0;

    for (size_t batch_index = 0; batch_index < BATCH_COUNT; ++batch_index) {
        unsigned batch = batches[batch_index];
        const size_t coefficient_count = (size_t)batch * N;
        const size_t byte_count = coefficient_count * sizeof(int32_t);
        int32_t *input = calloc(coefficient_count, sizeof(*input));
        int32_t *expected = calloc(coefficient_count, sizeof(*expected));
        int32_t *actual = calloc(coefficient_count, sizeof(*actual));
        int32_t *scalar_work = calloc(coefficient_count, sizeof(*scalar_work));
        uint64_t *h2d = calloc((size_t)samples, sizeof(*h2d));
        uint64_t *launch = calloc((size_t)samples, sizeof(*launch));
        uint64_t *sync = calloc((size_t)samples, sizeof(*sync));
        uint64_t *d2h = calloc((size_t)samples, sizeof(*d2h));
        uint64_t *end_to_end = calloc((size_t)samples, sizeof(*end_to_end));
        uint64_t *scalar = calloc((size_t)samples, sizeof(*scalar));
        CUdeviceptr input_device = 0;
        CUdeviceptr output_device = 0;
        int batch_ok = input && expected && actual && scalar_work && h2d &&
            launch && sync && d2h && end_to_end && scalar;

        if (!batch_ok) {
            fprintf(stderr, "CUDA performance allocation failed batch=%u\n", batch);
        }
        for (unsigned p = 0; batch_ok && p < batch; ++p) {
            for (int i = 0; i < N; ++i) {
                input[(size_t)p * N + (size_t)i] =
                    x25519mlkem768_ntt_fixture_coefficient((int)p, i);
                expected[(size_t)p * N + (size_t)i] =
                    input[(size_t)p * N + (size_t)i];
            }
            scalar_ntt(&expected[(size_t)p * N]);
        }
        if (batch_ok && !cuda_ok(cuMemAlloc(&input_device, byte_count),
                                 "perf cuMemAlloc(input)")) batch_ok = 0;
        if (batch_ok && !cuda_ok(cuMemAlloc(&output_device, byte_count),
                                 "perf cuMemAlloc(output)")) batch_ok = 0;
        void *args[] = {&input_device, &output_device, &batch};
        for (int warmup = 0; batch_ok && warmup < warmups; ++warmup) {
            if (!cuda_ok(cuMemcpyHtoD(input_device, input, byte_count),
                         "perf warm H2D") ||
                    !cuda_ok(cuLaunchKernel(kernel, batch, 1, 1, N, 1, 1,
                                  0, NULL, args, NULL), "perf warm launch") ||
                    !cuda_ok(cuCtxSynchronize(), "perf warm sync") ||
                    !cuda_ok(cuMemcpyDtoH(actual, output_device, byte_count),
                             "perf warm D2H")) batch_ok = 0;
        }
        for (int sample = 0; batch_ok && sample < samples; ++sample) {
            memcpy(scalar_work, input, byte_count);
            uint64_t start = 0;
            uint64_t stop = 0;
            if (!monotonic_ns(&start, "scalar-start")) {
                batch_ok = 0;
                break;
            }
            for (unsigned p = 0; p < batch; ++p)
                scalar_ntt(&scalar_work[(size_t)p * N]);
            if (!monotonic_elapsed(start, &scalar[sample], &stop,
                                   "scalar-stop")) {
                batch_ok = 0;
                break;
            }
            if (memcmp(scalar_work, expected, byte_count) != 0) {
                fprintf(stderr,
                        "CUDA scalar performance oracle mismatch device=%d batch=%u sample=%d\n",
                        ordinal, batch, sample);
                batch_ok = 0;
                break;
            }

            uint64_t end_to_end_start = 0;
            if (!monotonic_ns(&end_to_end_start, "e2e-start") ||
                    !monotonic_ns(&start, "h2d-start")) {
                batch_ok = 0;
                break;
            }
            if (!cuda_ok(cuMemcpyHtoD(input_device, input, byte_count),
                         "perf H2D")) {
                batch_ok = 0;
                break;
            }
            if (!monotonic_elapsed(start, &h2d[sample], &stop,
                                   "h2d-stop") ||
                    !monotonic_ns(&start, "launch-start")) {
                batch_ok = 0;
                break;
            }
            if (!cuda_ok(cuLaunchKernel(kernel, batch, 1, 1, N, 1, 1,
                              0, NULL, args, NULL), "perf launch")) {
                batch_ok = 0;
                break;
            }
            if (!monotonic_elapsed(start, &launch[sample], &stop,
                                   "launch-stop") ||
                    !monotonic_ns(&start, "sync-start")) {
                batch_ok = 0;
                break;
            }
            if (!cuda_ok(cuCtxSynchronize(), "perf sync")) {
                batch_ok = 0;
                break;
            }
            if (!monotonic_elapsed(start, &sync[sample], &stop,
                                   "sync-stop") ||
                    !monotonic_ns(&start, "d2h-start")) {
                batch_ok = 0;
                break;
            }
            if (!cuda_ok(cuMemcpyDtoH(actual, output_device, byte_count),
                         "perf D2H")) {
                batch_ok = 0;
                break;
            }
            if (!monotonic_elapsed(start, &d2h[sample], &stop,
                                   "d2h-stop")) {
                batch_ok = 0;
                break;
            }
            if (stop < end_to_end_start) {
                fprintf(stderr,
                        "monotonic clock moved backward step=e2e-stop start=%llu stop=%llu\n",
                        (unsigned long long)end_to_end_start,
                        (unsigned long long)stop);
                batch_ok = 0;
                break;
            }
            end_to_end[sample] = stop - end_to_end_start;
        }
        if (batch_ok && memcmp(actual, expected, byte_count) != 0) {
            fprintf(stderr, "CUDA performance oracle mismatch device=%d batch=%u\n",
                    ordinal, batch);
            batch_ok = 0;
        }
        if (batch_ok) {
            const uint64_t h2d_p50 = percentile(h2d, samples, 50);
            const uint64_t h2d_p95 = percentile(h2d, samples, 95);
            const uint64_t h2d_p99 = percentile(h2d, samples, 99);
            const uint64_t launch_p50 = percentile(launch, samples, 50);
            const uint64_t launch_p95 = percentile(launch, samples, 95);
            const uint64_t launch_p99 = percentile(launch, samples, 99);
            const uint64_t sync_p50 = percentile(sync, samples, 50);
            const uint64_t sync_p95 = percentile(sync, samples, 95);
            const uint64_t sync_p99 = percentile(sync, samples, 99);
            const uint64_t d2h_p50 = percentile(d2h, samples, 50);
            const uint64_t d2h_p95 = percentile(d2h, samples, 95);
            const uint64_t d2h_p99 = percentile(d2h, samples, 99);
            const uint64_t e2e_p50 = percentile(end_to_end, samples, 50);
            const uint64_t e2e_p95 = percentile(end_to_end, samples, 95);
            const uint64_t e2e_p99 = percentile(end_to_end, samples, 99);
            const uint64_t scalar_p50 = percentile(scalar, samples, 50);
            const uint64_t scalar_p95 = percentile(scalar, samples, 95);
            const uint64_t scalar_p99 = percentile(scalar, samples, 99);
            const int speedup_milli = e2e_p95 == 0 ? 0 :
                (int)((scalar_p95 * UINT64_C(1000)) / e2e_p95);
            speedups_milli[batch_index] = speedup_milli;
            if (speedup_milli > best_speedup_milli)
                best_speedup_milli = speedup_milli;
            if (first_gpu_win_batch == 0 && speedup_milli >= 1000)
                first_gpu_win_batch = batch;
            printf("CUDA_NTT_PERF backend=cuda device=%d name=%s capability=%d.%d "
                   "batch=%u samples=%d warmups=%d device_bytes=%zu host_bytes=%zu "
                   "h2d_p50_ns=%llu h2d_p95_ns=%llu h2d_p99_ns=%llu "
                   "launch_p50_ns=%llu launch_p95_ns=%llu launch_p99_ns=%llu "
                   "sync_p50_ns=%llu sync_p95_ns=%llu sync_p99_ns=%llu "
                   "d2h_p50_ns=%llu d2h_p95_ns=%llu d2h_p99_ns=%llu "
                   "e2e_p50_ns=%llu e2e_p95_ns=%llu e2e_p99_ns=%llu "
                   "scalar_p50_ns=%llu scalar_p95_ns=%llu scalar_p99_ns=%llu "
                   "speedup_milli=%d fixture_id=%s\n",
                   ordinal, name, major, minor, batch, samples, warmups,
                   byte_count * 2, byte_count * 4,
                   (unsigned long long)h2d_p50,
                   (unsigned long long)h2d_p95,
                   (unsigned long long)h2d_p99,
                   (unsigned long long)launch_p50,
                   (unsigned long long)launch_p95,
                   (unsigned long long)launch_p99,
                   (unsigned long long)sync_p50,
                   (unsigned long long)sync_p95,
                   (unsigned long long)sync_p99,
                   (unsigned long long)d2h_p50,
                   (unsigned long long)d2h_p95,
                   (unsigned long long)d2h_p99,
                   (unsigned long long)e2e_p50,
                   (unsigned long long)e2e_p95,
                   (unsigned long long)e2e_p99,
                   (unsigned long long)scalar_p50,
                   (unsigned long long)scalar_p95,
                   (unsigned long long)scalar_p99,
                   speedup_milli, X25519MLKEM768_NTT_FIXTURE_ID);
        }
        if (output_device) cuMemFree(output_device);
        if (input_device) cuMemFree(input_device);
        free(scalar);
        free(end_to_end);
        free(d2h);
        free(sync);
        free(launch);
        free(h2d);
        free(scalar_work);
        free(actual);
        free(expected);
        free(input);
        if (!batch_ok) return 0;
    }
    for (size_t candidate = 0; candidate < BATCH_COUNT; ++candidate) {
        int sustained = 1;
        for (size_t later = candidate; later < BATCH_COUNT; ++later) {
            if (speedups_milli[later] < minimum_speedup_milli) {
                sustained = 0;
                break;
            }
        }
        if (sustained) {
            promotion_batch = batches[candidate];
            break;
        }
    }
    printf("CUDA_NTT_PERF_GATE backend=cuda device=%d capability=%d.%d "
           "samples=%d canonical_minimum_speedup_milli=%d "
           "minimum_speedup_milli=%d first_gpu_win_batch=%u "
           "promotion_batch=%u promotion_supported_max_batch=1024 "
           "sustained_promotion=%s best_speedup_milli=%d result=%s\n",
           ordinal, major, minor, samples, CANONICAL_MIN_SPEEDUP_MILLI,
           minimum_speedup_milli, first_gpu_win_batch,
           promotion_batch, promotion_batch == 0 ? "false" : "true",
           best_speedup_milli, promotion_batch == 0 ? "fail" : "pass");
    return promotion_batch != 0;
}

static int run_device(int ordinal, const char *module_directory,
                      int perf_samples, int minimum_speedup_milli) {
    CUdevice device;
    CUcontext context = NULL;
    CUmodule module = NULL;
    CUfunction forward_kernel, inverse_kernel;
    CUdeviceptr input_device = 0;
    CUdeviceptr output_device = 0;
    int32_t input[BATCH * N];
    int32_t expected[BATCH * N];
    int32_t actual[BATCH * N];
    int32_t inverse_expected[BATCH * N];
    int32_t inverse_actual[BATCH * N];
    char name[256] = {0};
    char module_path[1024] = {0};
    int major = 0, minor = 0;
    CUctxCreateParams context_params = {0};
    const size_t byte_count = sizeof(input);
    int ok = 0;
    uint64_t start = 0;
    uint64_t context_create_ns = 0;
    uint64_t module_load_resolve_ns = 0;

    if (!cuda_ok(cuDeviceGet(&device, ordinal), "cuDeviceGet")) goto cleanup;
    if (!cuda_ok(cuDeviceGetName(name, sizeof(name), device), "cuDeviceGetName")) goto cleanup;
    if (!cuda_ok(cuDeviceGetAttribute(&major,
                    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MAJOR, device),
                 "cuDeviceGetAttribute(major)")) goto cleanup;
    if (!cuda_ok(cuDeviceGetAttribute(&minor,
                    CU_DEVICE_ATTRIBUTE_COMPUTE_CAPABILITY_MINOR, device),
                 "cuDeviceGetAttribute(minor)")) goto cleanup;
    int module_path_len = snprintf(module_path, sizeof(module_path),
        "%s/sm_%d%d.cubin", module_directory, major, minor);
    if (module_path_len < 0 ||
            (size_t)module_path_len >= sizeof(module_path)) goto cleanup;
    if (!monotonic_ns(&start, "context-create-start")) goto cleanup;
    if (!cuda_ok(cuCtxCreate(&context, &context_params, 0, device),
                 "cuCtxCreate")) goto cleanup;
    if (!monotonic_elapsed(start, &context_create_ns, NULL,
                           "context-create-stop") ||
            !monotonic_ns(&start, "module-load-start")) goto cleanup;
    if (!cuda_ok(cuModuleLoad(&module, module_path), "cuModuleLoad")) goto cleanup;
    if (!cuda_ok(cuModuleGetFunction(&forward_kernel, module,
                    "x25519_mlkem768_ntt_forward"), "cuModuleGetFunction")) goto cleanup;
    if (!cuda_ok(cuModuleGetFunction(&inverse_kernel, module,
                    "x25519_mlkem768_ntt_inverse"), "cuModuleGetFunction(inverse)")) goto cleanup;
    if (!monotonic_elapsed(start, &module_load_resolve_ns, NULL,
                           "module-load-stop")) goto cleanup;
    if (perf_samples > 0) {
        printf("CUDA_NTT_PERF_COLD backend=cuda device=%d name=%s capability=%d.%d "
               "context_create_ns=%llu module_load_resolve_ns=%llu\n",
               ordinal, name, major, minor,
               (unsigned long long)context_create_ns,
               (unsigned long long)module_load_resolve_ns);
    }

    for (int p = 0; p < BATCH; ++p) {
        for (int i = 0; i < N; ++i) {
            input[p * N + i] =
                x25519mlkem768_ntt_fixture_coefficient(p, i);
            expected[p * N + i] = input[p * N + i];
        }
        scalar_ntt(&expected[p * N]);
        memcpy(&inverse_expected[p * N], &expected[p * N], N * sizeof(int32_t));
        scalar_intt(&inverse_expected[p * N]);
    }

    if (!cuda_ok(cuMemAlloc(&input_device, byte_count), "cuMemAlloc(input)")) goto cleanup;
    if (!cuda_ok(cuMemAlloc(&output_device, byte_count), "cuMemAlloc(output)")) goto cleanup;
    if (!cuda_ok(cuMemcpyHtoD(input_device, input, byte_count), "cuMemcpyHtoD")) goto cleanup;
    unsigned polynomial_count = BATCH;
    void *args[] = {&input_device, &output_device, &polynomial_count};
    if (!cuda_ok(cuLaunchKernel(forward_kernel, BATCH, 1, 1, N, 1, 1,
                    0, NULL, args, NULL), "cuLaunchKernel")) goto cleanup;
    if (!cuda_ok(cuCtxSynchronize(), "cuCtxSynchronize")) goto cleanup;
    if (!cuda_ok(cuMemcpyDtoH(actual, output_device, byte_count), "cuMemcpyDtoH")) goto cleanup;
    if (memcmp(actual, expected, byte_count) != 0) {
        for (int i = 0; i < BATCH * N; ++i) {
            if (actual[i] != expected[i]) {
                fprintf(stderr, "device=%d mismatch index=%d expected=%d actual=%d\n",
                        ordinal, i, expected[i], actual[i]);
                break;
            }
        }
        goto cleanup;
    }
    void *inverse_args[] = {&output_device, &input_device, &polynomial_count};
    if (!cuda_ok(cuLaunchKernel(inverse_kernel, BATCH, 1, 1, N, 1, 1,
                    0, NULL, inverse_args, NULL), "cuLaunchKernel(inverse)")) goto cleanup;
    if (!cuda_ok(cuCtxSynchronize(), "cuCtxSynchronize(inverse)")) goto cleanup;
    if (!cuda_ok(cuMemcpyDtoH(inverse_actual, input_device, byte_count),
                 "cuMemcpyDtoH(inverse)")) goto cleanup;
    if (memcmp(inverse_actual, inverse_expected, byte_count) != 0) {
        for (int i = 0; i < BATCH * N; ++i) {
            if (inverse_actual[i] != inverse_expected[i]) {
                fprintf(stderr, "device=%d inverse_mismatch index=%d expected=%d actual=%d\n",
                        ordinal, i, inverse_expected[i], inverse_actual[i]);
                break;
            }
        }
        goto cleanup;
    }
    printf("PASS backend=cuda device=%d name=%s capability=%d.%d "
           "compile=1 forward=1 inverse=1 submit=1 complete=1 readback=1 "
           "oracle_match=1 batch=%d fixture_id=%s\n",
           ordinal, name, major, minor, BATCH,
           X25519MLKEM768_NTT_FIXTURE_ID);
    if (perf_samples > 0 && !run_performance(forward_kernel, ordinal, name,
            major, minor, perf_samples, minimum_speedup_milli)) goto cleanup;
    ok = 1;

cleanup:
    if (output_device) cuMemFree(output_device);
    if (input_device) cuMemFree(input_device);
    if (module) cuModuleUnload(module);
    if (context) cuCtxDestroy(context);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 2 || argc > 4) {
        fprintf(stderr, "usage: %s <per-architecture-cubin-directory> "
                "[perf-samples>=30] [minimum-speedup-milli]\n", argv[0]);
        return 2;
    }
    int perf_samples = 0;
    int minimum_speedup_milli = 1250;
    if (argc >= 3) {
        char *end = NULL;
        long parsed = strtol(argv[2], &end, 10);
        if (!end || *end != '\0' || parsed < 30 || parsed > 10000) {
            fprintf(stderr, "perf-samples must be an integer from 30 through 10000\n");
            return 2;
        }
        perf_samples = (int)parsed;
    }
    if (argc == 4) {
        char *end = NULL;
        long parsed = strtol(argv[3], &end, 10);
        if (!end || *end != '\0' || parsed < CANONICAL_MIN_SPEEDUP_MILLI ||
                parsed > 100000) {
            fprintf(stderr, "minimum-speedup-milli must be an integer from %d through 100000\n",
                    CANONICAL_MIN_SPEEDUP_MILLI);
            return 2;
        }
        minimum_speedup_milli = (int)parsed;
    }
    int driver_version = 0;
    if (!cuda_ok(cuInit(0), "cuInit") ||
            !cuda_ok(cuDriverGetVersion(&driver_version),
                     "cuDriverGetVersion")) return 1;
    int count = 0;
    if (!cuda_ok(cuDeviceGetCount(&count), "cuDeviceGetCount") || count <= 0) return 1;
    if (perf_samples > 0)
        printf("CUDA_NTT_PERF_DRIVER cuda_driver_version=%d device_count=%d\n",
               driver_version, count);
    int passed = 0;
    for (int device = 0; device < count; ++device)
        passed += run_device(device, argv[1], perf_samples,
                             minimum_speedup_milli);
    return passed == count ? 0 : 1;
}
