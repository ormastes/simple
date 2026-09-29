/* ProcessingIR CUDA offload break-even harness.
 * Build with: cc -O2 -std=c99 -o processing_ir_offload_break_even \
 *     processing_ir_offload_break_even.c -lcuda
 */
#define _POSIX_C_SOURCE 200809L
#include <cuda.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAX_ROWS 8

struct sample {
    long long cpu_us;
    long long device_us;
    long long transfer_us;
    long long total_us;
};

static long long now_ns(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static long long elapsed_us(long long start) {
    long long end = now_ns();
    if (start < 0 || end < start) return -1;
    return (end - start + 999LL) / 1000LL;
}

static uint32_t alpha_pixel(uint32_t s, uint32_t d, uint32_t alpha) {
    uint32_t inv = 255u - alpha;
    uint32_t rb = (((s & 0x00ff00ffu) * alpha) + ((d & 0x00ff00ffu) * inv)) >> 8;
    uint32_t g = (((s & 0x0000ff00u) * alpha) + ((d & 0x0000ff00u) * inv)) >> 8;
    return 0xff000000u | (rb & 0x00ff00ffu) | (g & 0x0000ff00u);
}

static void cpu_alpha(const uint32_t *src, const uint32_t *dst, uint32_t *out,
                      unsigned int count, uint32_t alpha) {
    unsigned int i;
    for (i = 0; i < count; i++) out[i] = alpha_pixel(src[i], dst[i], alpha);
}

static int compare_u32(const uint32_t *left, const uint32_t *right, unsigned int count) {
    return memcmp(left, right, (size_t)count * sizeof(uint32_t)) == 0;
}

static int read_proc_kb(const char *name) {
    char line[128];
    FILE *file = fopen("/proc/self/status", "r");
    int result = 0;
    if (!file) return 0;
    while (fgets(line, sizeof(line), file)) {
        char key[32];
        long value;
        if (sscanf(line, "%31[^:]: %ld", key, &value) == 2 && strcmp(key, name) == 0) {
            result = value > 0 && value <= 2147483647L ? (int)value : 0;
            break;
        }
    }
    fclose(file);
    return result;
}

static void sort_i64(long long *values, int count) {
    int i;
    for (i = 1; i < count; i++) {
        long long value = values[i];
        int j = i - 1;
        while (j >= 0 && values[j] > value) {
            values[j + 1] = values[j];
            j--;
        }
        values[j + 1] = value;
    }
}

static long long median(struct sample *samples, int count, int field) {
    long long values[64];
    int i;
    if (count < 1 || count > 64) return -1;
    for (i = 0; i < count; i++) {
        values[i] = field == 0 ? samples[i].cpu_us :
                    field == 1 ? samples[i].device_us :
                    field == 2 ? samples[i].transfer_us : samples[i].total_us;
    }
    sort_i64(values, count);
    return values[count / 2];
}

static char *read_file(const char *path, size_t *size_out) {
    FILE *file = fopen(path, "rb");
    long size;
    char *data;
    if (!file) return NULL;
    if (fseek(file, 0, SEEK_END) != 0 || (size = ftell(file)) <= 0 ||
        fseek(file, 0, SEEK_SET) != 0) { fclose(file); return NULL; }
    data = (char *)malloc((size_t)size + 1u);
    if (!data || fread(data, 1, (size_t)size, file) != (size_t)size) {
        free(data); fclose(file); return NULL;
    }
    fclose(file);
    data[size] = '\0';
    if (size_out) *size_out = (size_t)size;
    return data;
}

static void emit_failure(const char *reason) {
    printf("processing_ir_offload_status=fail\n");
    printf("processing_ir_offload_reason=%s\n", reason);
    printf("processing_ir_offload_schema=processing-ir-offload-v1\n");
    printf("processing_ir_offload_execution=processing_ir\n");
    printf("processing_ir_offload_backend=cuda\n");
}

static int run_gpu(CUfunction alpha_fn, CUdeviceptr src_device, CUdeviceptr dst_device,
                   const uint32_t *src, const uint32_t *dst, uint32_t *out,
                   unsigned int count, uint32_t alpha, struct sample *sample) {
    CUresult result;
    CUevent start_event = NULL, stop_event = NULL;
    unsigned int block = 256u;
    unsigned int grid = (count + block - 1u) / block;
    void *args[] = { &src_device, &dst_device, &alpha, &count };
    long long total_started = now_ns();
    float device_ms = 0.0f;
    int ok = 0;

    if (total_started < 0) return 0;
    if (sample && (cuEventCreate(&start_event, CU_EVENT_DEFAULT) != CUDA_SUCCESS ||
                   cuEventCreate(&stop_event, CU_EVENT_DEFAULT) != CUDA_SUCCESS)) goto done;
    result = cuMemcpyHtoD(src_device, src, (size_t)count * sizeof(uint32_t));
    if (result != CUDA_SUCCESS) goto done;
    result = cuMemcpyHtoD(dst_device, dst, (size_t)count * sizeof(uint32_t));
    if (result != CUDA_SUCCESS) goto done;
    if (sample && cuEventRecord(start_event, 0) != CUDA_SUCCESS) goto done;
    result = cuLaunchKernel(alpha_fn, grid, 1, 1, block, 1, 1, 0, NULL, args, NULL);
    if (result != CUDA_SUCCESS) goto done;
    if (sample) {
        long long total_us;
        if (cuEventRecord(stop_event, 0) != CUDA_SUCCESS ||
            cuEventSynchronize(stop_event) != CUDA_SUCCESS ||
            cuEventElapsedTime(&device_ms, start_event, stop_event) != CUDA_SUCCESS) goto done;
        sample->device_us = (long long)(device_ms * 1000.0f + 0.999f);
        if (sample->device_us < 1) goto done;
        result = cuMemcpyDtoH(out, dst_device, (size_t)count * sizeof(uint32_t));
        if (result != CUDA_SUCCESS) goto done;
        total_us = elapsed_us(total_started);
        if (total_us <= sample->device_us) goto done;
        sample->total_us = total_us;
        sample->transfer_us = total_us - sample->device_us;
        ok = 1;
    } else {
        if (cuCtxSynchronize() != CUDA_SUCCESS) goto done;
        result = cuMemcpyDtoH(out, dst_device, (size_t)count * sizeof(uint32_t));
        if (result != CUDA_SUCCESS) goto done;
        ok = elapsed_us(total_started) > 0;
    }

done:
    if (stop_event) cuEventDestroy(stop_event);
    if (start_event) cuEventDestroy(start_event);
    return ok;
}

static int self_test(void) {
    uint32_t src[] = { 0xff204060u, 0xff204061u };
    uint32_t dst[] = { 0xff102030u, 0xff102031u };
    uint32_t out[2];
    struct sample values[5] = {
        {9, 8, 7, 15}, {1, 2, 3, 5}, {7, 6, 5, 11}, {3, 4, 9, 13}, {5, 1, 1, 2}
    };
    cpu_alpha(src, dst, out, 2, 128u);
    if (out[0] != alpha_pixel(src[0], dst[0], 128u) || median(values, 5, 0) != 5 ||
        median(values, 5, 1) != 4 || median(values, 5, 2) != 5 ||
        median(values, 5, 3) != 11 ||
        read_proc_kb("VmRSS") < 1 || read_proc_kb("VmHWM") < 1) return 1;
    puts("processing_ir_offload_harness_self_test=pass");
    return 0;
}

int main(int argc, char **argv) {
    const char *ptx_path;
    const char *samples_path;
    char *ptx = NULL;
    CUcontext context = NULL;
    CUdevice device = 0;
    CUmodule module = NULL;
    CUfunction alpha_fn = NULL;
    CUdeviceptr src_device = 0, dst_device = 0;
    unsigned int batches[MAX_ROWS];
    long long transfer_medians[MAX_ROWS];
    int row_count, warmups, measured, row, sample_index;
    int cpu_rss, gpu_rss, peak_rss;
    int first_fast = -1;
    FILE *samples_file = NULL;
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) return self_test();
    if (argc < 8 || argc > 13) { emit_failure("invalid-argv"); return 2; }
    ptx_path = argv[1];
    warmups = atoi(argv[2]);
    measured = atoi(argv[3]);
    samples_path = argv[4];
    row_count = argc - 5;
    if (warmups < 3 || measured < 5 || row_count < 3 || row_count > MAX_ROWS) {
        emit_failure("invalid-sample-or-row-count"); return 2;
    }
    for (row = 0; row < row_count; row++) {
        char *end = NULL;
        unsigned long batch = strtoul(argv[row + 5], &end, 10);
        if (!end || *end || batch == 0 || batch > 67108864UL ||
            (row > 0 && batch <= batches[row - 1])) { emit_failure("invalid-batches"); return 2; }
        batches[row] = (unsigned int)batch;
    }
    samples_file = fopen(samples_path, "w");
    if (!samples_file) { emit_failure("raw-log-open-failed"); return 2; }
    ptx = read_file(ptx_path, NULL);
    if (!ptx) { fclose(samples_file); emit_failure("missing-ptx"); return 2; }
    if (cuInit(0) != CUDA_SUCCESS) { free(ptx); fclose(samples_file); emit_failure("cuda-init-failed"); return 3; }
    {
        int device_count = 0;
        if (cuDeviceGetCount(&device_count) != CUDA_SUCCESS || device_count < 1 ||
            cuDeviceGet(&device, 0) != CUDA_SUCCESS ||
            cuDevicePrimaryCtxRetain(&context, device) != CUDA_SUCCESS ||
            cuCtxSetCurrent(context) != CUDA_SUCCESS ||
            cuModuleLoadData(&module, ptx) != CUDA_SUCCESS ||
            cuModuleGetFunction(&alpha_fn, module, "simple_2d_alpha_u32") != CUDA_SUCCESS) {
            if (module) cuModuleUnload(module);
            if (context) cuDevicePrimaryCtxRelease(device);
            free(ptx); fclose(samples_file); emit_failure("cuda-module-or-device-unavailable"); return 3;
        }
    }
    fprintf(samples_file, "# batch sample cpu_us device_us transfer_us total_us\n");
    cpu_rss = 0;
    gpu_rss = 0;
    peak_rss = 0;
    for (row = 0; row < row_count; row++) {
        unsigned int count = batches[row];
        size_t bytes = (size_t)count * sizeof(uint32_t);
        uint32_t *src = (uint32_t *)malloc(bytes);
        uint32_t *dst = (uint32_t *)malloc(bytes);
        uint32_t *cpu_out = (uint32_t *)malloc(bytes);
        uint32_t *gpu_out = (uint32_t *)malloc(bytes);
        struct sample values[64];
        long long cpu_median, device_median, transfer_summary, total_median;
        int rss;
        if (!src || !dst || !cpu_out || !gpu_out) {
            free(src); free(dst); free(cpu_out); free(gpu_out);
            cuModuleUnload(module); cuDevicePrimaryCtxRelease(device); free(ptx); fclose(samples_file);
            emit_failure("allocation-failed"); return 3;
        }
        for (sample_index = 0; sample_index < (int)count; sample_index++) {
            src[sample_index] = 0xff204060u + (uint32_t)sample_index;
            dst[sample_index] = 0xff102030u + (uint32_t)sample_index;
        }
        for (sample_index = 0; sample_index < warmups; sample_index++) {
            cpu_alpha(src, dst, cpu_out, count, 128u);
        }
        rss = read_proc_kb("VmRSS");
        if (rss > cpu_rss) cpu_rss = rss;
        if (cuMemAlloc(&src_device, bytes) != CUDA_SUCCESS ||
            cuMemAlloc(&dst_device, bytes) != CUDA_SUCCESS) {
            if (src_device) cuMemFree(src_device);
            if (dst_device) cuMemFree(dst_device);
            free(src); free(dst); free(cpu_out); free(gpu_out);
            cuModuleUnload(module); cuDevicePrimaryCtxRelease(device); free(ptx); fclose(samples_file);
            emit_failure("device-allocation-failed"); return 3;
        }
        for (sample_index = 0; sample_index < warmups; sample_index++) {
            if (!run_gpu(alpha_fn, src_device, dst_device, src, dst, gpu_out, count, 128u, NULL) ||
                !compare_u32(cpu_out, gpu_out, count)) {
                cuMemFree(src_device); cuMemFree(dst_device); free(src); free(dst); free(cpu_out); free(gpu_out);
                cuModuleUnload(module); cuDevicePrimaryCtxRelease(device); free(ptx); fclose(samples_file);
                emit_failure("warmup-device-or-result-mismatch"); return 3;
            }
        }
        rss = read_proc_kb("VmRSS");
        if (rss > gpu_rss) gpu_rss = rss;
        for (sample_index = 0; sample_index < measured; sample_index++) {
            long long started = now_ns();
            cpu_alpha(src, dst, cpu_out, count, 128u);
            values[sample_index].cpu_us = elapsed_us(started);
            if (values[sample_index].cpu_us < 1 ||
                !run_gpu(alpha_fn, src_device, dst_device, src, dst, gpu_out, count, 128u, &values[sample_index]) ||
                !compare_u32(cpu_out, gpu_out, count)) {
                cuMemFree(src_device); cuMemFree(dst_device); free(src); free(dst); free(cpu_out); free(gpu_out);
                cuModuleUnload(module); cuDevicePrimaryCtxRelease(device); free(ptx); fclose(samples_file);
                emit_failure("measured-device-or-result-mismatch"); return 3;
            }
            fprintf(samples_file, "%u %d %lld %lld %lld %lld\n", count, sample_index,
                    values[sample_index].cpu_us, values[sample_index].device_us,
                    values[sample_index].transfer_us, values[sample_index].total_us);
        }
        cpu_median = median(values, measured, 0);
        device_median = median(values, measured, 1);
        total_median = median(values, measured, 3);
        transfer_summary = total_median - device_median;
        if (cpu_median < 1 || device_median < 1 || transfer_summary < 1) {
            cuMemFree(src_device); cuMemFree(dst_device); free(src); free(dst); free(cpu_out); free(gpu_out);
            cuModuleUnload(module); cuDevicePrimaryCtxRelease(device); free(ptx); fclose(samples_file);
            emit_failure("non-monotonic-timing"); return 3;
        }
        printf("processing_ir_offload_row_%d_batch=%u\n", row, count);
        printf("processing_ir_offload_row_%d_cpu_us=%lld\n", row, cpu_median);
        printf("processing_ir_offload_row_%d_device_us=%lld\n", row, device_median);
        /* Compatibility key: this is all non-device round-trip overhead, not DMA alone. */
        printf("processing_ir_offload_row_%d_transfer_us=%lld\n", row, transfer_summary);
        printf("processing_ir_offload_row_%d_total_us=%lld\n", row, total_median);
        printf("processing_ir_offload_row_%d_decision=%s\n", row,
               total_median < cpu_median ? "gpu" : "cpu");
        if (total_median < cpu_median && first_fast < 0) first_fast = row;
        transfer_medians[row] = transfer_summary;
        cuMemFree(src_device); src_device = 0;
        cuMemFree(dst_device); dst_device = 0;
        free(src); free(dst); free(cpu_out); free(gpu_out);
    }
    peak_rss = read_proc_kb("VmHWM");
    if (cpu_rss > peak_rss) peak_rss = cpu_rss;
    if (gpu_rss > peak_rss) peak_rss = gpu_rss;
    fclose(samples_file);
    cuModuleUnload(module);
    cuDevicePrimaryCtxRelease(device);
    free(ptx);
    if (cpu_rss < 1 || gpu_rss < 1 || peak_rss < 1) {
        emit_failure("procfs-rss-unavailable"); return 3;
    }
    if (first_fast < 1) { emit_failure("no-measured-break-even"); return 4; }
    printf("processing_ir_offload_status=pass\n");
    printf("processing_ir_offload_reason=measured-cuda-alpha-break-even\n");
    printf("processing_ir_offload_schema=processing-ir-offload-v1\n");
    printf("processing_ir_offload_execution=processing_ir\n");
    printf("processing_ir_offload_backend=cuda\n");
    printf("processing_ir_offload_aggregate=median\n");
    printf("processing_ir_offload_timing_unit=us\n");
    printf("processing_ir_offload_rss_source=procfs\n");
    printf("processing_ir_offload_warmup_samples=%d\n", warmups);
    printf("processing_ir_offload_measured_samples=%d\n", measured);
    printf("processing_ir_offload_row_count=%d\n", row_count);
    printf("processing_ir_offload_cpu_rss_kb=%d\n", cpu_rss);
    printf("processing_ir_offload_gpu_rss_kb=%d\n", gpu_rss);
    printf("processing_ir_offload_peak_rss_kb=%d\n", peak_rss);
    printf("processing_ir_offload_communication_overhead_us=%lld\n", transfer_medians[first_fast]);
    printf("processing_ir_offload_break_even_batch=%u\n", batches[first_fast]);
    return 0;
}
