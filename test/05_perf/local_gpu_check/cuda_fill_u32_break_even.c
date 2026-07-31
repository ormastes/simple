/* Production-equivalent ProcessingIr FillU32 CUDA break-even probe.
 * Build: cc -O2 -std=c99 -o cuda_fill_u32_break_even cuda_fill_u32_break_even.c -ldl
 */
#define _POSIX_C_SOURCE 200809L
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef int CUresult;
typedef int CUdevice;
typedef void *CUcontext;
typedef void *CUmodule;
typedef void *CUfunction;
typedef uint64_t CUdeviceptr;
typedef struct { unsigned char bytes[16]; } CUuuid;
enum { CUDA_SUCCESS = 0, CUDA_BLOCK_SIZE = 256 };

typedef CUresult (*init_fn)(unsigned int);
typedef CUresult (*count_fn)(int *);
typedef CUresult (*get_fn)(CUdevice *, int);
typedef CUresult (*name_fn)(char *, int, CUdevice);
typedef CUresult (*uuid_fn)(CUuuid *, CUdevice);
typedef CUresult (*retain_fn)(CUcontext *, CUdevice);
typedef CUresult (*set_fn)(CUcontext);
typedef CUresult (*release_fn)(CUdevice);
typedef CUresult (*alloc_fn)(CUdeviceptr *, size_t);
typedef CUresult (*free_fn)(CUdeviceptr);
typedef CUresult (*d2h_fn)(void *, CUdeviceptr, size_t);
typedef CUresult (*module_load_fn)(CUmodule *, const void *);
typedef CUresult (*module_unload_fn)(CUmodule);
typedef CUresult (*function_fn)(CUfunction *, CUmodule, const char *);
typedef CUresult (*launch_fn)(CUfunction, unsigned int, unsigned int, unsigned int,
                              unsigned int, unsigned int, unsigned int, unsigned int,
                              void *, void **, void **);
typedef CUresult (*sync_fn)(void);

struct api {
    void *lib;
    init_fn init; count_fn count; get_fn get; name_fn name; uuid_fn uuid;
    retain_fn retain; set_fn set; release_fn release;
    alloc_fn alloc; free_fn free; d2h_fn d2h;
    module_load_fn module_load; module_unload_fn module_unload; function_fn function;
    launch_fn launch; sync_fn sync;
};

struct sample {
    long long cpu_us;
    long long allocation_us;
    long long launch_sync_us;
    long long readback_us;
    long long conversion_cleanup_us;
    long long total_us;
    long long mismatch_count;
};

static const char processing_fill_u32_ptx[] =
    ".version 7.0\n.target sm_52\n.address_size 64\n\n.visible .entry processing_fill_u32(\n"
    "    .param .u64 output,\n    .param .u32 value,\n    .param .u32 count\n) {\n"
    "    .reg .pred %p;\n    .reg .b32 %r<6>;\n    .reg .b64 %rd<4>;\n"
    "    mov.u32 %r0, %ctaid.x;\n    mov.u32 %r1, %ntid.x;\n    mov.u32 %r2, %tid.x;\n"
    "    mad.lo.u32 %r3, %r0, %r1, %r2;\n    ld.param.u32 %r4, [count];\n"
    "    setp.ge.u32 %p, %r3, %r4;\n    @%p bra done;\n    ld.param.u64 %rd0, [output];\n"
    "    mul.wide.u32 %rd1, %r3, 4;\n    add.u64 %rd2, %rd0, %rd1;\n"
    "    ld.param.u32 %r5, [value];\n    st.global.u32 [%rd2], %r5;\ndone:\n    ret;\n}\n";

static long long now_ns(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) return -1;
    return (long long)t.tv_sec * 1000000000LL + t.tv_nsec;
}

static long long elapsed_us(long long start, long long end) {
    return start < 0 || end < start ? -1 : (end - start + 999LL) / 1000LL;
}

static int parse_int(const char *text, int minimum, int maximum, int *out) {
    char *end = NULL;
    long value = strtol(text, &end, 10);
    if (!text[0] || !end || *end || value < minimum || value > maximum) return 0;
    *out = (int)value;
    return 1;
}

static void fill_cpu(uint32_t *out, unsigned int count, uint32_t value) {
    unsigned int i;
    for (i = 0; i < count; i++) out[i] = value;
}

static long long mismatches(const uint32_t *expected, const uint32_t *actual, unsigned int count) {
    unsigned int i;
    long long result = 0;
    for (i = 0; i < count; i++) result += expected[i] != actual[i];
    return result;
}

static void sort_i64(long long *values, int count) {
    int i;
    for (i = 1; i < count; i++) {
        long long value = values[i];
        int j = i - 1;
        while (j >= 0 && values[j] > value) { values[j + 1] = values[j]; j--; }
        values[j + 1] = value;
    }
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

static long long median(const struct sample *samples, int count, int field) {
    long long values[64];
    int i;
    for (i = 0; i < count; i++) {
        values[i] = field == 0 ? samples[i].cpu_us :
                    field == 1 ? samples[i].allocation_us :
                    field == 2 ? samples[i].launch_sync_us :
                    field == 3 ? samples[i].readback_us :
                    field == 4 ? samples[i].conversion_cleanup_us :
                    field == 5 ? samples[i].total_us : samples[i].mismatch_count;
    }
    sort_i64(values, count);
    return values[count / 2];
}

static int load(struct api *api) {
    memset(api, 0, sizeof(*api));
    api->lib = dlopen("libcuda.so.1", RTLD_LAZY);
    if (!api->lib) api->lib = dlopen("libcuda.so", RTLD_LAZY);
    if (!api->lib) return 0;
#define SYMBOL(field, name) api->field = (field##_fn)dlsym(api->lib, name)
    SYMBOL(init, "cuInit"); SYMBOL(count, "cuDeviceGetCount"); SYMBOL(get, "cuDeviceGet");
    SYMBOL(name, "cuDeviceGetName"); SYMBOL(retain, "cuDevicePrimaryCtxRetain");
    SYMBOL(set, "cuCtxSetCurrent"); SYMBOL(release, "cuDevicePrimaryCtxRelease");
    SYMBOL(alloc, "cuMemAlloc_v2"); SYMBOL(free, "cuMemFree_v2"); SYMBOL(d2h, "cuMemcpyDtoH_v2");
    SYMBOL(module_load, "cuModuleLoadData"); SYMBOL(module_unload, "cuModuleUnload");
    SYMBOL(function, "cuModuleGetFunction"); SYMBOL(launch, "cuLaunchKernel"); SYMBOL(sync, "cuCtxSynchronize");
#undef SYMBOL
    api->uuid = (uuid_fn)dlsym(api->lib, "cuDeviceGetUuid_v2");
    if (!api->uuid) api->uuid = (uuid_fn)dlsym(api->lib, "cuDeviceGetUuid");
    return api->init && api->count && api->get && api->name && api->uuid && api->retain && api->set &&
           api->release && api->alloc && api->free && api->d2h && api->module_load && api->module_unload &&
           api->function && api->launch && api->sync;
}

static uint64_t device_identity(const CUuuid *uuid) {
    uint64_t hash = UINT64_C(14695981039346656037);
    uint64_t identity;
    int i;
    for (i = 0; i < 16; i++) if (uuid->bytes[i] != 0) break;
    if (i == 16) return 0;
    for (i = 0; i < 16; i++) { hash ^= uuid->bytes[i]; hash *= UINT64_C(1099511628211); }
    identity = hash & UINT64_C(0x0fffffffffffffff);
    return identity ? identity : 1;
}

static void uuid_hex(const CUuuid *uuid, char out[33]) {
    static const char hex[] = "0123456789abcdef";
    int i;
    for (i = 0; i < 16; i++) { out[i * 2] = hex[uuid->bytes[i] >> 4]; out[i * 2 + 1] = hex[uuid->bytes[i] & 15]; }
    out[32] = '\0';
}

static int cpu_run(unsigned int count, uint32_t value, uint32_t **out, long long *cpu_us) {
    size_t bytes = (size_t)count * sizeof(uint32_t);
    long long start = now_ns();
    uint32_t *values = (uint32_t *)malloc(bytes);
    if (!values) return 0;
    fill_cpu(values, count, value);
    *cpu_us = elapsed_us(start, now_ns());
    if (*cpu_us < 1) { free(values); return 0; }
    *out = values;
    return 1;
}

static int gpu_run(const struct api *api, CUfunction kernel, unsigned int count, uint32_t value,
                   uint32_t **out, struct sample *sample) {
    CUdeviceptr device = 0;
    size_t bytes = (size_t)count * sizeof(uint32_t);
    uint32_t *raw = NULL, *converted = NULL;
    unsigned int grid = (count + CUDA_BLOCK_SIZE - 1u) / CUDA_BLOCK_SIZE;
    void *args[] = { &device, &value, &count };
    long long started = now_ns(), allocated, launched, copied, completed;
    if (started < 0) return 0;
    raw = (uint32_t *)malloc(bytes);
    if (!raw || api->alloc(&device, bytes) != CUDA_SUCCESS) goto failed;
    allocated = now_ns();
    if (api->launch(kernel, grid, 1, 1, CUDA_BLOCK_SIZE, 1, 1, 0, NULL, args, NULL) != CUDA_SUCCESS ||
        api->sync() != CUDA_SUCCESS) goto failed;
    launched = now_ns();
    if (api->d2h(raw, device, bytes) != CUDA_SUCCESS) goto failed;
    copied = now_ns();
    converted = (uint32_t *)malloc(bytes);
    if (!converted) goto failed;
    memcpy(converted, raw, bytes);
    if (api->free(device) != CUDA_SUCCESS) goto failed;
    device = 0;
    free(raw);
    raw = NULL;
    completed = now_ns();
    sample->allocation_us = elapsed_us(started, allocated);
    sample->launch_sync_us = elapsed_us(allocated, launched);
    sample->readback_us = elapsed_us(launched, copied);
    sample->conversion_cleanup_us = elapsed_us(copied, completed);
    sample->total_us = sample->allocation_us + sample->launch_sync_us +
                       sample->readback_us + sample->conversion_cleanup_us;
    if (sample->allocation_us < 1 || sample->launch_sync_us < 1 || sample->readback_us < 1 || sample->conversion_cleanup_us < 1 || sample->total_us < 1) goto failed;
    *out = converted;
    return 1;
failed:
    if (device) api->free(device);
    free(raw);
    free(converted);
    return 0;
}

static void write_receipt(const char *path, const char *device_name, const char *device_uuid,
                          uint64_t identity, const char *raw, int warmups, int samples,
                          const unsigned int *batches, const struct sample *medians,
                          int rows, int first_fast, int cpu_rss, int gpu_rss, int peak_rss) {
    FILE *file = fopen(path, "w");
    int row;
    if (!file) return;
    fprintf(file, "cuda_fill_u32_status=pass\ncuda_fill_u32_schema=processing-cuda-fill-u32-v2\n");
    fprintf(file, "cuda_fill_u32_execution=processing_ir\ncuda_fill_u32_workload=fill_u32_v1\ncuda_fill_u32_workload_kind=output_only\ncuda_fill_u32_backend=cuda\n");
    fprintf(file, "cuda_fill_u32_device=%s\ncuda_fill_u32_device_uuid=%s\ncuda_fill_u32_device_identity=%llu\n", device_name, device_uuid, (unsigned long long)identity);
    fprintf(file, "cuda_fill_u32_context=primary_retained\ncuda_fill_u32_module_cached=true\ncuda_fill_u32_kernel_cached=true\n");
    fprintf(file, "cuda_fill_u32_kernel=processing_fill_u32\ncuda_fill_u32_launch_abi=u64_output_u32_value_u32_count\ncuda_fill_u32_block_size=256\n");
    fprintf(file, "cuda_fill_u32_cpu_workload=fill_u32_v1\ncuda_fill_u32_gpu_workload=fill_u32_v1\ncuda_fill_u32_upload_bytes=0\n");
    fprintf(file, "cuda_fill_u32_warmups=%d\ncuda_fill_u32_samples=%d\ncuda_fill_u32_aggregate=median\ncuda_fill_u32_raw_samples=%s\n", warmups, samples, raw);
    fprintf(file, "cuda_fill_u32_rss_source=procfs\ncuda_fill_u32_cpu_rss_kb=%d\ncuda_fill_u32_gpu_rss_kb=%d\ncuda_fill_u32_peak_rss_kb=%d\n", cpu_rss, gpu_rss, peak_rss);
    fprintf(file, "cuda_fill_u32_executor_timing=allocation_us+launch_sync_us+readback_us+conversion_cleanup_us\n");
    fprintf(file, "cuda_fill_u32_readback_source=device_readback\ncuda_fill_u32_readback_exact=true\ncuda_fill_u32_row_count=%d\n", rows);
    fprintf(file, "cuda_fill_u32_coverage_max_batch=%u\n", batches[rows - 1]);
    for (row = 0; row < rows; row++) {
        const struct sample *s = &medians[row];
        fprintf(file, "cuda_fill_u32_row_%d_batch=%u\ncuda_fill_u32_row_%d_cpu_us=%lld\ncuda_fill_u32_row_%d_allocation_us=%lld\n", row, batches[row], row, s->cpu_us, row, s->allocation_us);
        fprintf(file, "cuda_fill_u32_row_%d_launch_sync_us=%lld\ncuda_fill_u32_row_%d_readback_us=%lld\ncuda_fill_u32_row_%d_conversion_cleanup_us=%lld\ncuda_fill_u32_row_%d_executor_total_us=%lld\ncuda_fill_u32_row_%d_total_us=%lld\n", row, s->launch_sync_us, row, s->readback_us, row, s->conversion_cleanup_us, row, s->total_us, row, s->total_us);
        fprintf(file, "cuda_fill_u32_row_%d_mismatch_count=%lld\ncuda_fill_u32_row_%d_readback_exact=true\ncuda_fill_u32_row_%d_decision=%s\n", row, s->mismatch_count, row, row, s->total_us < s->cpu_us ? "gpu" : "cpu");
    }
    fprintf(file, "cuda_fill_u32_break_even_found=%s\ncuda_fill_u32_break_even_batch=%u\ncuda_fill_u32_break_even_row=%d\n", first_fast >= 0 ? "true" : "false", first_fast >= 0 ? batches[first_fast] : 0, first_fast);
    fclose(file);
}

static int dump_ptx(const char *path) {
    FILE *file = fopen(path, "w");
    if (!file) return 0;
    if (fputs(processing_fill_u32_ptx, file) < 0 || fclose(file) != 0) return 0;
    return 1;
}

int main(int argc, char **argv) {
    struct api api;
    CUdevice device;
    CUcontext context = NULL;
    CUmodule module = NULL;
    CUfunction kernel = NULL;
    CUuuid uuid;
    char device_name[256] = {0}, uuid_text[33];
    unsigned int batches[8];
    struct sample medians[8];
    const uint32_t value = UINT32_C(0xA5A5A5A5);
    FILE *raw;
    int warmups, samples, batch_count, row, sample, first_fast = -1, device_count;
    int cpu_rss, gpu_rss, peak_rss;
    uint64_t identity;

    if (argc == 3 && strcmp(argv[1], "--dump-ptx") == 0) return dump_ptx(argv[2]) ? 0 : 2;
    if (argc < 8 || argc > 13 || !parse_int(argv[3], 3, 64, &warmups) || !parse_int(argv[4], 5, 64, &samples)) return 2;
    batch_count = argc - 5;
    if (batch_count < 3 || batch_count > 8) return 2;
    for (row = 0; row < batch_count; row++) {
        char *end = NULL;
        unsigned long count = strtoul(argv[row + 5], &end, 10);
        if (!argv[row + 5][0] || !end || *end || count < 1 || count > 67108864UL || (row && count <= batches[row - 1])) return 2;
        batches[row] = (unsigned int)count;
    }
    raw = fopen(argv[1], "w");
    if (!raw) return 2;
    if (!load(&api) || api.init(0) != CUDA_SUCCESS || api.count(&device_count) != CUDA_SUCCESS || device_count < 1 ||
        api.get(&device, 0) != CUDA_SUCCESS || api.name(device_name, 255, device) != CUDA_SUCCESS ||
        api.uuid(&uuid, device) != CUDA_SUCCESS || (identity = device_identity(&uuid)) == 0 ||
        api.retain(&context, device) != CUDA_SUCCESS || api.set(context) != CUDA_SUCCESS ||
        api.module_load(&module, processing_fill_u32_ptx) != CUDA_SUCCESS ||
        api.function(&kernel, module, "processing_fill_u32") != CUDA_SUCCESS) {
        fclose(raw);
        puts("cuda_fill_u32_status=blocked\ncuda_fill_u32_reason=cuda-production-path-unavailable");
        return 3;
    }
    uuid_hex(&uuid, uuid_text);
    cpu_rss = read_proc_kb("VmRSS");
    gpu_rss = 0;
    if (cpu_rss < 1) { api.module_unload(module); api.release(device); fclose(raw); return 3; }
    fprintf(raw, "# batch mode sample cpu_us allocation_us launch_sync_us readback_us conversion_cleanup_us total_us mismatch_count\n");
    for (row = 0; row < batch_count; row++) {
        struct sample values[64];
        unsigned int count = batches[row];
        for (sample = 0; sample < warmups + samples; sample++) {
            uint32_t *cpu = NULL, *gpu = NULL;
            struct sample current;
            long long cpu_us;
            if (!cpu_run(count, value, &cpu, &cpu_us) || !gpu_run(&api, kernel, count, value, &gpu, &current)) {
                free(cpu); free(gpu); api.module_unload(module); api.release(device); fclose(raw); return 3;
            }
            current.cpu_us = cpu_us;
            current.mismatch_count = mismatches(cpu, gpu, count);
            if (current.mismatch_count != 0) {
                free(cpu); free(gpu); api.module_unload(module); api.release(device); fclose(raw); return 3;
            }
            if (sample >= warmups) {
                int measured = sample - warmups;
                values[measured] = current;
                fprintf(raw, "%u output_only %d %lld %lld %lld %lld %lld %lld %lld\n", count, measured, current.cpu_us,
                        current.allocation_us, current.launch_sync_us, current.readback_us, current.conversion_cleanup_us,
                        current.total_us, current.mismatch_count);
            }
            free(cpu); free(gpu);
        }
        medians[row].cpu_us = median(values, samples, 0);
        medians[row].allocation_us = median(values, samples, 1);
        medians[row].launch_sync_us = median(values, samples, 2);
        medians[row].readback_us = median(values, samples, 3);
        medians[row].conversion_cleanup_us = median(values, samples, 4);
        medians[row].total_us = median(values, samples, 5);
        medians[row].mismatch_count = median(values, samples, 6);
        if (medians[row].mismatch_count != 0) { api.module_unload(module); api.release(device); fclose(raw); return 3; }
        if (medians[row].total_us < medians[row].cpu_us && first_fast < 0) first_fast = row;
        if (read_proc_kb("VmRSS") > gpu_rss) gpu_rss = read_proc_kb("VmRSS");
    }
    fclose(raw);
    peak_rss = read_proc_kb("VmHWM");
    if (gpu_rss < 1 || peak_rss < cpu_rss || peak_rss < gpu_rss) {
        api.module_unload(module); api.release(device); return 3;
    }
    write_receipt(argv[2], device_name, uuid_text, identity, argv[1], warmups, samples, batches, medians, batch_count, first_fast, cpu_rss, gpu_rss, peak_rss);
    for (row = 0; row < batch_count; row++) {
        printf("cuda_fill_u32_row=%d\ncuda_fill_u32_batch=%u\ncuda_fill_u32_cpu_us=%lld\ncuda_fill_u32_allocation_us=%lld\ncuda_fill_u32_launch_sync_us=%lld\ncuda_fill_u32_readback_us=%lld\ncuda_fill_u32_conversion_cleanup_us=%lld\ncuda_fill_u32_total_us=%lld\ncuda_fill_u32_mismatch_count=%lld\ncuda_fill_u32_decision=%s\n",
               row, batches[row], medians[row].cpu_us, medians[row].allocation_us, medians[row].launch_sync_us,
               medians[row].readback_us, medians[row].conversion_cleanup_us, medians[row].total_us, medians[row].mismatch_count,
               medians[row].total_us < medians[row].cpu_us ? "gpu" : "cpu");
    }
    printf("cuda_fill_u32_status=pass\ncuda_fill_u32_device=%s\ncuda_fill_u32_device_identity=%llu\ncuda_fill_u32_raw_samples=%s\ncuda_fill_u32_receipt=%s\ncuda_fill_u32_break_even_found=%s\ncuda_fill_u32_break_even_batch=%u\n",
           device_name, (unsigned long long)identity, argv[1], argv[2], first_fast >= 0 ? "true" : "false", first_fast >= 0 ? batches[first_fast] : 0);
    api.module_unload(module);
    api.release(device);
    dlclose(api.lib);
    return 0;
}
