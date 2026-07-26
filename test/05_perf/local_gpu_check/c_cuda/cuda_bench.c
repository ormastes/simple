/* CUDA GPU Perf Benchmark — Driver API
 * Compile: gcc -O2 -o cuda_bench cuda_bench.c -ldl -lrt
 * Run:     ./cuda_bench
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <dlfcn.h>

typedef int CUresult;
typedef void* CUdevice;
typedef void* CUcontext;
typedef void* CUmodule;
typedef void* CUfunction;
typedef unsigned long long CUdeviceptr;

/* Function pointer types for CUDA driver API */
typedef CUresult (*cuInit_t)(unsigned int);
typedef CUresult (*cuDeviceGetCount_t)(int*);
typedef CUresult (*cuDeviceGet_t)(CUdevice*, int);
typedef CUresult (*cuDeviceGetName_t)(char*, int, CUdevice);
typedef CUresult (*cuCtxCreate_t)(CUcontext*, unsigned int, CUdevice);
typedef CUresult (*cuCtxDestroy_t)(CUcontext);
typedef CUresult (*cuCtxSynchronize_t)(void);
typedef CUresult (*cuMemAlloc_t)(CUdeviceptr*, size_t);
typedef CUresult (*cuMemFree_t)(CUdeviceptr);
typedef CUresult (*cuMemsetD32_t)(CUdeviceptr, unsigned int, size_t);
typedef CUresult (*cuMemcpyDtoH_t)(void*, CUdeviceptr, size_t);
typedef CUresult (*cuModuleLoadData_t)(CUmodule*, const void*);
typedef CUresult (*cuModuleGetFunction_t)(CUfunction*, CUmodule, const char*);
typedef CUresult (*cuLaunchKernel_t)(CUfunction, unsigned, unsigned, unsigned,
    unsigned, unsigned, unsigned, unsigned, void*, void**, void**);
typedef CUresult (*cuModuleUnload_t)(CUmodule);

static void* cuda_lib = NULL;
static cuInit_t p_cuInit;
static cuDeviceGetCount_t p_cuDeviceGetCount;
static cuDeviceGet_t p_cuDeviceGet;
static cuDeviceGetName_t p_cuDeviceGetName;
static cuCtxCreate_t p_cuCtxCreate;
static cuCtxDestroy_t p_cuCtxDestroy;
static cuCtxSynchronize_t p_cuCtxSynchronize;
static cuMemAlloc_t p_cuMemAlloc;
static cuMemFree_t p_cuMemFree;
static cuMemsetD32_t p_cuMemsetD32;
static cuMemcpyDtoH_t p_cuMemcpyDtoH;
static cuModuleLoadData_t p_cuModuleLoadData;
static cuModuleGetFunction_t p_cuModuleGetFunction;
static cuLaunchKernel_t p_cuLaunchKernel;
static cuModuleUnload_t p_cuModuleUnload;

static int load_cuda(void) {
    cuda_lib = dlopen("libcuda.so.1", RTLD_LAZY);
    if (!cuda_lib) cuda_lib = dlopen("libcuda.so", RTLD_LAZY);
    if (!cuda_lib) return -1;
    p_cuInit = (cuInit_t)dlsym(cuda_lib, "cuInit");
    p_cuDeviceGetCount = (cuDeviceGetCount_t)dlsym(cuda_lib, "cuDeviceGetCount");
    p_cuDeviceGet = (cuDeviceGet_t)dlsym(cuda_lib, "cuDeviceGet");
    p_cuDeviceGetName = (cuDeviceGetName_t)dlsym(cuda_lib, "cuDeviceGetName");
    p_cuCtxCreate = (cuCtxCreate_t)dlsym(cuda_lib, "cuCtxCreate_v2");
    p_cuCtxDestroy = (cuCtxDestroy_t)dlsym(cuda_lib, "cuCtxDestroy_v2");
    p_cuCtxSynchronize = (cuCtxSynchronize_t)dlsym(cuda_lib, "cuCtxSynchronize");
    p_cuMemAlloc = (cuMemAlloc_t)dlsym(cuda_lib, "cuMemAlloc_v2");
    p_cuMemFree = (cuMemFree_t)dlsym(cuda_lib, "cuMemFree_v2");
    p_cuMemsetD32 = (cuMemsetD32_t)dlsym(cuda_lib, "cuMemsetD32_v2");
    p_cuMemcpyDtoH = (cuMemcpyDtoH_t)dlsym(cuda_lib, "cuMemcpyDtoH_v2");
    p_cuModuleLoadData = (cuModuleLoadData_t)dlsym(cuda_lib, "cuModuleLoadData");
    p_cuModuleGetFunction = (cuModuleGetFunction_t)dlsym(cuda_lib, "cuModuleGetFunction");
    p_cuLaunchKernel = (cuLaunchKernel_t)dlsym(cuda_lib, "cuLaunchKernel");
    p_cuModuleUnload = (cuModuleUnload_t)dlsym(cuda_lib, "cuModuleUnload");
    if (!p_cuInit || !p_cuMemAlloc || !p_cuLaunchKernel) return -2;
    return 0;
}

static long long now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (long long)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

static void* (*volatile measured_memset)(void*, int, size_t) = memset;

static int offload_preferred(long long cpu_ns, long long device_ns) {
    return cpu_ns > 0 && device_ns > 0 && cpu_ns >= device_ns &&
        cpu_ns - device_ns >= device_ns / 2 + device_ns % 2;
}

static int self_test(void) {
    unsigned char buf[8] = {0};
    struct timespec delay = { .tv_nsec = 1000000 };
    long long started = now_ns();
    nanosleep(&delay, NULL);
    measured_memset(buf, 0x1E, sizeof(buf));
    if (now_ns() <= started || buf[0] != 0x1E || buf[7] != 0x1E ||
            !offload_preferred(150, 100) || offload_preferred(149, 100) ||
            !offload_preferred(152, 101) || offload_preferred(151, 101)) {
        printf("cuda_bench_self_test=fail\n");
        return 1;
    }
    printf("cuda_bench_self_test=pass\n");
    return 0;
}

static CUresult launch_clear(CUfunction func, unsigned int grid, void** params) {
    CUresult status = p_cuLaunchKernel(func, grid, 1, 1, 256, 1, 1, 0, NULL, params, NULL);
    if (status != 0) return status;
    return p_cuCtxSynchronize();
}

static const char ptx_clear[] =
    ".version 7.0\n.target sm_52\n.address_size 64\n"
    ".visible .entry kernel_clear(.param .u64 fb, .param .u32 color, .param .u32 count)\n"
    "{\n.reg .u64 %rd<4>; .reg .u32 %r<6>; .reg .pred %p1;\n"
    "ld.param.u64 %rd1, [fb]; ld.param.u32 %r1, [color]; ld.param.u32 %r2, [count];\n"
    "mov.u32 %r3, %ctaid.x; mov.u32 %r4, %ntid.x; mov.u32 %r5, %tid.x;\n"
    "mad.lo.u32 %r3, %r3, %r4, %r5;\n"
    "setp.ge.u32 %p1, %r3, %r2; @%p1 bra DONE;\n"
    "cvt.u64.u32 %rd2, %r3; shl.b64 %rd2, %rd2, 2; add.u64 %rd3, %rd1, %rd2;\n"
    "st.global.u32 [%rd3], %r1;\nDONE: ret;\n}\n";

int main(int argc, char** argv) {
    if (argc == 2 && strcmp(argv[1], "--self-test") == 0) return self_test();

    printf("========================================\n");
    printf("CUDA GPU Perf Check (C driver API)\n");
    printf("========================================\n");

    if (load_cuda() != 0) {
        printf("FAIL: cannot load libcuda.so\n");
        return 1;
    }
    if (p_cuInit(0) != 0) { printf("FAIL: cuInit\n"); return 1; }

    int dev_count = 0;
    p_cuDeviceGetCount(&dev_count);
    printf("Devices: %d\n", dev_count);
    if (dev_count <= 0) { printf("FAIL: no devices\n"); return 1; }

    CUdevice dev;
    p_cuDeviceGet(&dev, 0);
    char name[256] = {0};
    p_cuDeviceGetName(name, 255, dev);
    printf("Device: %s\n", name);

    CUcontext ctx;
    if (p_cuCtxCreate(&ctx, 0, dev) != 0) { printf("FAIL: ctx\n"); return 1; }
    printf("Context: OK\n\n");

    int W = 1920, H = 1080;
    int pixels = W * H;
    size_t bytes = (size_t)pixels * 4;
    CUdeviceptr d_fb;
    if (p_cuMemAlloc(&d_fb, bytes) != 0) { printf("FAIL: alloc\n"); return 1; }
    printf("Allocated: %zu bytes on device\n", bytes);

    /* --- Test 1: memset clear --- */
    printf("\n--- Test 1: cuMemsetD32 1080p ---\n");
    p_cuMemsetD32(d_fb, 0xFF1E1E1E, pixels);
    p_cuCtxSynchronize();

    long long t0 = now_ns();
    for (int i = 0; i < 100; i++) {
        p_cuMemsetD32(d_fb, 0xFF1E1E1E, pixels);
        p_cuCtxSynchronize();
    }
    long long elapsed_ns = now_ns() - t0;
    printf("  100 clears: %.3f ms\n", (double)elapsed_ns / 1000000.0);
    printf("  Avg clear: %.3f ms\n", (double)elapsed_ns / 100000000.0);

    /* --- Test 2: PTX kernel launch --- */
    printf("\n--- Test 2: PTX kernel 1080p ---\n");
    CUmodule mod;
    if (p_cuModuleLoadData(&mod, ptx_clear) != 0) {
        printf("  FAIL: PTX load\n");
        return 1;
    } else {
        CUfunction func;
        if (p_cuModuleGetFunction(&func, mod, "kernel_clear") != 0) {
            printf("  FAIL: PTX function lookup\n");
            return 1;
        }
        printf("  PTX loaded, function acquired\n");

        unsigned int color = 0xFF0000FF;
        unsigned int count = pixels;
        void* params[] = { &d_fb, &color, &count };
        unsigned int grid = (pixels + 255) / 256;

        /* Warmup */
        for (int i = 0; i < 5; i++) {
            if (launch_clear(func, grid, params) != 0) {
                printf("  FAIL: PTX warmup launch\n");
                return 1;
            }
        }

        /* Timed: 100 kernel launches */
        t0 = now_ns();
        for (int i = 0; i < 100; i++) {
            if (launch_clear(func, grid, params) != 0) {
                printf("  FAIL: PTX timed launch\n");
                return 1;
            }
        }
        elapsed_ns = now_ns() - t0;
        printf("  100 kernel clears: %.3f ms\n", (double)elapsed_ns / 1000000.0);
        printf("  Avg kernel: %.3f ms\n", (double)elapsed_ns / 100000000.0);

        p_cuModuleUnload(mod);
    }

    /* --- Test 3: Readback --- */
    printf("\n--- Test 3: Readback ---\n");
    unsigned char* host = malloc(bytes);
    t0 = now_ns();
    if (!host || p_cuMemcpyDtoH(host, d_fb, bytes) != 0) {
        printf("  FAIL: readback\n");
        return 1;
    }
    long long rb_ns = now_ns() - t0;
    printf("  Readback %zu bytes: %.3f ms\n", bytes, (double)rb_ns / 1000000.0);
    printf("  First pixel RGBA: %d,%d,%d,%d\n", host[0], host[1], host[2], host[3]);

    /* --- CPU comparison (memset) --- */
    printf("\n--- Test 4: CPU memset comparison ---\n");
    unsigned char* cpu_buf = malloc(bytes);
    t0 = now_ns();
    for (int i = 0; i < 100; i++) {
        measured_memset(cpu_buf, 0x1E, bytes);
    }
    long long cpu_ns = now_ns() - t0;
    printf("  100 CPU memsets: %.3f ms\n", (double)cpu_ns / 1000000.0);
    printf("  Avg CPU memset: %.3f ms\n", (double)cpu_ns / 100000000.0);

    /* --- Verdict --- */
    printf("\n========================================\n");
    printf("VERDICT\n");
    printf("========================================\n");
    double gpu_avg = (double)elapsed_ns / 100000000.0;
    double cpu_avg = (double)cpu_ns / 100000000.0;
    double roundtrip_avg = gpu_avg + (double)rb_ns / 1000000.0;
    printf("  GPU kernel clear: %.2f ms\n", gpu_avg);
    printf("  CPU memset clear: %.2f ms\n", cpu_avg);
    printf("  GPU clear + readback: %.2f ms\n", roundtrip_avg);
    if (gpu_avg > 0 && cpu_avg > 0) {
        double ratio = cpu_avg / gpu_avg;
        printf("  Speedup: %.1fx\n", ratio);
        if (gpu_avg <= cpu_avg) printf("  PASS: GPU equal or better\n");
        else if (gpu_avg <= cpu_avg * 1.25) printf("  ACCEPTABLE: within 1.25x\n");
        else printf("  WARN: GPU slower (sync overhead)\n");
    }
    if (offload_preferred(cpu_ns, elapsed_ns)) printf("  Compute offload: preferred\n");
    else printf("  Compute offload: available-not-preferred\n");
    if (offload_preferred(cpu_ns, elapsed_ns + rb_ns * 100)) printf("  Roundtrip offload: preferred\n");
    else printf("  Roundtrip offload: available-not-preferred (communication overhead)\n");
    if (gpu_avg < 16.7) printf("  60Hz capable: YES (%.2f ms < 16.7 ms)\n", gpu_avg);
    else printf("  60Hz capable: NO (%.2f ms > 16.7 ms)\n", gpu_avg);
    printf("========================================\n");

    free(host); free(cpu_buf);
    p_cuMemFree(d_fb);
    p_cuCtxDestroy(ctx);
    dlclose(cuda_lib);
    return 0;
}
