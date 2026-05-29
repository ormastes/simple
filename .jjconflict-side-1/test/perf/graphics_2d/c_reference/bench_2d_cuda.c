/* bench_2d_cuda.c — C CUDA GPU benchmark using PTX kernel launches
 *
 * Uses cuLaunchKernel with embedded PTX for true GPU-parallel rendering.
 * Scenes: fill_1080p, blit_tiles, clipped_scroll (same as bench_2d.c CPU ref).
 *
 * Build: gcc -O2 -o bench_2d_cuda bench_2d_cuda.c -ldl -lrt
 * Run:   ./bench_2d_cuda
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#include <time.h>
#include <stdint.h>

typedef int CUresult;
typedef void* CUcontext;
typedef void* CUmodule;
typedef void* CUfunction;
typedef unsigned long long CUdeviceptr;

typedef CUresult (*cuInit_t)(unsigned int);
typedef CUresult (*cuDeviceGet_t)(int*, int);
typedef CUresult (*cuDeviceGetName_t)(char*, int, int);
typedef CUresult (*cuCtxCreate_t)(CUcontext*, unsigned int, int);
typedef CUresult (*cuCtxSynchronize_t)(void);
typedef CUresult (*cuMemAlloc_t)(CUdeviceptr*, size_t);
typedef CUresult (*cuMemFree_t)(CUdeviceptr);
typedef CUresult (*cuMemsetD32_t)(CUdeviceptr, unsigned int, size_t);
typedef CUresult (*cuModuleLoadData_t)(CUmodule*, const void*);
typedef CUresult (*cuModuleGetFunction_t)(CUfunction*, CUmodule, const char*);
typedef CUresult (*cuLaunchKernel_t)(CUfunction, unsigned, unsigned, unsigned,
                                     unsigned, unsigned, unsigned,
                                     unsigned, void*, void**, void**);

#define FRAME_W 1920
#define FRAME_H 1080
#define PIXELS  (FRAME_W * FRAME_H)
#define FB_BYTES (PIXELS * 4)
#define WARMUP_FRAMES 10
#define TIMED_FRAMES 100

static const char *ptx_source =
    ".version 8.5\n"
    ".target sm_86\n"
    ".address_size 64\n"
    "\n"
    ".visible .entry kernel_clear(\n"
    "    .param .u64 param_fb,\n"
    "    .param .u32 param_color,\n"
    "    .param .u32 param_count\n"
    ") {\n"
    "    .reg .u32 %r<8>;\n"
    "    .reg .u64 %rd<4>;\n"
    "    .reg .pred %p1;\n"
    "    mov.u32 %r0, %tid.x;\n"
    "    mov.u32 %r1, %ntid.x;\n"
    "    mov.u32 %r2, %ctaid.x;\n"
    "    mul.lo.u32 %r3, %r2, %r1;\n"
    "    add.u32 %r4, %r3, %r0;\n"
    "    ld.param.u32 %r5, [param_count];\n"
    "    setp.ge.u32 %p1, %r4, %r5;\n"
    "    @%p1 bra done;\n"
    "    ld.param.u64 %rd0, [param_fb];\n"
    "    ld.param.u32 %r6, [param_color];\n"
    "    mul.wide.u32 %rd1, %r4, 4;\n"
    "    add.u64 %rd2, %rd0, %rd1;\n"
    "    st.global.u32 [%rd2], %r6;\n"
    "done:\n"
    "    ret;\n"
    "}\n"
    "\n"
    ".visible .entry kernel_draw_rect_filled(\n"
    "    .param .u64 param_fb,\n"
    "    .param .u32 param_x,\n"
    "    .param .u32 param_y,\n"
    "    .param .u32 param_w,\n"
    "    .param .u32 param_h,\n"
    "    .param .u32 param_stride,\n"
    "    .param .u32 param_color\n"
    ") {\n"
    "    .reg .u32 %r<16>;\n"
    "    .reg .u64 %rd<6>;\n"
    "    .reg .pred %p1, %p2;\n"
    "    mov.u32 %r0, %tid.x;\n"
    "    mov.u32 %r1, %ntid.x;\n"
    "    mov.u32 %r2, %ctaid.x;\n"
    "    mul.lo.u32 %r3, %r2, %r1;\n"
    "    add.u32 %r4, %r3, %r0;\n"
    "    ld.param.u32 %r5, [param_w];\n"
    "    ld.param.u32 %r6, [param_h];\n"
    "    mul.lo.u32 %r7, %r5, %r6;\n"
    "    setp.ge.u32 %p1, %r4, %r7;\n"
    "    @%p1 bra rect_done;\n"
    "    div.u32 %r8, %r4, %r5;\n"
    "    rem.u32 %r9, %r4, %r5;\n"
    "    ld.param.u32 %r10, [param_x];\n"
    "    ld.param.u32 %r11, [param_y];\n"
    "    add.u32 %r12, %r10, %r9;\n"
    "    add.u32 %r13, %r11, %r8;\n"
    "    ld.param.u32 %r14, [param_stride];\n"
    "    mul.lo.u32 %r15, %r13, %r14;\n"
    "    add.u32 %r15, %r15, %r12;\n"
    "    ld.param.u64 %rd0, [param_fb];\n"
    "    mul.wide.u32 %rd1, %r15, 4;\n"
    "    add.u64 %rd2, %rd0, %rd1;\n"
    "    ld.param.u32 %r10, [param_color];\n"
    "    st.global.u32 [%rd2], %r10;\n"
    "rect_done:\n"
    "    ret;\n"
    "}\n";

static cuCtxSynchronize_t p_ctx_sync;
static cuLaunchKernel_t p_launch;
static CUfunction f_clear, f_rect;
static CUdeviceptr d_fb;

static void gpu_clear(unsigned int color) {
    unsigned int count = PIXELS;
    void *args[] = { &d_fb, &color, &count };
    unsigned int blocks = (PIXELS + 255) / 256;
    p_launch(f_clear, blocks, 1, 1, 256, 1, 1, 0, NULL, args, NULL);
}

static void gpu_rect_fill(int x, int y, int w, int h, unsigned int color) {
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > FRAME_W) w = FRAME_W - x;
    if (y + h > FRAME_H) h = FRAME_H - y;
    if (w <= 0 || h <= 0) return;
    unsigned int ux = x, uy = y, uw = w, uh = h;
    unsigned int stride = FRAME_W;
    unsigned int total = uw * uh;
    unsigned int blocks = (total + 255) / 256;
    void *args[] = { &d_fb, &ux, &uy, &uw, &uh, &stride, &color };
    p_launch(f_rect, blocks, 1, 1, 256, 1, 1, 0, NULL, args, NULL);
}

static void gpu_sync(void) { p_ctx_sync(); }

static unsigned int fill_color(int idx) {
    switch (idx % 5) {
        case 0: return 0xFF0000FF;
        case 1: return 0xFF00FF00;
        case 2: return 0xFFFF0000;
        case 3: return 0xFF808080;
        default: return 0xFF00FFFF;
    }
}

static int scene_fill(void) {
    gpu_clear(0xFF000000);
    for (int i = 0; i < 100; i++) {
        int rx = (i * 19) % (FRAME_W - 1);
        int ry = (i * 11) % (FRAME_H - 1);
        int rw = 1 + (i * 7) % FRAME_W;
        int rh = 1 + (i * 13) % FRAME_H;
        gpu_rect_fill(rx, ry, rw, rh, fill_color((i * 37) % 5));
    }
    gpu_sync();
    return 101;
}

static int scene_blit(void) {
    gpu_clear(0xFF000000);
    int count = 1;
    for (int ty = 0; ty < FRAME_H; ty += 64) {
        for (int tx = 0; tx < FRAME_W; tx += 64) {
            gpu_rect_fill(tx, ty, 64, 64, fill_color(((tx/64)+(ty/64))%4));
            count++;
        }
    }
    gpu_sync();
    return count;
}

static int scene_scroll(void) {
    int cx = FRAME_W/4, cy = FRAME_H/4, cw = FRAME_W/2;
    gpu_clear(0xFF808080);
    int count = 2;
    for (int row = 0; row < 4; row++) {
        int ry = cy + row * 3 - 1;
        unsigned int rc = (row%2==1) ? 0xFF000000 : 0xFFFFFFFF;
        gpu_rect_fill(cx, ry, cw, 2, rc);
        unsigned int ic = 0xFF0000FF;
        if (row%3==1) ic = 0xFFFF0000;
        if (row%3==2) ic = 0xFF00FF00;
        gpu_rect_fill(cx+cw-2, ry, 2, 2, ic);
        count += 2;
    }
    gpu_sync();
    return count;
}

static int cmp_i64(const void *a, const void *b) {
    int64_t va = *(const int64_t*)a, vb = *(const int64_t*)b;
    return (va > vb) - (va < vb);
}

static int64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000000LL + ts.tv_nsec;
}

typedef int (*scene_fn)(void);

static void run_scene(const char *name, scene_fn fn) {
    for (int i = 0; i < WARMUP_FRAMES; i++) fn();

    int64_t samples[TIMED_FRAMES];
    int64_t total_draws = 0;
    for (int i = 0; i < TIMED_FRAMES; i++) {
        int64_t t0 = now_ns();
        int draws = fn();
        int64_t t1 = now_ns();
        samples[i] = t1 - t0;
        total_draws += draws;
    }
    qsort(samples, TIMED_FRAMES, sizeof(int64_t), cmp_i64);
    int64_t p50_ns = samples[TIMED_FRAMES/2];
    int64_t p95_ns = samples[TIMED_FRAMES-1];
    int64_t avg_draws = total_draws / TIMED_FRAMES;
    int64_t pps = 0, dps = 0;
    if (p50_ns > 0) {
        pps = (int64_t)PIXELS * 1000000000LL / p50_ns;
        dps = avg_draws * 1000000000LL / p50_ns;
    }
    printf("SCENE_RESULT scene=%s backend=c_cuda_gpu frame_count=%d "
           "p50_ms=%lld p95_ms=%lld pixels_per_sec=%lld draws_per_sec=%lld "
           "p50_ns=%lld mode=full\n",
           name, TIMED_FRAMES,
           (long long)(p50_ns/1000000), (long long)(p95_ns/1000000),
           (long long)pps, (long long)dps, (long long)p50_ns);
}

int main(void) {
    printf("========================================\n");
    printf("2D GPU Benchmark — C + CUDA PTX Kernels\n");
    printf("========================================\n\n");

    void *lib = dlopen("libcuda.so.1", RTLD_LAZY);
    if (!lib) lib = dlopen("libcuda.so", RTLD_LAZY);
    if (!lib) { fprintf(stderr, "FAIL: libcuda.so\n"); return 1; }

    cuInit_t p_init = (cuInit_t)dlsym(lib, "cuInit");
    cuDeviceGet_t p_dev_get = (cuDeviceGet_t)dlsym(lib, "cuDeviceGet");
    cuDeviceGetName_t p_dev_name = (cuDeviceGetName_t)dlsym(lib, "cuDeviceGetName");
    cuCtxCreate_t p_ctx_create = (cuCtxCreate_t)dlsym(lib, "cuCtxCreate_v2");
    p_ctx_sync = (cuCtxSynchronize_t)dlsym(lib, "cuCtxSynchronize");
    cuMemAlloc_t p_mem_alloc = (cuMemAlloc_t)dlsym(lib, "cuMemAlloc_v2");
    cuModuleLoadData_t p_mod_load = (cuModuleLoadData_t)dlsym(lib, "cuModuleLoadData");
    cuModuleGetFunction_t p_get_fn = (cuModuleGetFunction_t)dlsym(lib, "cuModuleGetFunction");
    p_launch = (cuLaunchKernel_t)dlsym(lib, "cuLaunchKernel");

    if (!p_init || !p_launch) { fprintf(stderr, "FAIL: symbols\n"); return 1; }

    CUresult r = p_init(0);
    if (r) { fprintf(stderr, "FAIL: cuInit=%d\n", r); return 1; }

    int dev = 0;
    p_dev_get(&dev, 0);
    char devname[256] = "unknown";
    if (p_dev_name) p_dev_name(devname, 256, dev);
    printf("Device: %s\n", devname);

    CUcontext ctx;
    r = p_ctx_create(&ctx, 0, dev);
    if (r) { fprintf(stderr, "FAIL: cuCtxCreate=%d\n", r); return 1; }

    r = p_mem_alloc(&d_fb, FB_BYTES);
    if (r) { fprintf(stderr, "FAIL: cuMemAlloc=%d\n", r); return 1; }

    CUmodule mod;
    r = p_mod_load(&mod, ptx_source);
    if (r) { fprintf(stderr, "FAIL: cuModuleLoadData=%d\n", r); return 1; }

    r = p_get_fn(&f_clear, mod, "kernel_clear");
    if (r) { fprintf(stderr, "FAIL: get kernel_clear=%d\n", r); return 1; }
    r = p_get_fn(&f_rect, mod, "kernel_draw_rect_filled");
    if (r) { fprintf(stderr, "FAIL: get kernel_draw_rect_filled=%d\n", r); return 1; }

    printf("Framebuffer: %dx%d (%d bytes)\n", FRAME_W, FRAME_H, FB_BYTES);
    printf("Warmup: %d frames, Timed: %d frames\n\n", WARMUP_FRAMES, TIMED_FRAMES);

    run_scene("fill_1080p", scene_fill);
    run_scene("blit_tiles", scene_blit);
    run_scene("clipped_scroll", scene_scroll);

    printf("\n========================================\n");

    cuMemFree_t p_free = (cuMemFree_t)dlsym(lib, "cuMemFree_v2");
    if (p_free) p_free(d_fb);
    dlclose(lib);
    return 0;
}
