/* bench_2d_memset.c — C CUDA benchmark using cuMemsetD32 (matches Simple approach)
 *
 * Same row-by-row rect fill via cuMemsetD32 as bench_2d_gpu.spl.
 * Build: gcc -O2 -o bench_2d_memset bench_2d_memset.c -ldl -lrt
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dlfcn.h>
#include <time.h>
#include <stdint.h>

typedef int CUresult;
typedef void* CUcontext;
typedef unsigned long long CUdeviceptr;

typedef CUresult (*cuInit_t)(unsigned int);
typedef CUresult (*cuDeviceGet_t)(int*, int);
typedef CUresult (*cuCtxCreate_t)(CUcontext*, unsigned int, int);
typedef CUresult (*cuCtxSynchronize_t)(void);
typedef CUresult (*cuMemAlloc_t)(CUdeviceptr*, size_t);
typedef CUresult (*cuMemFree_t)(CUdeviceptr);
typedef CUresult (*cuMemsetD32_t)(CUdeviceptr, unsigned int, size_t);

#define FRAME_W 640
#define FRAME_H 480
#define PIXELS  (FRAME_W * FRAME_H)
#define FB_BYTES (PIXELS * 4)
#define WARMUP_FRAMES 3
#define TIMED_FRAMES 20

static cuMemsetD32_t    p_memset32;
static cuCtxSynchronize_t p_ctx_sync;
static CUdeviceptr      d_fb;

static void gpu_clear(unsigned int color) {
    p_memset32(d_fb, color, PIXELS);
}

static void gpu_rect_fill(int x, int y, int w, int h, unsigned int color) {
    for (int row = 0; row < h; row++) {
        int ry = y + row;
        if (ry < 0 || ry >= FRAME_H) continue;
        int rx = x, rw = w;
        if (rx < 0) { rw += rx; rx = 0; }
        if (rx + rw > FRAME_W) rw = FRAME_W - rx;
        if (rw <= 0) continue;
        size_t offset = ((size_t)ry * FRAME_W + rx) * 4;
        p_memset32(d_fb + offset, color, (size_t)rw);
    }
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
    for (int i = 0; i < 20; i++) {
        int rx = (i * 19) % (FRAME_W - 1); if (rx < 0) rx = 0;
        int ry = (i * 11) % (FRAME_H - 1); if (ry < 0) ry = 0;
        int rw = 1 + (i * 7) % 200;
        int rh = 1 + (i * 13) % 100;
        gpu_rect_fill(rx, ry, rw, rh, fill_color((i * 37) % 5));
    }
    gpu_sync();
    return 21;
}

static int scene_blit(void) {
    gpu_clear(0xFF000000);
    int count = 1;
    for (int ty = 0; ty < FRAME_H; ty += 64)
        for (int tx = 0; tx < FRAME_W; tx += 64) {
            gpu_rect_fill(tx, ty, 64, 64, fill_color(((tx/64)+(ty/64))%4));
            count++;
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

static int64_t now_us(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000LL + ts.tv_nsec / 1000;
}

typedef int (*scene_fn)(void);

static void run_scene(const char *name, scene_fn fn) {
    for (int i = 0; i < WARMUP_FRAMES; i++) fn();
    int64_t samples[TIMED_FRAMES];
    int64_t total_draws = 0;
    for (int i = 0; i < TIMED_FRAMES; i++) {
        int64_t t0 = now_us();
        int draws = fn();
        int64_t t1 = now_us();
        samples[i] = t1 - t0;
        total_draws += draws;
    }
    qsort(samples, TIMED_FRAMES, sizeof(int64_t), cmp_i64);
    int64_t p50_us = samples[TIMED_FRAMES/2];
    int64_t p95_us = samples[TIMED_FRAMES-1];
    int64_t avg_draws = total_draws / TIMED_FRAMES;
    double p50_ms = p50_us / 1000.0;
    double p95_ms = p95_us / 1000.0;
    int64_t pps = 0, dps = 0;
    if (p50_us > 0) {
        pps = (int64_t)PIXELS * 1000000LL / p50_us;
        dps = avg_draws * 1000000LL / p50_us;
    }
    printf("SCENE_RESULT scene=%s backend=c_cuda_memset frame_count=%d "
           "p50_ms=%.3f p95_ms=%.3f pixels_per_sec=%lld draws_per_sec=%lld mode=full\n",
           name, TIMED_FRAMES, p50_ms, p95_ms, (long long)pps, (long long)dps);
}

int main(void) {
    printf("========================================\n");
    printf("2D GPU Benchmark — C + CUDA (cuMemsetD32)\n");
    printf("========================================\n\n");

    void *lib = dlopen("libcuda.so.1", RTLD_LAZY);
    if (!lib) lib = dlopen("libcuda.so", RTLD_LAZY);
    if (!lib) { fprintf(stderr, "FAIL: Cannot load libcuda.so\n"); return 1; }

    cuInit_t p_init = (cuInit_t)dlsym(lib, "cuInit");
    cuDeviceGet_t p_dev_get = (cuDeviceGet_t)dlsym(lib, "cuDeviceGet");
    cuCtxCreate_t p_ctx_create = (cuCtxCreate_t)dlsym(lib, "cuCtxCreate_v2");
    p_ctx_sync = (cuCtxSynchronize_t)dlsym(lib, "cuCtxSynchronize");
    cuMemAlloc_t p_mem_alloc = (cuMemAlloc_t)dlsym(lib, "cuMemAlloc_v2");
    p_memset32 = (cuMemsetD32_t)dlsym(lib, "cuMemsetD32_v2");

    if (!p_init || !p_memset32) { fprintf(stderr, "FAIL: Missing symbols\n"); return 1; }

    CUresult r = p_init(0);
    if (r) { fprintf(stderr, "FAIL: cuInit=%d\n", r); return 1; }

    int dev = 0;
    r = p_dev_get(&dev, 0);
    if (r) { fprintf(stderr, "FAIL: cuDeviceGet=%d\n", r); return 1; }

    CUcontext ctx;
    r = p_ctx_create(&ctx, 0, dev);
    if (r) { fprintf(stderr, "FAIL: cuCtxCreate=%d\n", r); return 1; }

    r = p_mem_alloc(&d_fb, FB_BYTES);
    if (r) { fprintf(stderr, "FAIL: cuMemAlloc=%d\n", r); return 1; }

    printf("Framebuffer: %dx%d (%d bytes)\n", FRAME_W, FRAME_H, FB_BYTES);
    printf("Warmup: %d frames, Timed: %d frames\n", WARMUP_FRAMES, TIMED_FRAMES);
    printf("Method: cuMemsetD32 (row-by-row rect fill, same as Simple)\n\n");

    run_scene("fill_640x480", scene_fill);
    run_scene("blit_tiles", scene_blit);
    run_scene("clipped_scroll", scene_scroll);

    printf("\n========================================\n");
    cuMemFree_t p_free = (cuMemFree_t)dlsym(lib, "cuMemFree_v2");
    if (p_free) p_free(d_fb);
    dlclose(lib);
    return 0;
}
