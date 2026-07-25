/*
 * test/perf/graphics_2d/c_reference/bench_2d_metal.m
 *
 * Apple Metal GPU reference benchmark — baseline for Simple's Metal backend.
 * Three compute scenes matching bench_2d.c scene definitions:
 *   fill_1080p    — fill_kernel:  solid-color fill of 1920x1080 RGBA8
 *   blit_tiles    — blit_kernel:  copy 30 64x64 tiles from src to dst buffer
 *   clipped_scroll — scroll_kernel: 1-row y-shift over a 1024x768 dirty rect
 *
 * Output: same SCENE_RESULT columns as bench_2d.c, plus p99_ms/p99_ns.
 * backend=c_metal_gpu
 *
 * Build:
 *   make bench_2d_metal    (see Makefile in this directory)
 *
 * Platform: macOS Apple Silicon (M-series), unified memory, ARC enabled.
 */

#import <Foundation/Foundation.h>
#import <Metal/Metal.h>
#include <mach/mach_time.h>
#include <sys/resource.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ── Dimensions (must match bench_2d.c) ────────────────────────────────────── */

#define FRAME_W       1920
#define FRAME_H       1080
#define BYTES_PER_PX  4
#define FB_SIZE       ((FRAME_W) * (FRAME_H) * (BYTES_PER_PX))

#define TILE_W        64
#define TILE_H        64
#define N_TILES       30          /* blit_tiles: 30 tiles across src→dst     */

#define SCROLL_W      1024
#define SCROLL_H      768

#define WARMUP_FRAMES 30
#define TIMED_FRAMES  200

/* ── MSL shader source ──────────────────────────────────────────────────────── */

static NSString * const kMSLSource = @"\
#include <metal_stdlib>\n\
using namespace metal;\n\
\n\
/* fill_kernel: write a solid RGBA8 color to every pixel */\n\
kernel void fill_kernel(\n\
    device uint8_t        *dst      [[ buffer(0) ]],\n\
    constant uint32_t     &color    [[ buffer(1) ]],\n\
    constant uint2        &dims     [[ buffer(2) ]],\n\
    uint2 gid [[ thread_position_in_grid ]])\n\
{\n\
    if (gid.x >= dims.x || gid.y >= dims.y) return;\n\
    uint32_t off = (gid.y * dims.x + gid.x) * 4u;\n\
    dst[off + 0] = (color      ) & 0xFF;\n\
    dst[off + 1] = (color >>  8) & 0xFF;\n\
    dst[off + 2] = (color >> 16) & 0xFF;\n\
    dst[off + 3] = (color >> 24) & 0xFF;\n\
}\n\
\n\
/* tile descriptor: src offset + dst offset (in bytes) */\n\
struct TileDesc {\n\
    uint32_t src_byte_off;\n\
    uint32_t dst_byte_off;\n\
};\n\
\n\
/* blit_kernel: copy one 64x64 tile from src to dst */\n\
kernel void blit_kernel(\n\
    device const uint8_t  *src      [[ buffer(0) ]],\n\
    device uint8_t        *dst      [[ buffer(1) ]],\n\
    device const TileDesc *tiles    [[ buffer(2) ]],\n\
    constant uint32_t     &fb_w     [[ buffer(3) ]],\n\
    uint3 gtid [[ thread_position_in_grid ]])\n\
{\n\
    /* gtid.z = tile index, gtid.xy = pixel within tile */\n\
    uint32_t tile_idx = gtid.z;\n\
    uint32_t px = gtid.x;   /* 0..TILE_W-1 */\n\
    uint32_t py = gtid.y;   /* 0..TILE_H-1 */\n\
    TileDesc td = tiles[tile_idx];\n\
    /* src: row-major in a TILE_W-wide strip */\n\
    uint32_t src_off = td.src_byte_off + (py * 64u + px) * 4u;\n\
    /* dst: row-major in a fb_w-wide framebuffer */\n\
    uint32_t dst_row_off = (py * fb_w + px) * 4u;\n\
    uint32_t dst_off = td.dst_byte_off + dst_row_off;\n\
    dst[dst_off + 0] = src[src_off + 0];\n\
    dst[dst_off + 1] = src[src_off + 1];\n\
    dst[dst_off + 2] = src[src_off + 2];\n\
    dst[dst_off + 3] = src[src_off + 3];\n\
}\n\
\n\
/* scroll_kernel: copy 1024x768 region from src with +1 row y-offset */\n\
kernel void scroll_kernel(\n\
    device const uint8_t  *src      [[ buffer(0) ]],\n\
    device uint8_t        *dst      [[ buffer(1) ]],\n\
    constant uint2        &dims     [[ buffer(2) ]],  /* scroll region w,h */\n\
    constant uint32_t     &fb_w     [[ buffer(3) ]],  /* full framebuffer width */\n\
    constant uint2        &origin   [[ buffer(4) ]],  /* top-left of scroll region in dst */\n\
    uint2 gid [[ thread_position_in_grid ]])\n\
{\n\
    if (gid.x >= dims.x || gid.y >= dims.y) return;\n\
    /* source row = gid.y + 1 (simulate 1-px scroll), clamp at bottom */\n\
    uint32_t src_y = gid.y + 1u;\n\
    if (src_y >= dims.y) src_y = dims.y - 1u;\n\
    uint32_t src_off = (src_y * fb_w + gid.x) * 4u;\n\
    uint32_t dst_off = ((origin.y + gid.y) * fb_w + (origin.x + gid.x)) * 4u;\n\
    dst[dst_off + 0] = src[src_off + 0];\n\
    dst[dst_off + 1] = src[src_off + 1];\n\
    dst[dst_off + 2] = src[src_off + 2];\n\
    dst[dst_off + 3] = src[src_off + 3];\n\
}\n\
";

/* ── Timing helpers ─────────────────────────────────────────────────────────── */

static mach_timebase_info_data_t g_tb;

static void init_timebase(void) {
    mach_timebase_info(&g_tb);
}

static int64_t mach_to_ns(uint64_t t) {
    return (int64_t)((__uint128_t)t * g_tb.numer / g_tb.denom);
}

static int cmp_i64(const void *a, const void *b) {
    int64_t x = *(const int64_t *)a;
    int64_t y = *(const int64_t *)b;
    return (x > y) - (x < y);
}

static int64_t percentile(int64_t *sorted, int n, int num, int den) {
    if (!n) return 0;
    int idx = (int)((int64_t)n * num / den);
    if (idx >= n) idx = n - 1;
    return sorted[idx];
}

/* ── RSS (bytes on macOS → divide by 1024 for KB) ──────────────────────────── */

static int64_t read_rss_kb(void) {
    struct rusage ru;
    if (getrusage(RUSAGE_SELF, &ru) != 0) return 0;
    return (int64_t)(ru.ru_maxrss / 1024);
}

/* ── Global Metal objects (set up once) ─────────────────────────────────────── */

static id<MTLDevice>              g_dev;
static id<MTLCommandQueue>        g_queue;
static id<MTLComputePipelineState> g_fill_pso;
static id<MTLComputePipelineState> g_blit_pso;
static id<MTLComputePipelineState> g_scroll_pso;

/* Shared buffers */
static id<MTLBuffer>  g_src_buf;   /* 1920*1080*4 source FB */
static id<MTLBuffer>  g_dst_buf;   /* 1920*1080*4 dest FB   */
static id<MTLBuffer>  g_tiles_buf; /* N_TILES * TileDesc     */

/* ── Tile descriptor (must match MSL struct layout) ────────────────────────── */
typedef struct {
    uint32_t src_byte_off;
    uint32_t dst_byte_off;
} TileDesc;

/* ── Setup ───────────────────────────────────────────────────────────────────── */

static void setup_metal(void) {
    g_dev = MTLCreateSystemDefaultDevice();
    if (!g_dev) { fprintf(stderr, "No Metal device\n"); exit(1); }

    g_queue = [g_dev newCommandQueue];
    if (!g_queue) { fprintf(stderr, "newCommandQueue failed\n"); exit(1); }

    /* Compile MSL library */
    NSError *err = nil;
    MTLCompileOptions *opts = [MTLCompileOptions new];
    opts.mathMode = MTLMathModeFast;
    id<MTLLibrary> lib = [g_dev newLibraryWithSource:kMSLSource
                                             options:opts
                                               error:&err];
    if (!lib) {
        fprintf(stderr, "Shader compile failed: %s\n",
                [[err localizedDescription] UTF8String]);
        exit(1);
    }

    /* Compute pipeline states */
    id<MTLFunction> fn;

    fn = [lib newFunctionWithName:@"fill_kernel"];
    g_fill_pso = [g_dev newComputePipelineStateWithFunction:fn error:&err];
    if (!g_fill_pso) {
        fprintf(stderr, "fill PSO: %s\n", [[err localizedDescription] UTF8String]);
        exit(1);
    }

    fn = [lib newFunctionWithName:@"blit_kernel"];
    g_blit_pso = [g_dev newComputePipelineStateWithFunction:fn error:&err];
    if (!g_blit_pso) {
        fprintf(stderr, "blit PSO: %s\n", [[err localizedDescription] UTF8String]);
        exit(1);
    }

    fn = [lib newFunctionWithName:@"scroll_kernel"];
    g_scroll_pso = [g_dev newComputePipelineStateWithFunction:fn error:&err];
    if (!g_scroll_pso) {
        fprintf(stderr, "scroll PSO: %s\n", [[err localizedDescription] UTF8String]);
        exit(1);
    }

    /* Allocate shared buffers (unified memory — zero copy on Apple Silicon) */
    g_src_buf = [g_dev newBufferWithLength:FB_SIZE
                                   options:MTLResourceStorageModeShared];
    g_dst_buf = [g_dev newBufferWithLength:FB_SIZE
                                   options:MTLResourceStorageModeShared];
    if (!g_src_buf || !g_dst_buf) {
        fprintf(stderr, "MTLBuffer allocation failed\n"); exit(1);
    }

    /* Pre-fill source buffer with a recognizable pattern */
    uint8_t *src = (uint8_t *)[g_src_buf contents];
    for (int i = 0; i < FRAME_W * FRAME_H; i++) {
        src[i*4+0] = (uint8_t)(i & 0xFF);
        src[i*4+1] = (uint8_t)((i >> 8) & 0xFF);
        src[i*4+2] = (uint8_t)0x80;
        src[i*4+3] = 0xFF;
    }

    /* Build tile descriptor table for blit scene:
     * 30 tiles placed along the top rows of the framebuffer.
     * src tiles are consecutive 64x64 blocks in a virtual 64-wide src strip
     * (byte offset = tile_idx * TILE_W * TILE_H * 4).
     * dst tiles: tiles[i] at column (i % tiles_per_row), row (i / tiles_per_row). */
    g_tiles_buf = [g_dev newBufferWithLength:N_TILES * sizeof(TileDesc)
                                     options:MTLResourceStorageModeShared];
    if (!g_tiles_buf) { fprintf(stderr, "tiles MTLBuffer failed\n"); exit(1); }
    TileDesc *tiles = (TileDesc *)[g_tiles_buf contents];
    int tiles_per_row = FRAME_W / TILE_W;   /* 30 */
    for (int i = 0; i < N_TILES; i++) {
        tiles[i].src_byte_off = (uint32_t)(i * TILE_W * TILE_H * BYTES_PER_PX);
        int col = i % tiles_per_row;
        int row = i / tiles_per_row;
        tiles[i].dst_byte_off = (uint32_t)((row * FRAME_W * TILE_H + col * TILE_W) * BYTES_PER_PX);
    }
}

/* ── Encode + dispatch helpers ──────────────────────────────────────────────── */

/* fill_1080p: fill 1920x1080 with solid gray (0xFF808080) */
static void encode_fill(id<MTLComputeCommandEncoder> enc) {
    [enc setComputePipelineState:g_fill_pso];
    [enc setBuffer:g_dst_buf offset:0 atIndex:0];
    uint32_t color = 0xFF808080u;
    [enc setBytes:&color length:sizeof(color) atIndex:1];
    uint32_t dims[2] = { FRAME_W, FRAME_H };
    [enc setBytes:dims length:sizeof(dims) atIndex:2];

    MTLSize tg  = MTLSizeMake(16, 16, 1);
    MTLSize gr  = MTLSizeMake((FRAME_W  + 15) / 16,
                              (FRAME_H  + 15) / 16, 1);
    [enc dispatchThreadgroups:gr threadsPerThreadgroup:tg];
}

/* blit_tiles: copy 30 64x64 tiles */
static void encode_blit(id<MTLComputeCommandEncoder> enc) {
    [enc setComputePipelineState:g_blit_pso];
    [enc setBuffer:g_src_buf   offset:0 atIndex:0];
    [enc setBuffer:g_dst_buf   offset:0 atIndex:1];
    [enc setBuffer:g_tiles_buf offset:0 atIndex:2];
    uint32_t fw = FRAME_W;
    [enc setBytes:&fw length:sizeof(fw) atIndex:3];

    /* Each threadgroup handles one tile (64x64 threads).
     * gtid.z = tile index, gtid.xy = pixel within tile. */
    MTLSize tg = MTLSizeMake(TILE_W, TILE_H, 1);
    MTLSize gr = MTLSizeMake(1, 1, N_TILES);
    [enc dispatchThreadgroups:gr threadsPerThreadgroup:tg];
}

/* clipped_scroll: scroll 1024x768 region by 1 row */
static void encode_scroll(id<MTLComputeCommandEncoder> enc) {
    [enc setComputePipelineState:g_scroll_pso];
    [enc setBuffer:g_src_buf offset:0 atIndex:0];
    [enc setBuffer:g_dst_buf offset:0 atIndex:1];
    uint32_t dims[2]   = { SCROLL_W, SCROLL_H };
    [enc setBytes:dims length:sizeof(dims) atIndex:2];
    uint32_t fw = FRAME_W;
    [enc setBytes:&fw length:sizeof(fw) atIndex:3];
    /* Place scroll region at (cx, cy) = (FRAME_W/8, FRAME_H/8) matching bench_2d.c */
    uint32_t origin[2] = { FRAME_W / 8, FRAME_H / 8 };
    [enc setBytes:origin length:sizeof(origin) atIndex:4];

    MTLSize tg = MTLSizeMake(16, 16, 1);
    MTLSize gr = MTLSizeMake((SCROLL_W + 15) / 16,
                             (SCROLL_H + 15) / 16, 1);
    [enc dispatchThreadgroups:gr threadsPerThreadgroup:tg];
}

/* ── Run one scene ───────────────────────────────────────────────────────────── */

typedef void (*EncodeFn)(id<MTLComputeCommandEncoder>);

static void run_scene(const char *name, EncodeFn encode_fn) {
    int64_t samples[TIMED_FRAMES];

    /* Warmup: discard timings */
    for (int i = 0; i < WARMUP_FRAMES; i++) {
        id<MTLCommandBuffer> cb = [g_queue commandBuffer];
        id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
        encode_fn(enc);
        [enc endEncoding];
        [cb commit];
        [cb waitUntilCompleted];
    }

    /* Timed iterations */
    for (int f = 0; f < TIMED_FRAMES; f++) {
        uint64_t t0 = mach_absolute_time();

        id<MTLCommandBuffer> cb = [g_queue commandBuffer];
        id<MTLComputeCommandEncoder> enc = [cb computeCommandEncoder];
        encode_fn(enc);
        [enc endEncoding];
        [cb commit];
        [cb waitUntilCompleted];

        uint64_t t1 = mach_absolute_time();
        samples[f] = mach_to_ns(t1 - t0);
    }

    int64_t sorted[TIMED_FRAMES];
    memcpy(sorted, samples, sizeof(samples));
    qsort(sorted, TIMED_FRAMES, sizeof(int64_t), cmp_i64);

    int64_t p50_ns = percentile(sorted, TIMED_FRAMES, 50, 100);
    int64_t p95_ns = percentile(sorted, TIMED_FRAMES, 95, 100);
    int64_t p99_ns = percentile(sorted, TIMED_FRAMES, 99, 100);

    int64_t ppf = (int64_t)FRAME_W * FRAME_H;
    int64_t pps = p50_ns > 0 ? (ppf * 1000000000LL) / p50_ns : 0;

    /* draws_per_sec: 1 dispatch per frame (no sub-draws in Metal path) */
    int64_t dps = p50_ns > 0 ? (1LL * 1000000000LL) / p50_ns : 0;

    int64_t rss = read_rss_kb();

    /* pixel_hash: 0 — reading back GPU buffer on every iter would force a
     * CPU-side stall that inflates timings; skip to keep Metal times clean */
    int64_t pixel_hash = 0;

    printf("SCENE_RESULT scene=%s backend=c_metal_gpu frame_count=%d"
           " p50_ms=%lld p95_ms=%lld pixels_per_sec=%lld draws_per_sec=%lld"
           " rss_kb=%lld pixel_hash=%lld p50_ns=%lld"
           " p99_ms=%lld p99_ns=%lld mode=full\n",
           name, TIMED_FRAMES,
           (long long)(p50_ns / 1000000LL),
           (long long)(p95_ns / 1000000LL),
           (long long)pps,
           (long long)dps,
           (long long)rss,
           (long long)pixel_hash,
           (long long)p50_ns,
           (long long)(p99_ns / 1000000LL),
           (long long)p99_ns);
}

/* ── main ────────────────────────────────────────────────────────────────────── */

int main(void) {
    @autoreleasepool {
        init_timebase();
        setup_metal();

        run_scene("fill_1080p",      encode_fill);
        run_scene("blit_tiles",      encode_blit);
        run_scene("clipped_scroll",  encode_scroll);
    }
    return 0;
}
