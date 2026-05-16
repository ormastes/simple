/* POSIX clock_gettime requires _POSIX_C_SOURCE >= 199309L */
#define _POSIX_C_SOURCE 199309L

/*
 * test/perf/graphics_2d/c_reference/bench_2d.c
 *
 * C reference benchmark for the C vs Simple 2D CPU scalar comparison.
 * Canonical scene definitions: test/perf/graphics_2d/scene_format.spl
 * Any change to a scene there MUST be mirrored here.
 *
 * Pixel format: RGBA8888, byte order R,G,B,A per pixel (row-major).
 * Uses raw memset/memcpy paths — no GPU, no library.
 *
 * Output: one SCENE_RESULT line per scene, same format as simple_runner.spl
 *   SCENE_RESULT scene=<name> backend=c_cpu_scalar frame_count=<n>
 *     p50_ms=<ms> p95_ms=<ms> pixels_per_sec=<n> draws_per_sec=<n>
 *     rss_kb=<n> pixel_hash=<h> p50_ns=<ns> mode=full
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define FRAME_W       1920
#define FRAME_H       1080
#define BYTES_PER_PX  4
#define STRIDE        (FRAME_W * BYTES_PER_PX)
#define FB_SIZE       (FRAME_W * FRAME_H * BYTES_PER_PX)
#define SPRITE_W      64
#define SPRITE_H      64
#define WARMUP_FRAMES 10
#define TIMED_FRAMES  100

#define COLOR_BLACK  ((int64_t)0xFF000000LL)
#define COLOR_WHITE  ((int64_t)0xFFFFFFFFLL)
#define COLOR_GRAY   ((int64_t)0xFF808080LL)

static inline uint8_t c_r(int64_t c) { return (uint8_t)(c & 0xFF); }
static inline uint8_t c_g(int64_t c) { return (uint8_t)((c >> 8)  & 0xFF); }
static inline uint8_t c_b(int64_t c) { return (uint8_t)((c >> 16) & 0xFF); }
static inline uint8_t c_a(int64_t c) { return (uint8_t)((c >> 24) & 0xFF); }

/* ── Clip rect ────────────────────────────────────────────────────────────── */

typedef struct { int active, x, y, x2, y2; } ClipRect;
static ClipRect clip_none(void) { ClipRect c = {0,0,0,0,0}; return c; }

/* ── Sprite (must match sprite_pixel in simple_runner.spl) ───────────────── */

static int64_t sprite_pixel(int id) {
    switch (id & 3) {
        case 0: return (int64_t)0xFF0000FFLL;
        case 1: return (int64_t)0xFF00FF00LL;
        case 2: return (int64_t)0xFFFF0000LL;
        default:return (int64_t)0xFF00FFFFLL;
    }
}

/* ── Draw ops ─────────────────────────────────────────────────────────────── */

static void do_clear(uint8_t *fb, int64_t color) {
    uint8_t r=c_r(color), g=c_g(color), b=c_b(color), a=c_a(color);
    if (r==g && g==b && b==a) { memset(fb, r, FB_SIZE); return; }
    for (int i = 0; i < FRAME_W*FRAME_H; i++) {
        int off = i*BYTES_PER_PX;
        fb[off]=r; fb[off+1]=g; fb[off+2]=b; fb[off+3]=a;
    }
}

static void do_rect(uint8_t *fb, ClipRect cr, int bx, int by, int bw, int bh, int64_t color) {
    uint8_t r=c_r(color), g=c_g(color), b=c_b(color), a=c_a(color);
    int x0=bx, y0=by, x1=bx+bw, y1=by+bh;
    if (cr.active) {
        if (x0<cr.x) x0=cr.x; if (y0<cr.y) y0=cr.y;
        if (x1>cr.x2) x1=cr.x2; if (y1>cr.y2) y1=cr.y2;
    }
    if (x0<0) x0=0; if (y0<0) y0=0;
    if (x1>FRAME_W) x1=FRAME_W; if (y1>FRAME_H) y1=FRAME_H;
    if (x0>=x1 || y0>=y1) return;
    int row_bytes = (x1-x0)*BYTES_PER_PX;
    for (int row=y0; row<y1; row++) {
        uint8_t *dst = fb + row*STRIDE + x0*BYTES_PER_PX;
        if (r==g && g==b && b==a) { memset(dst, r, row_bytes); continue; }
        for (int col=x0; col<x1; col++) {
            uint8_t *p = fb + row*STRIDE + col*BYTES_PER_PX;
            p[0]=r; p[1]=g; p[2]=b; p[3]=a;
        }
    }
}

static void do_blit(uint8_t *fb, ClipRect cr, int src_id, int dst_x, int dst_y) {
    int64_t pix = sprite_pixel(src_id);
    uint8_t r=c_r(pix), g=c_g(pix), b=c_b(pix), a=c_a(pix);
    for (int sx=0; sx<SPRITE_W; sx++) {
        for (int sy=0; sy<SPRITE_H; sy++) {
            int dx=dst_x+sx, dy=dst_y+sy;
            if (cr.active && (dx<cr.x||dx>=cr.x2||dy<cr.y||dy>=cr.y2)) continue;
            if (dx<0||dx>=FRAME_W||dy<0||dy>=FRAME_H) continue;
            uint8_t *p = fb + dy*STRIDE + dx*BYTES_PER_PX;
            p[0]=r; p[1]=g; p[2]=b; p[3]=a;
        }
    }
}

/* ── Scene: fill_1080p (must match run_fill in simple_runner.spl) ─────────── */
/* NOTE: C uses full 1920x1080 coords; Simple smoke mode scales down.          */
/* For hash comparison, both must run in full mode (1920x1080).                */

static int scene_fill(uint8_t *fb) {
    static int64_t colors[5] = {
        (int64_t)0xFF0000FFLL, (int64_t)0xFF00FF00LL, (int64_t)0xFFFF0000LL,
        (int64_t)0xFF808080LL, (int64_t)0xFF00FFFFLL,
    };
    ClipRect cr = clip_none();
    do_clear(fb, COLOR_BLACK);
    for (int i=0; i<100; i++) {
        int col = (i*37)%5;
        int rx = (i*19)%(FRAME_W-1); if (rx<0) rx=0;
        int ry = (i*11)%(FRAME_H-1); if (ry<0) ry=0;
        int rw = 1+(i*7)%FRAME_W;
        int rh = 1+(i*13)%FRAME_H;
        do_rect(fb, cr, rx, ry, rw, rh, colors[col]);
    }
    return 101;
}

/* ── Scene: blit_tiles (must match run_blit) ─────────────────────────────── */

static int scene_blit(uint8_t *fb) {
    ClipRect cr = clip_none();
    do_clear(fb, COLOR_BLACK);
    int count = 1;
    for (int ty=0; ty<FRAME_H; ty+=SPRITE_H)
        for (int tx=0; tx<FRAME_W; tx+=SPRITE_W) {
            do_blit(fb, cr, ((tx/SPRITE_W)+(ty/SPRITE_H))%4, tx, ty);
            count++;
        }
    return count;
}

/* ── Scene: clipped_scroll (must match run_scroll) ───────────────────────── */

static int scene_scroll(uint8_t *fb) {
    int cx=FRAME_W/8, cy=FRAME_H/8;
    int cw=FRAME_W-cx*2, ch=FRAME_H-cy*2;
    ClipRect cr = {1, cx, cy, cx+cw, cy+ch};
    static int64_t row_colors[2] = {(int64_t)0xFFFFFFFFLL, (int64_t)0xFF000000LL};
    static int64_t ind_colors[3] = {
        (int64_t)0xFF0000FFLL, (int64_t)0xFFFF0000LL, (int64_t)0xFF00FF00LL};
    int scroll_offset=1, row_h=2, n_rows=4;
    do_clear(fb, COLOR_GRAY);
    int count=2;
    for (int row=0; row<n_rows; row++) {
        int ry = cy + row*(row_h+1) - scroll_offset;
        do_rect(fb, cr, cx, ry, cw, row_h, row_colors[row%2]);
        do_rect(fb, cr, cx+cw-2, ry, 2, row_h, ind_colors[row%3]);
        count+=2;
    }
    return count+1;
}

/* ── Timing ───────────────────────────────────────────────────────────────── */

static int64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec*1000000000LL + ts.tv_nsec;
}

static int cmp_i64(const void *a, const void *b) {
    int64_t x=*(const int64_t*)a, y=*(const int64_t*)b;
    return (x>y)-(x<y);
}

static int64_t percentile(int64_t *sorted, int n, int num, int den) {
    if (!n) return 0;
    int idx=(int)((int64_t)n*num/den);
    if (idx>=n) idx=n-1;
    return sorted[idx];
}

/* ── RSS ──────────────────────────────────────────────────────────────────── */

static int64_t read_rss_kb(void) {
    FILE *f=fopen("/proc/self/status","r");
    if (!f) return 0;
    char line[256]; int64_t kb=0;
    while (fgets(line,sizeof(line),f))
        if (!strncmp(line,"VmRSS:",6)) { sscanf(line+6," %lld",(long long*)&kb); break; }
    fclose(f);
    return kb;
}

/* ── FNV-1a 64-bit (must match fnv1a_fb in simple_runner.spl) ────────────── */

static int64_t fnv1a_framebuffer(const uint8_t *fb) {
    uint64_t h=14695981039346656037ULL;
    int len=FRAME_W*FRAME_H*BYTES_PER_PX;
    for (int i=0; i<len; i++) { h^=(uint64_t)fb[i]; h*=1099511628211ULL; }
    return (int64_t)h;
}

/* ── Run one scene ────────────────────────────────────────────────────────── */

typedef int (*SceneFn)(uint8_t *);

static void run_scene(const char *name, SceneFn fn) {
    uint8_t *fb = malloc(FB_SIZE);
    if (!fb) { fprintf(stderr,"OOM\n"); exit(1); }
    for (int i=0; i<WARMUP_FRAMES; i++) fn(fb);
    int64_t samples[TIMED_FRAMES]; int64_t total_draws=0;
    for (int f=0; f<TIMED_FRAMES; f++) {
        int64_t t0=now_ns();
        int draws=fn(fb);
        int64_t t1=now_ns();
        samples[f]=t1-t0; total_draws+=draws;
    }
    int64_t sorted[TIMED_FRAMES];
    memcpy(sorted,samples,sizeof(samples));
    qsort(sorted,TIMED_FRAMES,sizeof(int64_t),cmp_i64);
    int64_t p50_ns=percentile(sorted,TIMED_FRAMES,50,100);
    int64_t p95_ns=percentile(sorted,TIMED_FRAMES,95,100);
    int64_t ppf=(int64_t)FRAME_W*FRAME_H;
    int64_t pps=p50_ns>0?(ppf*1000000000LL)/p50_ns:0;
    int64_t avg_draws=total_draws/TIMED_FRAMES;
    int64_t dps=p50_ns>0?(avg_draws*1000000000LL)/p50_ns:0;
    int64_t rss=read_rss_kb();
    int64_t phash=fnv1a_framebuffer(fb);
    printf("SCENE_RESULT scene=%s backend=c_cpu_scalar frame_count=%d"
           " p50_ms=%lld p95_ms=%lld pixels_per_sec=%lld draws_per_sec=%lld"
           " rss_kb=%lld pixel_hash=%lld p50_ns=%lld mode=full\n",
           name, TIMED_FRAMES,
           (long long)(p50_ns/1000000LL),(long long)(p95_ns/1000000LL),
           (long long)pps,(long long)dps,(long long)rss,(long long)phash,
           (long long)p50_ns);
    free(fb);
}

int main(void) {
    run_scene("fill_1080p",     scene_fill);
    run_scene("blit_tiles",     scene_blit);
    run_scene("clipped_scroll", scene_scroll);
    return 0;
}
