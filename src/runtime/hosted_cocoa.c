/*
 * hosted_cocoa.c — Objective-C implementation of the Cocoa hosted-surface SFFI.
 *
 * These symbols back the `extern fn rt_cocoa_*` declarations in
 * `src/os/compositor/hosted_backend_cocoa.spl`. The Simple side treats every
 * handle as an opaque int64_t and every boolean as a C-ABI bool.
 *
 * Two modes:
 *   - Stub mode (non-macOS): every function compiles, exports, and returns a
 *     sentinel failure value.  Keeps Linux / CI linking while we iterate on
 *     the macOS side.
 *   - Real mode (macOS, __APPLE__): NSWindow + NSImageView backed by a
 *     CPU-side ARGB pixel buffer. Metal lands in a later phase.
 *
 * Build:
 *   cc -x objective-c -c -fPIC -O2 hosted_cocoa.c \
 *      -o hosted_cocoa.o -framework Cocoa
 */

#include <stdint.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#define COCOA_INVALID_HANDLE ((int64_t)(-1))

/* -------------------------------------------------------------------------
 * Simple runtime helpers: decode a tagged-text RuntimeValue (int64_t) into
 * a raw byte pointer + length.  Linked against libsimple_native_all.
 * ---------------------------------------------------------------------- */
extern const char *rt_string_data(int64_t rv);
extern int64_t     rt_string_len(int64_t rv);

/* Decode a Simple `text` RuntimeValue into a NUL-terminated C string
 * allocated with malloc.  Caller must free().  Returns strdup("untitled") on
 * any error. */
static char *text_rv_to_cstr(int64_t rv) {
    if (rv == 0) return strdup("untitled");
    int64_t len = rt_string_len(rv);
    if (len <= 0) return strdup("untitled");
    const char *ptr = rt_string_data(rv);
    if (!ptr) return strdup("untitled");
    char *buf = (char *)malloc((size_t)(len + 1));
    if (!buf) return strdup("untitled");
    memcpy(buf, ptr, (size_t)len);
    buf[len] = '\0';
    return buf;
}

/* =========================================================================
 * Non-macOS stub implementations
 * ====================================================================== */
#ifndef __APPLE__

int64_t rt_cocoa_window_new(int64_t w, int64_t h, int64_t title_rv) {
    (void)w; (void)h; (void)title_rv;
    return COCOA_INVALID_HANDLE;
}
bool rt_cocoa_window_resize(int64_t win, int64_t w, int64_t h) {
    (void)win; (void)w; (void)h; return false;
}
bool rt_cocoa_window_close(int64_t win) {
    (void)win; return false;
}
int64_t rt_cocoa_layer_create(int64_t win, int64_t w, int64_t h, int64_t fill_color) {
    (void)win; (void)w; (void)h; (void)fill_color;
    return COCOA_INVALID_HANDLE;
}
bool rt_cocoa_layer_fill_rect(int64_t layer, int64_t x, int64_t y,
                               int64_t w, int64_t h, int64_t color) {
    (void)layer; (void)x; (void)y; (void)w; (void)h; (void)color;
    return false;
}
bool rt_cocoa_layer_present(int64_t win, int64_t layer) {
    (void)win; (void)layer; return false;
}
bool rt_cocoa_layer_free(int64_t layer) {
    (void)layer; return false;
}
int64_t rt_cocoa_layer_read_pixel(int64_t layer, int64_t x, int64_t y) {
    (void)layer; (void)x; (void)y; return 0;
}
bool rt_cocoa_layer_blend_rect(int64_t layer, int64_t x, int64_t y,
                                int64_t w, int64_t h,
                                int64_t color, int64_t alpha) {
    (void)layer; (void)x; (void)y; (void)w; (void)h;
    (void)color; (void)alpha;
    return false;
}
bool rt_cocoa_layer_blur(int64_t layer, int64_t x, int64_t y,
                          int64_t w, int64_t h, int64_t radius) {
    (void)layer; (void)x; (void)y; (void)w; (void)h; (void)radius;
    return false;
}
bool rt_cocoa_layer_gradient_v(int64_t layer, int64_t x, int64_t y,
                                int64_t w, int64_t h,
                                int64_t color_top, int64_t color_bottom) {
    (void)layer; (void)x; (void)y; (void)w; (void)h;
    (void)color_top; (void)color_bottom;
    return false;
}
int64_t rt_cocoa_event_pump(int64_t win) {
    (void)win; return 0;
}

#else /* __APPLE__ */

/* =========================================================================
 * macOS real implementation
 * ====================================================================== */
#import <Cocoa/Cocoa.h>
#include <stdatomic.h>
#include <pthread.h>

/* -------------------------------------------------------------------------
 * Handle table
 * A compact fixed-size table mapping int64_t IDs to void* records.
 * IDs start at 1; 0 and -1 are reserved sentinels.
 * ---------------------------------------------------------------------- */
#define MAX_HANDLES 4096

typedef struct {
    int64_t  id;
    void    *ptr;       /* Window* or Layer* */
    uint8_t  kind;      /* 1 = window, 2 = layer */
} HandleEntry;

static HandleEntry   g_handles[MAX_HANDLES];
static pthread_mutex_t g_mutex = PTHREAD_MUTEX_INITIALIZER;
static _Atomic int64_t g_next_handle = 1;

static int64_t next_handle(void) {
    return atomic_fetch_add_explicit(&g_next_handle, 1, memory_order_relaxed);
}

/* Insert; returns false on table full. */
static bool handle_insert(int64_t id, void *ptr, uint8_t kind) {
    for (int i = 0; i < MAX_HANDLES; i++) {
        if (g_handles[i].id == 0) {
            g_handles[i].id   = id;
            g_handles[i].ptr  = ptr;
            g_handles[i].kind = kind;
            return true;
        }
    }
    return false;
}

/* Lookup without removing. */
static void *handle_get(int64_t id, uint8_t kind) {
    if (id <= 0) return NULL;
    for (int i = 0; i < MAX_HANDLES; i++) {
        if (g_handles[i].id == id && g_handles[i].kind == kind)
            return g_handles[i].ptr;
    }
    return NULL;
}

/* Remove and return the pointer. */
static void *handle_remove(int64_t id, uint8_t kind) {
    for (int i = 0; i < MAX_HANDLES; i++) {
        if (g_handles[i].id == id && g_handles[i].kind == kind) {
            void *p = g_handles[i].ptr;
            g_handles[i].id   = 0;
            g_handles[i].ptr  = NULL;
            g_handles[i].kind = 0;
            return p;
        }
    }
    return NULL;
}

/* -------------------------------------------------------------------------
 * Window record
 * ---------------------------------------------------------------------- */
#define KIND_WINDOW 1
#define KIND_LAYER  2

/* Maximum event queue depth per window. */
#define EVENT_QUEUE_CAP 256

typedef struct {
    int64_t     w, h;
    NSWindow   *ns_window;    /* strong, retained via CFRetain */
    NSImageView *ns_view;     /* strong */
    int64_t     event_queue[EVENT_QUEUE_CAP];
    int         eq_head, eq_tail, eq_count;
} CocoaWindow;

static void wnd_eq_push(CocoaWindow *wnd, int64_t code) {
    if (wnd->eq_count >= EVENT_QUEUE_CAP) return; /* drop oldest */
    wnd->event_queue[wnd->eq_tail] = code;
    wnd->eq_tail = (wnd->eq_tail + 1) % EVENT_QUEUE_CAP;
    wnd->eq_count++;
}

static bool wnd_eq_pop(CocoaWindow *wnd, int64_t *out) {
    if (wnd->eq_count == 0) return false;
    *out = wnd->event_queue[wnd->eq_head];
    wnd->eq_head = (wnd->eq_head + 1) % EVENT_QUEUE_CAP;
    wnd->eq_count--;
    return true;
}

/* -------------------------------------------------------------------------
 * Layer record
 * ---------------------------------------------------------------------- */
typedef struct {
    int64_t   w, h;
    uint32_t *pixels; /* ARGB (0xAARRGGBB) CPU buffer, w*h elements */
} CocoaLayer;

/* -------------------------------------------------------------------------
 * ensure_app: promote the process to a regular GUI app on first call.
 * Must be called from the main thread.
 * ---------------------------------------------------------------------- */
static void ensure_app(void) {
    static bool done = false;
    if (done) return;
    done = true;
    NSApplication *app = [NSApplication sharedApplication];
    [app setActivationPolicy:NSApplicationActivationPolicyRegular];
    [app activateIgnoringOtherApps:YES];
}

/* Helper: is this the main thread? */
static bool is_main_thread(void) {
    return [NSThread isMainThread];
}

/* =========================================================================
 * Window operations
 * ====================================================================== */

int64_t rt_cocoa_window_new(int64_t w, int64_t h, int64_t title_rv) {
    if (w <= 0 || h <= 0) return COCOA_INVALID_HANDLE;
    if (!is_main_thread())  return COCOA_INVALID_HANDLE;

    char *title_cstr = text_rv_to_cstr(title_rv);

    @autoreleasepool {
        ensure_app();

        NSRect frame = NSMakeRect(0, 0, (CGFloat)w, (CGFloat)h);
        NSWindowStyleMask style =
            NSWindowStyleMaskTitled      |
            NSWindowStyleMaskClosable    |
            NSWindowStyleMaskResizable   |
            NSWindowStyleMaskMiniaturizable;

        NSWindow *ns_window = [[NSWindow alloc]
            initWithContentRect:frame
                      styleMask:style
                        backing:NSBackingStoreBuffered
                          defer:NO];

        NSString *ns_title = [NSString stringWithUTF8String:title_cstr];
        [ns_window setTitle:ns_title];
        [ns_window center];

        NSImageView *ns_view = [[NSImageView alloc] initWithFrame:frame];
        [ns_window setContentView:ns_view];
        [ns_window makeKeyAndOrderFront:nil];

        CocoaWindow *wnd = (CocoaWindow *)calloc(1, sizeof(CocoaWindow));
        if (!wnd) {
            free(title_cstr);
            return COCOA_INVALID_HANDLE;
        }
        wnd->w          = w;
        wnd->h          = h;
        wnd->ns_window  = (NSWindow *)CFRetain((__bridge CFTypeRef)ns_window);
        wnd->ns_view    = (NSImageView *)CFRetain((__bridge CFTypeRef)ns_view);
        wnd->eq_head    = 0;
        wnd->eq_tail    = 0;
        wnd->eq_count   = 0;

        int64_t id = next_handle();

        pthread_mutex_lock(&g_mutex);
        bool ok = handle_insert(id, wnd, KIND_WINDOW);
        pthread_mutex_unlock(&g_mutex);

        free(title_cstr);
        if (!ok) {
            CFRelease((__bridge CFTypeRef)wnd->ns_window);
            CFRelease((__bridge CFTypeRef)wnd->ns_view);
            free(wnd);
            return COCOA_INVALID_HANDLE;
        }
        return id;
    }
}

bool rt_cocoa_window_resize(int64_t win, int64_t w, int64_t h) {
    if (w <= 0 || h <= 0)   return false;
    if (!is_main_thread())   return false;

    pthread_mutex_lock(&g_mutex);
    CocoaWindow *wnd = (CocoaWindow *)handle_get(win, KIND_WINDOW);
    pthread_mutex_unlock(&g_mutex);
    if (!wnd) return false;

    @autoreleasepool {
        wnd->w = w;
        wnd->h = h;
        NSSize new_size = NSMakeSize((CGFloat)w, (CGFloat)h);
        [wnd->ns_window setContentSize:new_size];
        NSRect new_frame = NSMakeRect(0, 0, (CGFloat)w, (CGFloat)h);
        [wnd->ns_view setFrame:new_frame];
    }
    return true;
}

bool rt_cocoa_window_close(int64_t win) {
    pthread_mutex_lock(&g_mutex);
    CocoaWindow *wnd = (CocoaWindow *)handle_remove(win, KIND_WINDOW);
    pthread_mutex_unlock(&g_mutex);
    if (!wnd) return false;

    @autoreleasepool {
        [wnd->ns_window orderOut:nil];
    }
    CFRelease((__bridge CFTypeRef)wnd->ns_window);
    CFRelease((__bridge CFTypeRef)wnd->ns_view);
    free(wnd);
    return true;
}

/* =========================================================================
 * Layer operations
 * ====================================================================== */

int64_t rt_cocoa_layer_create(int64_t win, int64_t w, int64_t h, int64_t fill_color) {
    (void)win; /* not bound to a specific window in our model */
    if (w <= 0 || h <= 0) return COCOA_INVALID_HANDLE;

    size_t len = (size_t)(w * h);
    uint32_t *pixels = (uint32_t *)malloc(len * sizeof(uint32_t));
    if (!pixels) return COCOA_INVALID_HANDLE;

    uint32_t c = (uint32_t)fill_color;
    for (size_t i = 0; i < len; i++) pixels[i] = c;

    CocoaLayer *layer = (CocoaLayer *)malloc(sizeof(CocoaLayer));
    if (!layer) { free(pixels); return COCOA_INVALID_HANDLE; }
    layer->w      = w;
    layer->h      = h;
    layer->pixels = pixels;

    int64_t id = next_handle();

    pthread_mutex_lock(&g_mutex);
    bool ok = handle_insert(id, layer, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);

    if (!ok) { free(pixels); free(layer); return COCOA_INVALID_HANDLE; }
    return id;
}

bool rt_cocoa_layer_fill_rect(int64_t layer_id, int64_t x, int64_t y,
                               int64_t w, int64_t h, int64_t color) {
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return false;

    uint32_t c  = (uint32_t)color;
    int64_t lw = l->w, lh = l->h;
    int64_t x0 = x < 0 ? 0 : (x > lw ? lw : x);
    int64_t y0 = y < 0 ? 0 : (y > lh ? lh : y);
    int64_t x1 = (x+w) < 0 ? 0 : ((x+w) > lw ? lw : (x+w));
    int64_t y1 = (y+h) < 0 ? 0 : ((y+h) > lh ? lh : (y+h));

    for (int64_t yy = y0; yy < y1; yy++) {
        uint32_t *row = l->pixels + (size_t)(yy * lw);
        for (int64_t xx = x0; xx < x1; xx++)
            row[xx] = c;
    }
    return true;
}

bool rt_cocoa_layer_present(int64_t win, int64_t layer_id) {
    if (!is_main_thread()) return false;

    pthread_mutex_lock(&g_mutex);
    CocoaLayer  *l   = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    CocoaWindow *wnd = (CocoaWindow *)handle_get(win,      KIND_WINDOW);
    pthread_mutex_unlock(&g_mutex);
    if (!l || !wnd) return false;

    size_t  pw = (size_t)l->w;
    size_t  ph = (size_t)l->h;
    if (pw == 0 || ph == 0) return false;

    @autoreleasepool {
        /* Convert ARGB (0xAARRGGBB) → RGBA bytes for NSBitmapImageRep. */
        size_t  nbytes = pw * ph * 4;
        uint8_t *rgba  = (uint8_t *)malloc(nbytes);
        if (!rgba) return false;

        for (size_t i = 0; i < pw * ph; i++) {
            uint32_t px = l->pixels[i];
            rgba[i*4+0] = (uint8_t)((px >> 16) & 0xff); /* R */
            rgba[i*4+1] = (uint8_t)((px >>  8) & 0xff); /* G */
            rgba[i*4+2] = (uint8_t)( px        & 0xff); /* B */
            rgba[i*4+3] = (uint8_t)((px >> 24) & 0xff); /* A */
        }

        NSBitmapImageRep *bmp = [[NSBitmapImageRep alloc]
            initWithBitmapDataPlanes:NULL
                          pixelsWide:(NSInteger)pw
                          pixelsHigh:(NSInteger)ph
                       bitsPerSample:8
                     samplesPerPixel:4
                            hasAlpha:YES
                            isPlanar:NO
                      colorSpaceName:NSDeviceRGBColorSpace
                         bytesPerRow:(NSInteger)(pw * 4)
                        bitsPerPixel:32];

        if (bmp) {
            memcpy([bmp bitmapData], rgba, nbytes);
            NSImage *image = [[NSImage alloc]
                initWithSize:NSMakeSize((CGFloat)pw, (CGFloat)ph)];
            [image addRepresentation:bmp];
            [wnd->ns_view setImage:image];
        }

        free(rgba);
    }
    return true;
}

bool rt_cocoa_layer_free(int64_t layer_id) {
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_remove(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return false;
    free(l->pixels);
    free(l);
    return true;
}

int64_t rt_cocoa_layer_read_pixel(int64_t layer_id, int64_t x, int64_t y) {
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return 0;
    if (x < 0 || y < 0 || x >= l->w || y >= l->h) return 0;
    return (int64_t)l->pixels[(size_t)(y * l->w + x)];
}

bool rt_cocoa_layer_blend_rect(int64_t layer_id, int64_t x, int64_t y,
                                int64_t w, int64_t h,
                                int64_t color, int64_t alpha) {
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return false;

    uint32_t a   = (uint32_t)(alpha < 0 ? 0 : alpha > 255 ? 255 : alpha);
    uint32_t inv = 255 - a;
    uint32_t sr  = (uint32_t)((color >> 16) & 0xff);
    uint32_t sg  = (uint32_t)((color >>  8) & 0xff);
    uint32_t sb  = (uint32_t)( color        & 0xff);

    int64_t lw = l->w, lh = l->h;
    int64_t x0 = x < 0 ? 0 : (x > lw ? lw : x);
    int64_t y0 = y < 0 ? 0 : (y > lh ? lh : y);
    int64_t x1 = (x+w) < 0 ? 0 : ((x+w) > lw ? lw : (x+w));
    int64_t y1 = (y+h) < 0 ? 0 : ((y+h) > lh ? lh : (y+h));

    for (int64_t yy = y0; yy < y1; yy++) {
        uint32_t *row = l->pixels + (size_t)(yy * lw);
        for (int64_t xx = x0; xx < x1; xx++) {
            uint32_t dst = row[xx];
            uint32_t dr  = (dst >> 16) & 0xff;
            uint32_t dg  = (dst >>  8) & 0xff;
            uint32_t db  =  dst        & 0xff;
            uint32_t r   = (sr * a + dr * inv) / 255;
            uint32_t g2  = (sg * a + dg * inv) / 255;
            uint32_t b   = (sb * a + db * inv) / 255;
            row[xx] = 0xff000000u | (r << 16) | (g2 << 8) | b;
        }
    }
    return true;
}

bool rt_cocoa_layer_blur(int64_t layer_id, int64_t x, int64_t y,
                          int64_t w, int64_t h, int64_t radius) {
    /*
     * Simple 3-pass box blur over the region [x,y,w,h].
     * Each pass blurs horizontally then vertically.
     */
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return false;
    if (radius <= 0) return true;

    int64_t lw = l->w, lh = l->h;
    int64_t x0 = x < 0 ? 0 : (x > lw ? lw : x);
    int64_t y0 = y < 0 ? 0 : (y > lh ? lh : y);
    int64_t x1 = (x+w) < 0 ? 0 : ((x+w) > lw ? lw : (x+w));
    int64_t y1 = (y+h) < 0 ? 0 : ((y+h) > lh ? lh : (y+h));
    if (x1 <= x0 || y1 <= y0) return true;

    int64_t rw = x1 - x0;
    int64_t rh = y1 - y0;
    uint32_t *tmp = (uint32_t *)malloc((size_t)(rw * rh) * sizeof(uint32_t));
    if (!tmp) return false;

    int64_t r = radius;
    if (r > rw / 2) r = rw / 2;
    if (r > rh / 2) r = rh / 2;
    if (r < 1) r = 1;

    /* Copy region into tmp. */
    for (int64_t yy = 0; yy < rh; yy++) {
        memcpy(tmp + (size_t)(yy * rw),
               l->pixels + (size_t)((y0 + yy) * lw + x0),
               (size_t)(rw) * sizeof(uint32_t));
    }

    /* 3 passes of box blur. */
    for (int pass = 0; pass < 3; pass++) {
        /* Horizontal. */
        for (int64_t yy = 0; yy < rh; yy++) {
            uint32_t *row = tmp + (size_t)(yy * rw);
            for (int64_t xx = 0; xx < rw; xx++) {
                int64_t lo = xx - r; if (lo < 0)   lo = 0;
                int64_t hi = xx + r; if (hi >= rw)  hi = rw - 1;
                int64_t cnt = hi - lo + 1;
                uint64_t sr2 = 0, sg2 = 0, sb2 = 0, sa2 = 0;
                for (int64_t k = lo; k <= hi; k++) {
                    uint32_t px = row[k];
                    sa2 += (px >> 24) & 0xff;
                    sr2 += (px >> 16) & 0xff;
                    sg2 += (px >>  8) & 0xff;
                    sb2 +=  px        & 0xff;
                }
                row[xx] = (uint32_t)(((sa2/cnt) << 24) | ((sr2/cnt) << 16)
                                   | ((sg2/cnt) <<  8) |  (sb2/cnt));
            }
        }
        /* Vertical. */
        for (int64_t xx = 0; xx < rw; xx++) {
            for (int64_t yy = 0; yy < rh; yy++) {
                int64_t lo = yy - r; if (lo < 0)   lo = 0;
                int64_t hi = yy + r; if (hi >= rh)  hi = rh - 1;
                int64_t cnt = hi - lo + 1;
                uint64_t sr2 = 0, sg2 = 0, sb2 = 0, sa2 = 0;
                for (int64_t k = lo; k <= hi; k++) {
                    uint32_t px = tmp[(size_t)(k * rw + xx)];
                    sa2 += (px >> 24) & 0xff;
                    sr2 += (px >> 16) & 0xff;
                    sg2 += (px >>  8) & 0xff;
                    sb2 +=  px        & 0xff;
                }
                tmp[(size_t)(yy * rw + xx)] =
                    (uint32_t)(((sa2/cnt) << 24) | ((sr2/cnt) << 16)
                              | ((sg2/cnt) <<  8) |  (sb2/cnt));
            }
        }
    }

    /* Write blurred region back to pixel buffer. */
    for (int64_t yy = 0; yy < rh; yy++) {
        memcpy(l->pixels + (size_t)((y0 + yy) * lw + x0),
               tmp + (size_t)(yy * rw),
               (size_t)(rw) * sizeof(uint32_t));
    }

    free(tmp);
    return true;
}

bool rt_cocoa_layer_gradient_v(int64_t layer_id, int64_t x, int64_t y,
                                int64_t w, int64_t h,
                                int64_t color_top, int64_t color_bottom) {
    pthread_mutex_lock(&g_mutex);
    CocoaLayer *l = (CocoaLayer *)handle_get(layer_id, KIND_LAYER);
    pthread_mutex_unlock(&g_mutex);
    if (!l) return false;

    int64_t lw = l->w, lh = l->h;
    int64_t x0 = x < 0 ? 0 : (x > lw ? lw : x);
    int64_t y0 = y < 0 ? 0 : (y > lh ? lh : y);
    int64_t x1 = (x+w) < 0 ? 0 : ((x+w) > lw ? lw : (x+w));
    int64_t y1 = (y+h) < 0 ? 0 : ((y+h) > lh ? lh : (y+h));
    if (y1 <= y0) return true;

    int64_t span = y1 - y0;
    int64_t r1 = (color_top  >> 16) & 0xff;
    int64_t g1 = (color_top  >>  8) & 0xff;
    int64_t b1 =  color_top         & 0xff;
    int64_t r2 = (color_bottom >> 16) & 0xff;
    int64_t g2 = (color_bottom >>  8) & 0xff;
    int64_t b2 =  color_bottom        & 0xff;

    for (int64_t yy = y0; yy < y1; yy++) {
        int64_t  t     = yy - y0;
        uint32_t r     = (uint32_t)((r1 * (span - t) + r2 * t) / span);
        uint32_t g     = (uint32_t)((g1 * (span - t) + g2 * t) / span);
        uint32_t b     = (uint32_t)((b1 * (span - t) + b2 * t) / span);
        uint32_t color = 0xff000000u | (r << 16) | (g << 8) | b;
        uint32_t *row  = l->pixels + (size_t)(yy * lw);
        for (int64_t xx = x0; xx < x1; xx++)
            row[xx] = color;
    }
    return true;
}

/* =========================================================================
 * Event pump
 * ====================================================================== */

int64_t rt_cocoa_event_pump(int64_t win) {
    /* Drain queued events first. */
    pthread_mutex_lock(&g_mutex);
    CocoaWindow *wnd = (CocoaWindow *)handle_get(win, KIND_WINDOW);
    if (wnd) {
        int64_t code;
        if (wnd_eq_pop(wnd, &code)) {
            pthread_mutex_unlock(&g_mutex);
            return code;
        }
    }
    pthread_mutex_unlock(&g_mutex);

    if (!is_main_thread()) return 0;

    @autoreleasepool {
        NSApplication *app = [NSApplication sharedApplication];
        NSEvent *evt = [app nextEventMatchingMask:NSEventMaskAny
                                       untilDate:[NSDate distantPast]
                                          inMode:NSDefaultRunLoopMode
                                         dequeue:YES];
        if (!evt) return 0;

        /* Encode the event type as the return value; Simple currently only
         * checks non-zero ⇒ something happened, but the raw type keeps the
         * wire compatible with future input wiring. */
        int64_t code = (int64_t)[evt type];
        [app sendEvent:evt];
        return code;
    }
}

#endif /* __APPLE__ */
