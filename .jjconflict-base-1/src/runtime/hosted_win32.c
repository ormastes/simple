/*
 * hosted_win32.c — Win32 hosted-surface C implementation.
 *
 * Replaces src/runtime/hosted/win32.rs for the C build path.
 *
 * Two modes, controlled by the _WIN32 preprocessor macro:
 *
 *   Stub mode  (default, every non-Windows host):
 *     Every rt_win32_* symbol exists and returns -1 / false / 0.
 *     Keeps Linux + macOS link happy and lets the Simple runtime fall
 *     back to winit when no real Win32 is available.
 *
 *   Real mode  (_WIN32 defined, i.e. compiled on Windows):
 *     CreateWindowExW + CreateDIBSection + BitBlt path.
 *     No Direct2D, no D3D11 — Phase C only wants "window exists, DIB
 *     pixels get written, BitBlt pumps them to the HDC".
 *
 * Build (Windows, MSVC):
 *   cl /c /O2 hosted_win32.c /link user32.lib gdi32.lib
 *
 * Build (Windows, MinGW / clang-cl):
 *   gcc -O2 -c hosted_win32.c -luser32 -lgdi32
 */

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#define WIN32_INVALID_HANDLE ((int64_t)(-1))

/* -------------------------------------------------------------------------
 * Non-Windows stub implementations
 * ------------------------------------------------------------------------- */

#ifndef _WIN32

int64_t rt_win32_window_new(int64_t w, int64_t h, int64_t title)
    { (void)w; (void)h; (void)title; return WIN32_INVALID_HANDLE; }

bool rt_win32_window_resize(int64_t hwnd, int64_t w, int64_t h)
    { (void)hwnd; (void)w; (void)h; return false; }

bool rt_win32_window_close(int64_t hwnd)
    { (void)hwnd; return false; }

int64_t rt_win32_dib_create(int64_t hwnd, int64_t w, int64_t h, int64_t fill_color)
    { (void)hwnd; (void)w; (void)h; (void)fill_color; return WIN32_INVALID_HANDLE; }

bool rt_win32_dib_fill_rect(int64_t dib, int64_t x, int64_t y, int64_t w, int64_t h, int64_t color)
    { (void)dib; (void)x; (void)y; (void)w; (void)h; (void)color; return false; }

bool rt_win32_dib_present(int64_t hwnd, int64_t dib)
    { (void)hwnd; (void)dib; return false; }

bool rt_win32_dib_present_rect(int64_t hwnd, int64_t dib, int64_t x, int64_t y, int64_t w, int64_t h)
    { (void)hwnd; (void)dib; (void)x; (void)y; (void)w; (void)h; return false; }

bool rt_win32_dib_free(int64_t dib)
    { (void)dib; return false; }

int64_t rt_win32_dib_resize(int64_t hwnd, int64_t dib, int64_t w, int64_t h)
    { (void)hwnd; (void)dib; (void)w; (void)h; return WIN32_INVALID_HANDLE; }

int64_t rt_win32_dib_read_pixel(int64_t dib, int64_t x, int64_t y)
    { (void)dib; (void)x; (void)y; return 0; }

bool rt_win32_dib_blend_rect(int64_t dib, int64_t x, int64_t y, int64_t w, int64_t h,
                              int64_t color, int64_t alpha)
    { (void)dib; (void)x; (void)y; (void)w; (void)h; (void)color; (void)alpha; return false; }

bool rt_win32_dib_blur(int64_t dib, int64_t x, int64_t y, int64_t w, int64_t h, int64_t radius)
    { (void)dib; (void)x; (void)y; (void)w; (void)h; (void)radius; return false; }

bool rt_win32_dib_gradient_v(int64_t dib, int64_t x, int64_t y, int64_t w, int64_t h,
                              int64_t c1, int64_t c2)
    { (void)dib; (void)x; (void)y; (void)w; (void)h; (void)c1; (void)c2; return false; }

int64_t rt_win32_message_pump(int64_t hwnd)
    { (void)hwnd; return 0; }

#else /* _WIN32 — real implementation */

/* -------------------------------------------------------------------------
 * Windows headers
 * ------------------------------------------------------------------------- */

#define WIN32_LEAN_AND_MEAN
#include <windows.h>
#include <stdlib.h>

/* -------------------------------------------------------------------------
 * Handle table
 *
 * We maintain two parallel flat arrays (open-addressed by linear scan).
 * Maximum simultaneous windows and DIBs are capped at TABLE_CAP each.
 * IDs are monotonically increasing int64_t values starting at 1.
 *
 * WndSlot  — maps a window id  → HWND + backing DIB section
 * DibSlot  — maps a dib   id  → either "owned by a WndSlot" or an orphan
 *            CPU pixel buffer
 *
 * Access is serialised by a global CRITICAL_SECTION (g_cs).
 * ------------------------------------------------------------------------- */

#define TABLE_CAP 256

typedef struct {
    int64_t  id;          /* 0 = free slot */
    HWND     hwnd;
    HDC      mem_dc;
    HBITMAP  bitmap;
    HGDIOBJ  old_obj;
    uint32_t *pixels;     /* points into DIB section bits */
    int64_t  w, h;
    int64_t  last_event;
} WndSlot;

typedef struct {
    int64_t  id;          /* 0 = free slot */
    int64_t  owner_wnd;   /* 0 = orphan (owns its own pixel buffer) */
    int64_t  w, h;
    uint32_t *pixels;     /* non-NULL only when owner_wnd == 0 (orphan) */
} DibSlot;

static WndSlot      g_wnds[TABLE_CAP];
static DibSlot      g_dibs[TABLE_CAP];
static CRITICAL_SECTION g_cs;
static volatile LONG g_init_done = 0;   /* 0=not-init, 1=done */
static int64_t      g_next_id    = 1;
static bool         g_class_registered = false;

/* Window class name (UTF-16) */
static const WCHAR CLASS_NAME[] = L"SimpleHostedWin32";

/* -------------------------------------------------------------------------
 * One-time initialisation — called before every public function.
 * Uses InterlockedCompareExchange so it is safe to call from any thread.
 * ------------------------------------------------------------------------- */
static void ensure_init(void)
{
    /* Fast path — already initialised */
    if (g_init_done) return;

    /* Slow path — first caller wins */
    static LONG s_flag = 0;
    if (InterlockedCompareExchange(&s_flag, 1, 0) == 0) {
        memset(g_wnds, 0, sizeof(g_wnds));
        memset(g_dibs, 0, sizeof(g_dibs));
        InitializeCriticalSection(&g_cs);
        g_init_done = 1;
    } else {
        /* Spin until the winner finishes */
        while (!g_init_done) { Sleep(0); }
    }
}

/* -------------------------------------------------------------------------
 * Handle allocation / lookup helpers (must be called under g_cs)
 * ------------------------------------------------------------------------- */
static int64_t next_handle(void)
{
    return g_next_id++;
}

static WndSlot *wnd_find(int64_t id)
{
    if (id <= 0) return NULL;
    for (int i = 0; i < TABLE_CAP; i++) {
        if (g_wnds[i].id == id) return &g_wnds[i];
    }
    return NULL;
}

static WndSlot *wnd_alloc(void)
{
    for (int i = 0; i < TABLE_CAP; i++) {
        if (g_wnds[i].id == 0) return &g_wnds[i];
    }
    return NULL;
}

static DibSlot *dib_find(int64_t id)
{
    if (id <= 0) return NULL;
    for (int i = 0; i < TABLE_CAP; i++) {
        if (g_dibs[i].id == id) return &g_dibs[i];
    }
    return NULL;
}

static DibSlot *dib_alloc(void)
{
    for (int i = 0; i < TABLE_CAP; i++) {
        if (g_dibs[i].id == 0) return &g_dibs[i];
    }
    return NULL;
}

/* -------------------------------------------------------------------------
 * Window procedure — stateless, forwards to DefWindowProc.
 * Real event reporting happens in message_pump via PeekMessage.
 * ------------------------------------------------------------------------- */
static LRESULT CALLBACK wnd_proc(HWND hwnd, UINT msg, WPARAM wparam, LPARAM lparam)
{
    if (msg == WM_DESTROY) {
        PostQuitMessage(0);
        return 0;
    }
    return DefWindowProc(hwnd, msg, wparam, lparam);
}

/* -------------------------------------------------------------------------
 * RegisterClassEx — called once, under g_cs
 * ------------------------------------------------------------------------- */
static bool ensure_class_registered(void)
{
    if (g_class_registered) return true;

    HINSTANCE hinstance = GetModuleHandle(NULL);
    WNDCLASSEXW wc;
    memset(&wc, 0, sizeof(wc));
    wc.cbSize        = sizeof(wc);
    wc.style         = CS_HREDRAW | CS_VREDRAW | CS_OWNDC;
    wc.lpfnWndProc   = wnd_proc;
    wc.hInstance     = hinstance;
    wc.hCursor       = LoadCursor(NULL, IDC_ARROW);
    wc.lpszClassName = CLASS_NAME;

    ATOM atom = RegisterClassExW(&wc);
    /* ERROR_CLASS_ALREADY_EXISTS (1410) is fine */
    (void)atom;
    g_class_registered = true;
    return true;
}

/* -------------------------------------------------------------------------
 * DIB section creation helper
 * Allocates a top-down 32-bpp BGRA DIB and a compatible memory DC.
 * Returns false on failure; out params are zeroed on failure.
 * ------------------------------------------------------------------------- */
static bool create_dib_section(HDC screen_dc, int32_t w, int32_t h,
                                HDC *out_mem_dc, HBITMAP *out_bitmap,
                                HGDIOBJ *out_old_obj, uint32_t **out_pixels)
{
    *out_mem_dc  = NULL;
    *out_bitmap  = NULL;
    *out_old_obj = NULL;
    *out_pixels  = NULL;

    HDC mem_dc = CreateCompatibleDC(screen_dc);
    if (!mem_dc) return false;

    BITMAPINFO bmi;
    memset(&bmi, 0, sizeof(bmi));
    bmi.bmiHeader.biSize        = sizeof(BITMAPINFOHEADER);
    bmi.bmiHeader.biWidth       = w;
    bmi.bmiHeader.biHeight      = -h;   /* negative → top-down */
    bmi.bmiHeader.biPlanes      = 1;
    bmi.bmiHeader.biBitCount    = 32;
    bmi.bmiHeader.biCompression = BI_RGB;

    void *bits = NULL;
    HBITMAP bitmap = CreateDIBSection(mem_dc, &bmi, DIB_RGB_COLORS, &bits, NULL, 0);
    if (!bitmap || !bits) {
        DeleteDC(mem_dc);
        return false;
    }

    HGDIOBJ old_obj = SelectObject(mem_dc, bitmap);

    *out_mem_dc  = mem_dc;
    *out_bitmap  = bitmap;
    *out_old_obj = old_obj;
    *out_pixels  = (uint32_t *)bits;
    return true;
}

/* -------------------------------------------------------------------------
 * Clip helpers
 * ------------------------------------------------------------------------- */
static void clip_rect(int64_t lw, int64_t lh,
                      int64_t x,  int64_t y,  int64_t w,  int64_t h,
                      int64_t *ox0, int64_t *oy0, int64_t *ox1, int64_t *oy1)
{
    *ox0 = x < 0 ? 0 : (x > lw ? lw : x);
    *oy0 = y < 0 ? 0 : (y > lh ? lh : y);
    int64_t x1 = x + w;
    int64_t y1 = y + h;
    *ox1 = x1 < 0 ? 0 : (x1 > lw ? lw : x1);
    *oy1 = y1 < 0 ? 0 : (y1 > lh ? lh : y1);
}

/* -------------------------------------------------------------------------
 * Resize the DIB section that backs a WndSlot (lock must be held by caller)
 * ------------------------------------------------------------------------- */
static bool resize_wnd_dib(WndSlot *wnd, int64_t w, int64_t h)
{
    if (w <= 0 || h <= 0 || w > (int64_t)INT_MAX || h > (int64_t)INT_MAX)
        return false;

    /* Release the old DIB */
    if (wnd->mem_dc) {
        if (wnd->old_obj) SelectObject(wnd->mem_dc, wnd->old_obj);
        if (wnd->bitmap)  DeleteObject(wnd->bitmap);
        DeleteDC(wnd->mem_dc);
        wnd->mem_dc  = NULL;
        wnd->bitmap  = NULL;
        wnd->old_obj = NULL;
        wnd->pixels  = NULL;
    }

    HDC screen_dc = GetDC(wnd->hwnd);
    HDC      mem_dc;
    HBITMAP  bitmap;
    HGDIOBJ  old_obj;
    uint32_t *pixels;
    bool ok = create_dib_section(screen_dc, (int32_t)w, (int32_t)h,
                                 &mem_dc, &bitmap, &old_obj, &pixels);
    ReleaseDC(wnd->hwnd, screen_dc);

    if (!ok) return false;

    wnd->mem_dc  = mem_dc;
    wnd->bitmap  = bitmap;
    wnd->old_obj = old_obj;
    wnd->pixels  = pixels;
    wnd->w       = w;
    wnd->h       = h;
    return true;
}

/* =========================================================================
 * Public rt_win32_* functions — Windows implementation
 * ========================================================================= */

/* title is a Simple runtime string pointer (int64_t alias for char*) */
int64_t rt_win32_window_new(int64_t w, int64_t h, int64_t title)
{
    ensure_init();

    if (w <= 0 || h <= 0 || w > (int64_t)INT_MAX || h > (int64_t)INT_MAX)
        return WIN32_INVALID_HANDLE;

    const char *title_str = (const char *)(uintptr_t)title;
    if (!title_str) title_str = "untitled";

    /* Convert UTF-8 title to UTF-16 */
    int wlen = MultiByteToWideChar(CP_UTF8, 0, title_str, -1, NULL, 0);
    WCHAR *wide_title = (WCHAR *)malloc((size_t)wlen * sizeof(WCHAR));
    if (!wide_title) return WIN32_INVALID_HANDLE;
    MultiByteToWideChar(CP_UTF8, 0, title_str, -1, wide_title, wlen);

    EnterCriticalSection(&g_cs);

    if (!ensure_class_registered()) {
        LeaveCriticalSection(&g_cs);
        free(wide_title);
        return WIN32_INVALID_HANDLE;
    }

    WndSlot *slot = wnd_alloc();
    if (!slot) {
        LeaveCriticalSection(&g_cs);
        free(wide_title);
        return WIN32_INVALID_HANDLE;
    }

    HINSTANCE hinstance = GetModuleHandle(NULL);

    /* Compute outer window size so the client area matches w × h */
    RECT rect = { 0, 0, (LONG)w, (LONG)h };
    AdjustWindowRectEx(&rect, WS_OVERLAPPEDWINDOW, FALSE, WS_EX_APPWINDOW);
    int outer_w = rect.right  - rect.left;
    int outer_h = rect.bottom - rect.top;

    HWND hwnd = CreateWindowExW(
        WS_EX_APPWINDOW,
        CLASS_NAME,
        wide_title,
        WS_OVERLAPPEDWINDOW,
        CW_USEDEFAULT, CW_USEDEFAULT,
        outer_w, outer_h,
        NULL, NULL,
        hinstance,
        NULL);
    free(wide_title);

    if (!hwnd) {
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }

    /* Create the backing DIB section */
    HDC screen_dc = GetDC(hwnd);
    HDC      mem_dc;
    HBITMAP  bitmap;
    HGDIOBJ  old_obj;
    uint32_t *pixels;
    bool ok = create_dib_section(screen_dc, (int32_t)w, (int32_t)h,
                                 &mem_dc, &bitmap, &old_obj, &pixels);
    ReleaseDC(hwnd, screen_dc);

    if (!ok) {
        DestroyWindow(hwnd);
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }

    ShowWindow(hwnd, SW_SHOW);
    UpdateWindow(hwnd);

    int64_t id = next_handle();
    memset(slot, 0, sizeof(*slot));
    slot->id         = id;
    slot->hwnd       = hwnd;
    slot->mem_dc     = mem_dc;
    slot->bitmap     = bitmap;
    slot->old_obj    = old_obj;
    slot->pixels     = pixels;
    slot->w          = w;
    slot->h          = h;
    slot->last_event = 0;

    LeaveCriticalSection(&g_cs);
    return id;
}

bool rt_win32_window_resize(int64_t hwnd_id, int64_t w, int64_t h)
{
    ensure_init();
    if (w <= 0 || h <= 0 || w > (int64_t)INT_MAX || h > (int64_t)INT_MAX)
        return false;

    EnterCriticalSection(&g_cs);
    WndSlot *wnd = wnd_find(hwnd_id);
    bool ok = wnd ? resize_wnd_dib(wnd, w, h) : false;
    LeaveCriticalSection(&g_cs);
    return ok;
}

bool rt_win32_window_close(int64_t hwnd_id)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    WndSlot *wnd = wnd_find(hwnd_id);
    if (!wnd) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    /* Invalidate any DIB slots that reference this window */
    for (int i = 0; i < TABLE_CAP; i++) {
        if (g_dibs[i].id != 0 && g_dibs[i].owner_wnd == hwnd_id) {
            g_dibs[i].id        = 0;
            g_dibs[i].owner_wnd = 0;
        }
    }

    /* Release GDI resources */
    if (wnd->mem_dc) {
        if (wnd->old_obj) SelectObject(wnd->mem_dc, wnd->old_obj);
        if (wnd->bitmap)  DeleteObject(wnd->bitmap);
        DeleteDC(wnd->mem_dc);
    }
    if (wnd->hwnd) DestroyWindow(wnd->hwnd);

    memset(wnd, 0, sizeof(*wnd)); /* marks slot as free */

    LeaveCriticalSection(&g_cs);
    return true;
}

int64_t rt_win32_dib_create(int64_t hwnd_id, int64_t w, int64_t h, int64_t fill_color)
{
    ensure_init();
    if (w <= 0 || h <= 0) return WIN32_INVALID_HANDLE;

    EnterCriticalSection(&g_cs);

    DibSlot *dslot = dib_alloc();
    if (!dslot) {
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }

    WndSlot *wnd = wnd_find(hwnd_id);
    if (wnd) {
        /* Resize backing DIB if dimensions differ */
        if ((wnd->w != w || wnd->h != h) && !resize_wnd_dib(wnd, w, h)) {
            LeaveCriticalSection(&g_cs);
            return WIN32_INVALID_HANDLE;
        }

        /* Optional fill */
        if (fill_color != 0 && wnd->pixels) {
            size_t len = (size_t)(w * h);
            uint32_t c = (uint32_t)fill_color;
            for (size_t i = 0; i < len; i++) wnd->pixels[i] = c;
        }

        int64_t dib_id = next_handle();
        memset(dslot, 0, sizeof(*dslot));
        dslot->id        = dib_id;
        dslot->owner_wnd = hwnd_id;
        dslot->w         = w;
        dslot->h         = h;
        dslot->pixels    = NULL; /* pixels live inside WndSlot */

        LeaveCriticalSection(&g_cs);
        return dib_id;
    }

    /* Orphan CPU buffer — no associated window */
    size_t len = (size_t)(w * h);
    uint32_t *pixels = (uint32_t *)malloc(len * sizeof(uint32_t));
    if (!pixels) {
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }

    uint32_t c = (uint32_t)fill_color;
    for (size_t i = 0; i < len; i++) pixels[i] = c;

    int64_t dib_id = next_handle();
    memset(dslot, 0, sizeof(*dslot));
    dslot->id        = dib_id;
    dslot->owner_wnd = 0;
    dslot->w         = w;
    dslot->h         = h;
    dslot->pixels    = pixels;

    LeaveCriticalSection(&g_cs);
    return dib_id;
}

/* Resolve a dib handle → (pixels, w, h).  Called under g_cs. */
static bool dib_resolve(int64_t dib_id,
                        uint32_t **out_pixels, int64_t *out_w, int64_t *out_h)
{
    DibSlot *ds = dib_find(dib_id);
    if (!ds) return false;

    if (ds->owner_wnd != 0) {
        WndSlot *wnd = wnd_find(ds->owner_wnd);
        if (!wnd || !wnd->pixels) return false;
        *out_pixels = wnd->pixels;
        *out_w      = wnd->w;
        *out_h      = wnd->h;
    } else {
        if (!ds->pixels) return false;
        *out_pixels = ds->pixels;
        *out_w      = ds->w;
        *out_h      = ds->h;
    }
    return true;
}

bool rt_win32_dib_fill_rect(int64_t dib, int64_t x, int64_t y,
                             int64_t w, int64_t h, int64_t color)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    uint32_t *pixels; int64_t lw, lh;
    if (!dib_resolve(dib, &pixels, &lw, &lh)) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    int64_t x0, y0, x1, y1;
    clip_rect(lw, lh, x, y, w, h, &x0, &y0, &x1, &y1);
    uint32_t c = (uint32_t)color;
    for (int64_t yy = y0; yy < y1; yy++) {
        uint32_t *row = pixels + yy * lw;
        for (int64_t xx = x0; xx < x1; xx++) row[xx] = c;
    }

    LeaveCriticalSection(&g_cs);
    return true;
}

bool rt_win32_dib_present(int64_t hwnd_id, int64_t dib)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    WndSlot *wnd = wnd_find(hwnd_id);
    if (!wnd || !wnd->mem_dc || !wnd->bitmap) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    /* Only HWND-owned DIBs can present */
    DibSlot *ds = dib_find(dib);
    if (!ds || ds->owner_wnd != hwnd_id) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    HWND hwnd  = wnd->hwnd;
    HDC  mem_dc = wnd->mem_dc;
    int64_t ww = wnd->w, wh = wnd->h;

    LeaveCriticalSection(&g_cs);

    HDC screen_dc = GetDC(hwnd);
    if (!screen_dc) return false;
    BOOL ok = BitBlt(screen_dc, 0, 0, (int)ww, (int)wh,
                     mem_dc, 0, 0, SRCCOPY);
    ReleaseDC(hwnd, screen_dc);
    return ok != 0;
}

bool rt_win32_dib_present_rect(int64_t hwnd_id, int64_t dib,
                                int64_t x, int64_t y, int64_t w, int64_t h)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    WndSlot *wnd = wnd_find(hwnd_id);
    if (!wnd || !wnd->mem_dc || !wnd->bitmap) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    DibSlot *ds = dib_find(dib);
    if (!ds || ds->owner_wnd != hwnd_id) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    int64_t x0, y0, x1, y1;
    clip_rect(wnd->w, wnd->h, x, y, w, h, &x0, &y0, &x1, &y1);
    int bw = (int)(x1 - x0);
    int bh = (int)(y1 - y0);

    if (bw <= 0 || bh <= 0) {
        LeaveCriticalSection(&g_cs);
        return true;
    }

    HWND hwnd   = wnd->hwnd;
    HDC  mem_dc = wnd->mem_dc;

    LeaveCriticalSection(&g_cs);

    HDC screen_dc = GetDC(hwnd);
    if (!screen_dc) return false;
    BOOL ok = BitBlt(screen_dc, (int)x0, (int)y0, bw, bh,
                     mem_dc, (int)x0, (int)y0, SRCCOPY);
    ReleaseDC(hwnd, screen_dc);
    return ok != 0;
}

bool rt_win32_dib_free(int64_t dib)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    DibSlot *ds = dib_find(dib);
    if (!ds) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    if (ds->owner_wnd == 0 && ds->pixels) {
        free(ds->pixels);
    }
    memset(ds, 0, sizeof(*ds)); /* marks slot as free */

    LeaveCriticalSection(&g_cs);
    return true;
}

/*
 * rt_win32_dib_resize — resize a DIB.
 *
 * The user-facing spec takes (hwnd, dib, w, h) but the Rust export only
 * exposed (dib, w, h).  We accept the 4-arg form here to match the header
 * in the task specification; the hwnd param is used for HWND-owned DIBs.
 */
int64_t rt_win32_dib_resize(int64_t hwnd_id, int64_t dib, int64_t w, int64_t h)
{
    ensure_init();
    if (w <= 0 || h <= 0) return WIN32_INVALID_HANDLE;

    EnterCriticalSection(&g_cs);

    DibSlot *ds = dib_find(dib);
    if (!ds) {
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }

    if (ds->owner_wnd != 0) {
        /* HWND-owned: resize the window's backing DIB */
        WndSlot *wnd = wnd_find(ds->owner_wnd);
        bool ok = wnd ? resize_wnd_dib(wnd, w, h) : false;
        if (ok) { ds->w = w; ds->h = h; }
        LeaveCriticalSection(&g_cs);
        return ok ? dib : WIN32_INVALID_HANDLE;
    }

    /* Orphan: reallocate pixel buffer */
    uint32_t *new_pixels = (uint32_t *)malloc((size_t)(w * h) * sizeof(uint32_t));
    if (!new_pixels) {
        LeaveCriticalSection(&g_cs);
        return WIN32_INVALID_HANDLE;
    }
    memset(new_pixels, 0, (size_t)(w * h) * sizeof(uint32_t));

    if (ds->pixels) free(ds->pixels);
    ds->pixels = new_pixels;
    ds->w = w;
    ds->h = h;

    LeaveCriticalSection(&g_cs);
    return dib;
}

int64_t rt_win32_dib_read_pixel(int64_t dib, int64_t x, int64_t y)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    uint32_t *pixels; int64_t lw, lh;
    if (!dib_resolve(dib, &pixels, &lw, &lh) ||
        x < 0 || y < 0 || x >= lw || y >= lh) {
        LeaveCriticalSection(&g_cs);
        return 0;
    }

    /*
     * DIB stores BGRA; caller expects ARGB (0xAARRGGBB).
     * DIB 32-bit: byte order in memory is B G R A (little-endian u32 = 0xAARRGGBB).
     * Since BI_RGB 32-bpp stores pixels as 0x00RRGGBB in the DWORD (A byte unused
     * but set to 0xff by fill), the raw uint32_t value is already the BGRA DWORD
     * = 0xAARRGGBB when read as little-endian.  Return directly.
     */
    int64_t val = (int64_t)pixels[y * lw + x];

    LeaveCriticalSection(&g_cs);
    return val;
}

/* Alpha-blend a filled rectangle onto the DIB. */
bool rt_win32_dib_blend_rect(int64_t dib, int64_t x, int64_t y,
                              int64_t w, int64_t h,
                              int64_t color, int64_t alpha)
{
    ensure_init();

    uint32_t a   = (uint32_t)(alpha < 0 ? 0 : alpha > 255 ? 255 : alpha);
    uint32_t inv = 255 - a;
    uint32_t sr  = (uint32_t)((color >> 16) & 0xff);
    uint32_t sg  = (uint32_t)((color >>  8) & 0xff);
    uint32_t sb  = (uint32_t)( color        & 0xff);

    EnterCriticalSection(&g_cs);

    uint32_t *pixels; int64_t lw, lh;
    if (!dib_resolve(dib, &pixels, &lw, &lh)) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    int64_t x0, y0, x1, y1;
    clip_rect(lw, lh, x, y, w, h, &x0, &y0, &x1, &y1);
    for (int64_t yy = y0; yy < y1; yy++) {
        uint32_t *row = pixels + yy * lw;
        for (int64_t xx = x0; xx < x1; xx++) {
            uint32_t dst = row[xx];
            uint32_t dr  = (dst >> 16) & 0xff;
            uint32_t dg  = (dst >>  8) & 0xff;
            uint32_t db  =  dst        & 0xff;
            uint32_t r   = (sr * a + dr * inv) / 255;
            uint32_t g   = (sg * a + dg * inv) / 255;
            uint32_t b   = (sb * a + db * inv) / 255;
            row[xx] = 0xff000000u | (r << 16) | (g << 8) | b;
        }
    }

    LeaveCriticalSection(&g_cs);
    return true;
}

/* Separable box-blur — Phase C no-ops (placeholder, same as Rust). */
bool rt_win32_dib_blur(int64_t dib, int64_t x, int64_t y,
                       int64_t w, int64_t h, int64_t radius)
{
    (void)dib; (void)x; (void)y; (void)w; (void)h; (void)radius;
    return true;
}

/* Vertical linear gradient fill. */
bool rt_win32_dib_gradient_v(int64_t dib, int64_t x, int64_t y,
                              int64_t w, int64_t h,
                              int64_t c1, int64_t c2)
{
    ensure_init();

    EnterCriticalSection(&g_cs);

    uint32_t *pixels; int64_t lw, lh;
    if (!dib_resolve(dib, &pixels, &lw, &lh)) {
        LeaveCriticalSection(&g_cs);
        return false;
    }

    int64_t x0, y0, x1, y1;
    clip_rect(lw, lh, x, y, w, h, &x0, &y0, &x1, &y1);
    if (y1 <= y0) {
        LeaveCriticalSection(&g_cs);
        return true;
    }

    int64_t span = y1 - y0;
    int64_t r1 = (c1 >> 16) & 0xff, g1 = (c1 >> 8) & 0xff, b1 = c1 & 0xff;
    int64_t r2 = (c2 >> 16) & 0xff, g2 = (c2 >> 8) & 0xff, b2 = c2 & 0xff;

    for (int64_t yy = y0; yy < y1; yy++) {
        int64_t t = yy - y0;
        uint32_t r = (uint32_t)((r1 * (span - t) + r2 * t) / span);
        uint32_t g = (uint32_t)((g1 * (span - t) + g2 * t) / span);
        uint32_t b = (uint32_t)((b1 * (span - t) + b2 * t) / span);
        uint32_t c = 0xff000000u | (r << 16) | (g << 8) | b;
        uint32_t *row = pixels + yy * lw;
        for (int64_t xx = x0; xx < x1; xx++) row[xx] = c;
    }

    LeaveCriticalSection(&g_cs);
    return true;
}

/*
 * Polling-style message pump.
 *
 * Drains every pending WM_* for the given hwnd via PeekMessage + PM_REMOVE.
 * Returns the wm-id of the most recently observed interesting event, or 0
 * if nothing was pending.  Simple uses the returned wm-id as a discriminator.
 */
int64_t rt_win32_message_pump(int64_t hwnd_id)
{
    ensure_init();

    EnterCriticalSection(&g_cs);
    WndSlot *wnd = wnd_find(hwnd_id);
    HWND hwnd = wnd ? wnd->hwnd : NULL;
    LeaveCriticalSection(&g_cs);

    if (!hwnd) return 0;

    int64_t last = 0;
    MSG msg;
    while (PeekMessage(&msg, hwnd, 0, 0, PM_REMOVE)) {
        switch (msg.message) {
        case WM_KEYDOWN:
        case WM_KEYUP:
        case WM_LBUTTONDOWN:
        case WM_LBUTTONUP:
        case WM_RBUTTONDOWN:
        case WM_RBUTTONUP:
        case WM_MBUTTONDOWN:
        case WM_MBUTTONUP:
        case WM_MOUSEMOVE:
        case WM_CLOSE:
        case WM_DESTROY:
        case WM_QUIT:
            last = (int64_t)msg.message;
            break;
        default:
            break;
        }
        TranslateMessage(&msg);
        DispatchMessage(&msg);
    }

    if (last != 0) {
        EnterCriticalSection(&g_cs);
        WndSlot *w2 = wnd_find(hwnd_id);
        if (w2) w2->last_event = last;
        LeaveCriticalSection(&g_cs);
    }

    return last;
}

#endif /* _WIN32 */
