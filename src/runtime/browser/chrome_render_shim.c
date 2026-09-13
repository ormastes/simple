/* chrome_render_shim.c — Chrome (CEF) offscreen render dynlib, C ABI v1.
 *
 * Build modes:
 *   stub  (default)          — no CEF headers included at all; create() returns
 *                              -CHROME_RENDER_E_BACKEND_UNAVAILABLE. Compiles anywhere.
 *   -DSIMPLE_CHROME_CEF      — CEF-backed. Every CEF include lives behind this guard so a
 *                              host with no CEF drop still passes the blocking
 *                              `clang -fsyntax-only` push gate.
 *
 * The `pure logic` block below (state machine, bounds validation, status mapping) has a
 * 1:1 Simple twin at src/lib/common/browser/chrome_render_shim_twin.spl.
 */
#include "chrome_render_shim.h"

#include <string.h>

#ifdef SIMPLE_CHROME_CEF
/* Real Chromium Embedded Framework. Only ever compiled when a pinned CEF drop is staged
 * by scripts/setup/setup-cef-dynlib.shs and passed via --cef-root. */
#include "include/capi/cef_app_capi.h"
#include "include/capi/cef_client_capi.h"
#include "include/capi/cef_render_handler_capi.h"
#endif

/* ------------------------------------------------------------------ pure logic (twinned) */

/* Legal frame-state transitions. `event` is one of the CHROME_RENDER_EV_* below.
 * Returns the next state, or -1 when the transition is illegal. */
#define CHROME_RENDER_EV_RESIZE   0
#define CHROME_RENDER_EV_LOAD     1
#define CHROME_RENDER_EV_FRAME    2
#define CHROME_RENDER_EV_READ     3
#define CHROME_RENDER_EV_DESTROY  4

static int32_t chrome_render_state_next(int32_t state, int32_t event) {
    if (state == CHROME_RENDER_STATE_RELEASED) {
        return -1;
    }
    if (event == CHROME_RENDER_EV_DESTROY) {
        return CHROME_RENDER_STATE_RELEASED;
    }
    if (event == CHROME_RENDER_EV_RESIZE) {
        if (state == CHROME_RENDER_STATE_NEW || state == CHROME_RENDER_STATE_SIZED ||
            state == CHROME_RENDER_STATE_LOADED || state == CHROME_RENDER_STATE_FRAME) {
            return CHROME_RENDER_STATE_SIZED;
        }
        return -1;
    }
    if (event == CHROME_RENDER_EV_LOAD) {
        if (state == CHROME_RENDER_STATE_SIZED || state == CHROME_RENDER_STATE_LOADED ||
            state == CHROME_RENDER_STATE_FRAME) {
            return CHROME_RENDER_STATE_LOADED;
        }
        return -1; /* a document may not be loaded before the viewport is sized */
    }
    if (event == CHROME_RENDER_EV_FRAME) {
        if (state == CHROME_RENDER_STATE_LOADED || state == CHROME_RENDER_STATE_FRAME) {
            return CHROME_RENDER_STATE_FRAME;
        }
        return -1;
    }
    if (event == CHROME_RENDER_EV_READ) {
        if (state == CHROME_RENDER_STATE_FRAME) {
            return CHROME_RENDER_STATE_FRAME;
        }
        return -1;
    }
    return -1;
}

/* Byte count of one BGRA frame, or 0 when the geometry is out of bounds. */
static uint64_t chrome_render_frame_bytes(uint32_t w, uint32_t h_px) {
    uint64_t need;
    if (w == 0u || h_px == 0u) {
        return 0u;
    }
    if (w > CHROME_RENDER_MAX_DIMENSION || h_px > CHROME_RENDER_MAX_DIMENSION) {
        return 0u;
    }
    need = (uint64_t)w * (uint64_t)h_px * 4u;
    if (need > (uint64_t)CHROME_RENDER_MAX_PIXEL_BYTES) {
        return 0u;
    }
    return need;
}

/* Validates a caller-supplied readback buffer against the frame geometry.
 * Returns CHROME_RENDER_OK, E_INVALID_REQUEST or E_BUFFER_TOO_SMALL. */
static int32_t chrome_render_readback_status(uint32_t w, uint32_t h_px, uint64_t cap) {
    uint64_t need = chrome_render_frame_bytes(w, h_px);
    if (need == 0u) {
        return CHROME_RENDER_E_INVALID_REQUEST;
    }
    if (cap < need) {
        return CHROME_RENDER_E_BUFFER_TOO_SMALL;
    }
    return CHROME_RENDER_OK;
}

/* A bounded request payload is a non-empty buffer no larger than 1 MiB. */
static int32_t chrome_render_request_status(const uint8_t *data, uint64_t len) {
    if (data == NULL || len == 0u) {
        return CHROME_RENDER_E_INVALID_REQUEST;
    }
    if (len > (uint64_t)CHROME_RENDER_MAX_REQUEST_BYTES) {
        return CHROME_RENDER_E_INVALID_REQUEST;
    }
    return CHROME_RENDER_OK;
}

static const char *chrome_render_status_text(int32_t code) {
    if (code == CHROME_RENDER_OK) { return "ok"; }
    if (code == CHROME_RENDER_E_INVALID_REQUEST) { return "invalid-request"; }
    if (code == CHROME_RENDER_E_INVALID_HANDLE) { return "invalid-handle"; }
    if (code == CHROME_RENDER_E_BUFFER_TOO_SMALL) { return "buffer-too-small"; }
    if (code == CHROME_RENDER_E_BACKEND_UNAVAILABLE) { return "backend-unavailable"; }
    if (code == CHROME_RENDER_E_TIMEOUT) { return "timeout"; }
    if (code == CHROME_RENDER_E_RELEASED_HANDLE) { return "released-handle"; }
    if (code == CHROME_RENDER_E_NO_FRAME) { return "no-frame"; }
    return "unknown-status";
}

/* ------------------------------------------------------------------ session state */

typedef struct {
    int32_t  state;
    uint32_t width;
    uint32_t height;
    double   scale;
    int32_t  last_error;
#ifdef SIMPLE_CHROME_CEF
    void    *browser;      /* cef_browser_t*, owned */
    void    *render_handler;
    uint8_t *frame;        /* last on_paint BGRA buffer, owned */
    uint64_t frame_len;
#endif
} chrome_render_session;

/* v1 hosts exactly one session; the handle is 1. A handle table is not warranted until a
 * second concurrent browser is a real requirement (do not over-engineer). */
static chrome_render_session g_session;
static int32_t g_session_open = 0;
static int32_t g_last_global_error = CHROME_RENDER_E_BACKEND_UNAVAILABLE;

static chrome_render_session *chrome_render_lookup(int64_t h) {
    if (h != 1 || g_session_open == 0) {
        return NULL;
    }
    if (g_session.state == CHROME_RENDER_STATE_RELEASED) {
        return NULL;
    }
    return &g_session;
}

static int32_t chrome_render_fail(chrome_render_session *s, int32_t code) {
    if (s != NULL) {
        s->last_error = code;
    }
    g_last_global_error = code;
    return code;
}

static int32_t chrome_render_copy_out(const char *text, uint8_t *buf, uint64_t cap,
                                      uint64_t *out_len) {
    uint64_t need;
    if (buf == NULL || out_len == NULL) {
        return CHROME_RENDER_E_INVALID_REQUEST;
    }
    need = (uint64_t)strlen(text);
    if (cap < need) {
        *out_len = need;
        return CHROME_RENDER_E_BUFFER_TOO_SMALL;
    }
    memcpy(buf, text, (size_t)need);
    *out_len = need;
    return CHROME_RENDER_OK;
}

/* ------------------------------------------------------------------ exported ABI v1 */

uint32_t simple_chrome_render_abi_version(void) {
    return SIMPLE_CHROME_RENDER_ABI_VERSION;
}

int64_t simple_chrome_render_create(const uint8_t *cfg_json, uint64_t len) {
    int32_t status = chrome_render_request_status(cfg_json, len);
    if (status != CHROME_RENDER_OK) {
        g_last_global_error = status;
        return -(int64_t)status;
    }
    if (g_session_open != 0) {
        g_last_global_error = CHROME_RENDER_E_INVALID_REQUEST;
        return -(int64_t)CHROME_RENDER_E_INVALID_REQUEST;
    }
#ifdef SIMPLE_CHROME_CEF
    /* Real CEF initialisation (windowless_rendering_enabled + a cef_render_handler_t whose
     * on_paint stores the BGRA buffer into the session) is staged behind a pinned CEF drop.
     * It is deliberately NOT faked here: a stub that pretended to succeed would let
     * backend_stage report `ok` without a browser, which the lane forbids. */
    g_last_global_error = CHROME_RENDER_E_BACKEND_UNAVAILABLE;
    return -(int64_t)CHROME_RENDER_E_BACKEND_UNAVAILABLE;
#else
    g_last_global_error = CHROME_RENDER_E_BACKEND_UNAVAILABLE;
    return -(int64_t)CHROME_RENDER_E_BACKEND_UNAVAILABLE;
#endif
}

int32_t simple_chrome_render_load_html(int64_t h, const uint8_t *html, uint64_t len) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t status;
    int32_t next;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    status = chrome_render_request_status(html, len);
    if (status != CHROME_RENDER_OK) {
        return chrome_render_fail(s, status);
    }
    next = chrome_render_state_next(s->state, CHROME_RENDER_EV_LOAD);
    if (next < 0) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    s->state = next;
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_load_url(int64_t h, const uint8_t *url, uint64_t len) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t status;
    int32_t next;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    status = chrome_render_request_status(url, len);
    if (status != CHROME_RENDER_OK) {
        return chrome_render_fail(s, status);
    }
    next = chrome_render_state_next(s->state, CHROME_RENDER_EV_LOAD);
    if (next < 0) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    s->state = next;
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_resize(int64_t h, uint32_t w, uint32_t h_px, double scale) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t next;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    if (chrome_render_frame_bytes(w, h_px) == 0u || scale <= 0.0 || scale > 8.0) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    next = chrome_render_state_next(s->state, CHROME_RENDER_EV_RESIZE);
    if (next < 0) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    s->state = next;
    s->width = w;
    s->height = h_px;
    s->scale = scale;
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_frame(int64_t h, uint64_t timeout_ms) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t next;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    if (timeout_ms == 0u) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    next = chrome_render_state_next(s->state, CHROME_RENDER_EV_FRAME);
    if (next < 0) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_read_pixels_into(int64_t h, uint8_t *buf, uint64_t cap,
                                              uint64_t *out_len) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t status;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    if (buf == NULL || out_len == NULL) {
        return chrome_render_fail(s, CHROME_RENDER_E_INVALID_REQUEST);
    }
    status = chrome_render_readback_status(s->width, s->height, cap);
    if (status != CHROME_RENDER_OK) {
        *out_len = chrome_render_frame_bytes(s->width, s->height);
        return chrome_render_fail(s, status);
    }
    if (chrome_render_state_next(s->state, CHROME_RENDER_EV_READ) < 0) {
        *out_len = 0u;
        return chrome_render_fail(s, CHROME_RENDER_E_NO_FRAME);
    }
    *out_len = 0u;
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_event(int64_t h, const uint8_t *evt_json, uint64_t len) {
    chrome_render_session *s = chrome_render_lookup(h);
    int32_t status;
    if (s == NULL) {
        return chrome_render_fail(NULL, CHROME_RENDER_E_INVALID_HANDLE);
    }
    status = chrome_render_request_status(evt_json, len);
    if (status != CHROME_RENDER_OK) {
        return chrome_render_fail(s, status);
    }
    return chrome_render_fail(s, CHROME_RENDER_E_BACKEND_UNAVAILABLE);
}

int32_t simple_chrome_render_last_error_into(int64_t h, uint8_t *buf, uint64_t cap,
                                             uint64_t *out_len) {
    chrome_render_session *s;
    if (h == 0) {
        /* Handle 0 reads the process-global last error, so a caller whose create() failed
         * can still recover a reason without ever holding a session. */
        return chrome_render_copy_out(chrome_render_status_text(g_last_global_error),
                                      buf, cap, out_len);
    }
    s = chrome_render_lookup(h);
    if (s == NULL) {
        return CHROME_RENDER_E_INVALID_HANDLE;
    }
    return chrome_render_copy_out(chrome_render_status_text(s->last_error), buf, cap, out_len);
}

int32_t simple_chrome_render_destroy(int64_t h) {
    chrome_render_session *s = chrome_render_lookup(h);
    if (s == NULL) {
        /* destroy(0) and destroy of an already-released handle must not crash. */
        g_last_global_error = CHROME_RENDER_E_INVALID_HANDLE;
        return CHROME_RENDER_E_INVALID_HANDLE;
    }
    s->state = CHROME_RENDER_STATE_RELEASED;
    g_session_open = 0;
    g_last_global_error = CHROME_RENDER_OK;
    return CHROME_RENDER_OK;
}
