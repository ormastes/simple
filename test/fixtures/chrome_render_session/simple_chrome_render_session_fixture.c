/* Session-lifetime fixture only. It does not render or provide CEF evidence. */
#include "chrome_render_shim.h"
#include <stdlib.h>

static int slot_live[2];

static int valid(int64_t handle) {
    if (handle == 73) return slot_live[0];
    if (handle == 74) return slot_live[1];
    return 0;
}

uint32_t simple_chrome_render_abi_version(void) { return 1; }

int64_t simple_chrome_render_create(const uint8_t *config, uint64_t length) {
    if (!config || !length || length > CHROME_RENDER_MAX_REQUEST_BYTES) return -1;
    for (int slot = 0; slot < 2; ++slot) {
        if (!slot_live[slot]) {
            slot_live[slot] = 1;
            return 73 + slot;
        }
    }
    return -1;
}

int32_t simple_chrome_render_load_html(int64_t handle, const uint8_t *html, uint64_t length) {
    return valid(handle) && html && length ? 0 : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_load_url(int64_t handle, const uint8_t *url, uint64_t length) {
    return valid(handle) && url && length ? 0 : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_resize(int64_t handle, uint32_t width, uint32_t height, double scale) {
    (void)handle;
    (void)width;
    (void)height;
    (void)scale;
    /* The caller must refuse resize until it has a correctly typed bridge. */
    abort();
}

int32_t simple_chrome_render_frame(int64_t handle, uint64_t timeout_ms) {
    return valid(handle) && timeout_ms ? 0 : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_read_pixels_into(int64_t handle, uint8_t *buf,
                                              uint64_t capacity, uint64_t *out_len) {
    (void)buf;
    (void)capacity;
    if (out_len) *out_len = 0;
    return valid(handle) ? CHROME_RENDER_E_NO_FRAME : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_event(int64_t handle, const uint8_t *event, uint64_t length) {
    return valid(handle) && event && length ? 0 : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_last_error_into(int64_t handle, uint8_t *buf,
                                             uint64_t capacity, uint64_t *out_len) {
    (void)buf;
    (void)capacity;
    if (out_len) *out_len = 0;
    return valid(handle) ? 0 : CHROME_RENDER_E_INVALID_HANDLE;
}

int32_t simple_chrome_render_destroy(int64_t handle) {
    if (!valid(handle)) return CHROME_RENDER_E_INVALID_HANDLE;
    slot_live[handle - 73] = 0;
    return 0;
}
