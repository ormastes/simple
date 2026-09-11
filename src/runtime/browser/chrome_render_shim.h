/* chrome_render_shim.h — frozen C ABI v1 for the Chrome (CEF) offscreen render dynlib.
 *
 * Boundary justification (see doc/01_research/ui/chrome_dynlib/
 * chrome_dynlib_vulkan_render_module_2026-09-11.md §3.1): CEF delivers offscreen frames
 * by CALLING BACK into the host (cef_render_handler_t::on_paint). The repo's FFI is
 * forward-only (spl_wffi_call_i64 / rt_dyncall_0..6) and no host C->Simple trampoline
 * exists, so the callback owner must be C. The pure logic in this module has a Simple
 * twin at src/lib/common/browser/chrome_render_shim_twin.spl for the dual-run gate.
 *
 * This ABI is a SIBLING of, not a replacement for, the frozen 5-symbol
 * simple_chromium_oracle_* ABI: disjoint prefix, same nm-exact-set discipline.
 *
 * Exactly 10 symbols are exported. Everything else in the .c file is static.
 */
#ifndef SIMPLE_CHROME_RENDER_SHIM_H
#define SIMPLE_CHROME_RENDER_SHIM_H

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

#if defined(_WIN32)
#define SIMPLE_CHROME_RENDER_API __declspec(dllexport)
#else
#define SIMPLE_CHROME_RENDER_API __attribute__((visibility("default")))
#endif

/* ABI version. Frozen at 1. */
#define SIMPLE_CHROME_RENDER_ABI_VERSION 1u

/* Status codes. Mirrored 1:1 by chrome_render_status_text() in the Simple twin. */
#define CHROME_RENDER_OK                       0
#define CHROME_RENDER_E_INVALID_REQUEST        1
#define CHROME_RENDER_E_INVALID_HANDLE         2
#define CHROME_RENDER_E_BUFFER_TOO_SMALL       3
#define CHROME_RENDER_E_BACKEND_UNAVAILABLE    4
#define CHROME_RENDER_E_TIMEOUT                5
#define CHROME_RENDER_E_RELEASED_HANDLE        6
#define CHROME_RENDER_E_NO_FRAME               7

/* Frame state machine. Mirrored by chrome_render_state_next() in the Simple twin. */
#define CHROME_RENDER_STATE_NEW        0
#define CHROME_RENDER_STATE_SIZED      1
#define CHROME_RENDER_STATE_LOADED     2
#define CHROME_RENDER_STATE_FRAME      3
#define CHROME_RENDER_STATE_RELEASED   4

/* Bounds. Request payloads are capped at 1 MiB; a pixel response is w*h*4 and may never
 * exceed the hard ceiling regardless of the caller-supplied capacity. */
#define CHROME_RENDER_MAX_REQUEST_BYTES   1048576u
#define CHROME_RENDER_MAX_PIXEL_BYTES     268435456u /* 256 MiB: 8192x8192x4 */
#define CHROME_RENDER_MAX_DIMENSION       8192u

/* --- the 10 exported symbols (ABI v1) --- */
SIMPLE_CHROME_RENDER_API uint32_t simple_chrome_render_abi_version(void);
SIMPLE_CHROME_RENDER_API int64_t  simple_chrome_render_create(const uint8_t *cfg_json, uint64_t len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_load_html(int64_t h, const uint8_t *html, uint64_t len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_load_url(int64_t h, const uint8_t *url, uint64_t len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_resize(int64_t h, uint32_t w, uint32_t h_px, double scale);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_frame(int64_t h, uint64_t timeout_ms);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_read_pixels_into(int64_t h, uint8_t *buf, uint64_t cap, uint64_t *out_len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_event(int64_t h, const uint8_t *evt_json, uint64_t len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_last_error_into(int64_t h, uint8_t *buf, uint64_t cap, uint64_t *out_len);
SIMPLE_CHROME_RENDER_API int32_t  simple_chrome_render_destroy(int64_t h);

#ifdef __cplusplus
}
#endif
#endif /* SIMPLE_CHROME_RENDER_SHIM_H */
