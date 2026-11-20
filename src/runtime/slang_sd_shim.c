/* slang stable-diffusion shim -- int64-only ABI for the Simple dynamic SFFI.
 *
 * Same boundary rule as slang_ggml_shim.c: it holds no policy. Simple decides
 * sizes, steps, seeds and the PNG container; this file wraps stable-diffusion.cpp's
 * opaque-options C API (sd_ctx_create / sd_generate_image) behind integer calls.
 *
 * ABI: every export takes and returns int64. Byte payloads move through the
 * wffi byte facades: IN with `spl_wffi_call_i64_with_bytes`
 * (callee sees prefix..., ptr, len, suffix...), OUT with
 * `spl_wffi_call_i64_into_bytes` (callee sees prefix..., buf, cap, out_len*).
 * A context is an opaque handle (> 0); 0 / negative is failure. Not thread
 * safe: slang serves one image at a time, and the shim adds no lock.
 *
 * Built by scripts/check/build-slang-sd-shim.shs, never by the main runtime
 * link: it needs stable-diffusion.h and the stable-diffusion.cpp static
 * archives (ggml statically linked into the DLL, see design section 3.4).
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "stable-diffusion.h"

#if defined(_WIN32)
#  define SLANG_SD_API __declspec(dllexport)
#else
#  define SLANG_SD_API __attribute__((visibility("default")))
#endif

#define SLANG_SD_MAGIC 0x534c4e47u
#define SLANG_SD_ERR_CAP 512

typedef struct {
    uint32_t magic;
    sd_ctx_t* ctx;
    sd_result_t* result;
    const sd_tensor_t* image; /* borrowed from result */
    char error[SLANG_SD_ERR_CAP];
} slang_sd_t;

static slang_sd_t* from_handle(int64_t h) {
    slang_sd_t* s = (slang_sd_t*)(intptr_t)h;
    if (h <= 0 || s->magic != SLANG_SD_MAGIC) return NULL;
    return s;
}

static void set_error(slang_sd_t* s, const char* what) {
    const char* e = sd_get_last_error();
    snprintf(s->error, SLANG_SD_ERR_CAP, "%s%s%s", what, (e && e[0]) ? ": " : "", (e && e[0]) ? e : "");
}

static int64_t copy_out(const void* src, size_t n, void* buf, int64_t cap, int64_t* out_len) {
    if (out_len) *out_len = (int64_t)n;
    if (!buf || cap < (int64_t)n) return -2; /* caller sizes with cap 0 first */
    memcpy(buf, src, n);
    return 0;
}

/* Bit 0: a model can be generated from. Bit 1: built with the Vulkan backend. */
SLANG_SD_API int64_t slang_sd_capabilities(void) {
    int64_t caps = 1;
#if defined(SLANG_SD_VULKAN)
    caps |= 2;
#endif
    return caps;
}

/* Loads a checkpoint; the path arrives as bytes. Returns the handle, 0 on failure
 * (read the reason with slang_sd_error_into(0, ...)). */
static char g_open_error[SLANG_SD_ERR_CAP];

SLANG_SD_API int64_t slang_sd_ctx_open(const char* path, int64_t path_len, int64_t n_threads) {
    char* p = (char*)malloc((size_t)path_len + 1);
    sd_ctx_opt_t* opt = sd_ctx_opt_create();
    slang_sd_t* s = (slang_sd_t*)calloc(1, sizeof(slang_sd_t));
    g_open_error[0] = 0;
    if (!p || !opt || !s) { snprintf(g_open_error, SLANG_SD_ERR_CAP, "out of memory"); goto fail; }
    memcpy(p, path, (size_t)path_len);
    p[path_len] = 0;
    s->magic = SLANG_SD_MAGIC;
    if (sd_opt_set_string(opt, "model_path", p) != SD_STATUS_OK ||
        (n_threads > 0 && sd_opt_set_int(opt, "n_threads", n_threads) != SD_STATUS_OK) ||
        sd_ctx_create(opt, &s->ctx) != SD_STATUS_OK) {
        const char* e = sd_get_last_error();
        snprintf(g_open_error, SLANG_SD_ERR_CAP, "ctx_open: %s", (e && e[0]) ? e : "failed");
        goto fail;
    }
    sd_opt_free(opt);
    free(p);
    return (int64_t)(intptr_t)s;
fail:
    sd_opt_free(opt);
    free(p);
    free(s);
    return 0;
}

/* One image, replacing any previous one held by the handle. The prompt is the
 * byte payload; cfg is scaled by 100 so the call stays integer-only.
 * Returns 0, or a negative code with the reason in slang_sd_error_into. */
SLANG_SD_API int64_t slang_sd_gen(int64_t h, const char* prompt, int64_t prompt_len,
                                  int64_t w, int64_t ht, int64_t steps, int64_t seed, int64_t cfg_x100) {
    slang_sd_t* s = from_handle(h);
    sd_img_gen_opt_t* opt;
    char* p;
    if (!s) return -1;
    sd_result_free(s->result);
    s->result = NULL;
    s->image = NULL;
    s->error[0] = 0;
    p = (char*)malloc((size_t)prompt_len + 1);
    opt = sd_img_gen_opt_create();
    if (!p || !opt) { snprintf(s->error, SLANG_SD_ERR_CAP, "out of memory"); free(p); sd_opt_free(opt); return -3; }
    memcpy(p, prompt, (size_t)prompt_len);
    p[prompt_len] = 0;
    if (sd_opt_set_string(opt, "prompt", p) != SD_STATUS_OK ||
        sd_opt_set_int(opt, "width", w) != SD_STATUS_OK ||
        sd_opt_set_int(opt, "height", ht) != SD_STATUS_OK ||
        sd_opt_set_int(opt, "seed", seed) != SD_STATUS_OK ||
        sd_opt_set_int(opt, "sample.steps", steps) != SD_STATUS_OK ||
        sd_opt_set_float(opt, "sample.guidance.txt_cfg", (double)cfg_x100 / 100.0) != SD_STATUS_OK) {
        set_error(s, "gen options");
        free(p); sd_opt_free(opt);
        return -4;
    }
    free(p);
    if (sd_generate_image(s->ctx, opt, &s->result) != SD_STATUS_OK) {
        set_error(s, "generate_image");
        sd_opt_free(opt);
        return -5;
    }
    sd_opt_free(opt);
    s->image = sd_result_get_image_count(s->result) > 0 ? sd_result_get_image(s->result, 0) : NULL;
    if (!s->image || sd_tensor_type(s->image) != SD_TENSOR_U8 || sd_tensor_rank(s->image) != 3) {
        snprintf(s->error, SLANG_SD_ERR_CAP, "generate_image returned no U8 image");
        return -6;
    }
    return 0;
}

/* Which = 0 width, 1 height, 2 channels of the held image; -1 when none. */
SLANG_SD_API int64_t slang_sd_image_dim(int64_t h, int64_t which) {
    slang_sd_t* s = from_handle(h);
    if (!s || !s->image) return -1;
    if (which == 0) return sd_tensor_dim(s->image, 1);
    if (which == 1) return sd_tensor_dim(s->image, 2);
    if (which == 2) return sd_tensor_dim(s->image, 0);
    return -1;
}

/* Interleaved 8-bit pixels, row-major. Sizing call: cap 0 reports the byte count
 * in *out_len and returns -2. */
SLANG_SD_API int64_t slang_sd_image_into(int64_t h, void* buf, int64_t cap, int64_t* out_len) {
    slang_sd_t* s = from_handle(h);
    if (!s || !s->image) return -1;
    return copy_out(sd_tensor_data(s->image), sd_tensor_byte_size(s->image), buf, cap, out_len);
}

/* Last failure text; handle 0 reads the ctx_open failure. */
SLANG_SD_API int64_t slang_sd_error_into(int64_t h, void* buf, int64_t cap, int64_t* out_len) {
    const char* e = g_open_error;
    if (h > 0) {
        slang_sd_t* s = from_handle(h);
        if (!s) return -1;
        e = s->error;
    }
    return copy_out(e, strlen(e), buf, cap, out_len);
}

/* ggml system / backend summary, for evidence that the intended backend ran. */
SLANG_SD_API int64_t slang_sd_info_into(void* buf, int64_t cap, int64_t* out_len) {
    const char* e = sd_get_system_info();
    if (!e) e = "";
    return copy_out(e, strlen(e), buf, cap, out_len);
}

SLANG_SD_API int64_t slang_sd_free(int64_t h) {
    slang_sd_t* s = from_handle(h);
    if (!s) return -1;
    sd_result_free(s->result);
    sd_ctx_free(s->ctx);
    s->magic = 0;
    free(s);
    return 0;
}
