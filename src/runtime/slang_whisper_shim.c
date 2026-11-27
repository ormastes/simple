/* slang whisper shim -- int64-only ABI over whisper.cpp for the Simple dynamic SFFI.
 *
 * whisper_full() takes a struct by value (whisper_full_params), which the
 * int64-only dynamic SFFI cannot pass, so this file builds that struct and
 * exposes four scalar entries. Policy lives in Simple
 * (src/lib/gc_async_mut/slang/model_executor/runners/whisper_runner.spl).
 *
 * ONE-GGML RULE: whisper.cpp vendors its own ggml. This DLL links it
 * STATICALLY (scripts/check/build-slang-whisper-shim.shs, BUILD_SHARED_LIBS=OFF)
 * so it can never bind to llama.cpp's ggml.dll already loaded for chat.
 *
 * ABI: init(path_ptr, path_len)            -> 0 ok, <0 failure   (path bytes IN)
 *      transcribe(pcm_ptr, pcm_bytes, n_threads) -> n_segments, <0 failure
 *                                          (PCM is 16 kHz mono s16le, bytes IN)
 *      text_into(buf, cap, out_len_ptr)    -> 0 ok, -1 buffer too small;
 *                                          *out_len is always the full length
 *      free()                              -> 0
 * One resident model per process (the runner keeps a single model open).
 * Built by scripts/check/build-slang-whisper-shim.shs, never by the main
 * runtime link: it needs whisper.h, an external SDK header.
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "whisper.h"

#define SLANG_WHISPER_TEXT_CAP (1 << 20)

static struct whisper_context *g_ctx = NULL;
static char *g_text = NULL;
static size_t g_text_len = 0;

static void quiet_log(enum ggml_log_level level, const char *text, void *user) {
    (void)level; (void)text; (void)user;
}

int64_t slang_whisper_abi(void) { return 1; }

int64_t slang_whisper_free(void) {
    if (g_ctx != NULL) {
        whisper_free(g_ctx);
        g_ctx = NULL;
    }
    free(g_text);
    g_text = NULL;
    g_text_len = 0;
    return 0;
}

int64_t slang_whisper_init(int64_t path_ptr, int64_t path_len) {
    if (path_ptr == 0 || path_len <= 0 || path_len > 4096) {
        return -1;
    }
    char path[4097];
    memcpy(path, (const void *)(intptr_t)path_ptr, (size_t)path_len);
    path[path_len] = '\0';
    slang_whisper_free();
    whisper_log_set(quiet_log, NULL);
    struct whisper_context_params cp = whisper_context_default_params();
    cp.use_gpu = false;
    g_ctx = whisper_init_from_file_with_params(path, cp);
    return g_ctx != NULL ? 0 : -2;
}

int64_t slang_whisper_transcribe(int64_t pcm_ptr, int64_t pcm_bytes, int64_t n_threads) {
    if (g_ctx == NULL) {
        return -1;
    }
    if (pcm_ptr == 0 || pcm_bytes < 2 || pcm_bytes > ((int64_t)1 << 30)) {
        return -2;
    }
    size_t n = (size_t)pcm_bytes / 2;
    const uint8_t *src = (const uint8_t *)(intptr_t)pcm_ptr;
    float *pcm = (float *)malloc(n * sizeof(float));
    if (pcm == NULL) {
        return -3;
    }
    for (size_t i = 0; i < n; i++) {
        int16_t s = (int16_t)((uint16_t)src[2 * i] | ((uint16_t)src[2 * i + 1] << 8));
        pcm[i] = (float)s / 32768.0f;
    }
    struct whisper_full_params wp = whisper_full_default_params(WHISPER_SAMPLING_GREEDY);
    wp.print_progress = false;
    wp.print_realtime = false;
    wp.print_timestamps = false;
    wp.print_special = false;
    wp.n_threads = n_threads > 0 ? (int)n_threads : 4;
    wp.language = "en";
    int rc = whisper_full(g_ctx, wp, pcm, (int)n);
    free(pcm);
    if (rc != 0) {
        return -4;
    }
    free(g_text);
    g_text = (char *)malloc(SLANG_WHISPER_TEXT_CAP);
    g_text_len = 0;
    if (g_text == NULL) {
        return -3;
    }
    int segs = whisper_full_n_segments(g_ctx);
    for (int i = 0; i < segs; i++) {
        const char *t = whisper_full_get_segment_text(g_ctx, i);
        size_t len = t != NULL ? strlen(t) : 0;
        if (g_text_len + len >= SLANG_WHISPER_TEXT_CAP) {
            break;
        }
        memcpy(g_text + g_text_len, t, len);
        g_text_len += len;
    }
    return segs;
}

int64_t slang_whisper_text_into(int64_t buf, int64_t cap, int64_t out_len_ptr) {
    if (out_len_ptr != 0) {
        *(int64_t *)(intptr_t)out_len_ptr = (int64_t)g_text_len;
    }
    if (buf == 0 || cap < (int64_t)g_text_len) {
        return -1;
    }
    if (g_text_len > 0) {
        memcpy((void *)(intptr_t)buf, g_text, g_text_len);
    }
    return 0;
}
