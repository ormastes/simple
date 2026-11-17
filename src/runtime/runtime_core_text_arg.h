/* Shared tagged-text argument decode helpers for the core export TUs
 * (runtime_core_exports.c, runtime_core_io_exports.c,
 * runtime_core_host_services.c). Previously copied verbatim in each file.
 * Include after "runtime.h" (needs rt_string_len / rt_string_data). */
#ifndef RUNTIME_CORE_TEXT_ARG_H
#define RUNTIME_CORE_TEXT_ARG_H

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#ifdef _WIN32
#include <windows.h>
#endif

/* Copy a tagged text argument into buf as a NUL-terminated C string.
 * Returns 0 when the value is not a text or does not fit. */
static inline int core_text_arg(int64_t value, char* buf, size_t buf_size) {
    int64_t len = rt_string_len(value);
    if (len < 0 || (uint64_t)len >= buf_size) return 0;
    const uint8_t* data = rt_string_data(value);
    if (!data && len != 0) return 0;
    if (len != 0) memcpy(buf, data, (size_t)len);
    buf[(size_t)len] = '\0';
    return 1;
}

/* Heap copy of a tagged text argument (for values too long for a stack
 * buffer, e.g. shell command lines). NULL on failure; caller frees. */
static inline char* core_text_arg_dup(int64_t value) {
    int64_t len = rt_string_len(value);
    if (len < 0) return NULL;
    const uint8_t* data = rt_string_data(value);
    if (!data && len != 0) return NULL;
    char* buf = (char*)malloc((size_t)len + 1u);
    if (!buf) return NULL;
    if (len != 0) memcpy(buf, data, (size_t)len);
    buf[(size_t)len] = '\0';
    return buf;
}

#ifdef _WIN32
/* UTF-8 -> UTF-16 for W-API filesystem calls. Malloc'd, NULL on failure. */
static inline wchar_t* core_utf8_to_wide(const char* utf8) {
    int wlen = MultiByteToWideChar(CP_UTF8, 0, utf8, -1, NULL, 0);
    if (wlen <= 0) return NULL;
    wchar_t* wide = (wchar_t*)malloc(sizeof(wchar_t) * (size_t)wlen);
    if (!wide) return NULL;
    if (MultiByteToWideChar(CP_UTF8, 0, utf8, -1, wide, wlen) <= 0) {
        free(wide);
        return NULL;
    }
    return wide;
}
#endif

#endif /* RUNTIME_CORE_TEXT_ARG_H */
