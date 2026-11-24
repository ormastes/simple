/* spl_win_utf16_private.h - internal UTF-8 <-> UTF-16 conversion for the
 * Windows C runtime. Header-only, every function is static inline, and no
 * exported (rt_*) symbol is defined here.
 *
 * This replaces about a dozen hand-rolled MultiByteToWideChar and
 * WideCharToMultiByte copies. Each caller keeps its own policy:
 *   flags      0 (lenient: invalid input becomes U+FFFD) or
 *              MB_ERR_INVALID_CHARS / WC_ERR_INVALID_CHARS (strict: NULL);
 *   alloc_fn   the allocator the call site used before (malloc,
 *              rt_observed_malloc_v1, RT_OWNED_HOST_MALLOC, ...);
 *   free_fn    the free that matches alloc_fn. It releases the buffer when
 *              the second (fill) conversion fails.
 *
 * Length convention:
 *   len < 0    the input is NUL-terminated (the converted size counts the
 *              terminator, as with cchWideChar = -1);
 *   len >= 0   exactly len input units, which may contain embedded NULs.
 *              len == 0 gives an allocated empty string. len > INT_MAX
 *              gives NULL.
 * The result is always NUL-terminated. *out_len (optional) receives the
 * length without the terminator, in code units.
 *
 * Behaviour is pinned by test/rt_win_utf16_convert_characterization_selfcheck.c.
 */
#ifndef SPL_WIN_UTF16_PRIVATE_H
#define SPL_WIN_UTF16_PRIVATE_H

#ifdef _WIN32
#include <windows.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>

typedef void* (*spl_w16_alloc_fn)(size_t size);
typedef void (*spl_w16_free_fn)(void* ptr);

static inline wchar_t* spl_win_utf8_to_wide(const char* text, ptrdiff_t len, DWORD flags,
                                            spl_w16_alloc_fn alloc_fn, spl_w16_free_fn free_fn,
                                            size_t* out_len) {
    if (out_len) *out_len = 0;
    if (len > (ptrdiff_t)INT_MAX) return NULL;
    int in = len < 0 ? -1 : (int)len;
    int need = in == 0 ? 0 : MultiByteToWideChar(CP_UTF8, flags, text, in, NULL, 0);
    if (in != 0 && need <= 0) return NULL;
    size_t units = in < 0 ? (size_t)need : (size_t)need + 1;
    wchar_t* out = (wchar_t*)alloc_fn(units * sizeof(wchar_t));
    if (!out) return NULL;
    if (need && MultiByteToWideChar(CP_UTF8, flags, text, in, out, need) <= 0) {
        free_fn(out);
        return NULL;
    }
    out[units - 1] = L'\0';
    if (out_len) *out_len = units - 1;
    return out;
}

static inline char* spl_win_wide_to_utf8(const wchar_t* text, ptrdiff_t len, DWORD flags,
                                         spl_w16_alloc_fn alloc_fn, spl_w16_free_fn free_fn,
                                         size_t* out_len) {
    if (out_len) *out_len = 0;
    if (len > (ptrdiff_t)INT_MAX) return NULL;
    int in = len < 0 ? -1 : (int)len;
    int need = in == 0 ? 0 : WideCharToMultiByte(CP_UTF8, flags, text, in, NULL, 0, NULL, NULL);
    if (in != 0 && need <= 0) return NULL;
    size_t bytes = in < 0 ? (size_t)need : (size_t)need + 1;
    char* out = (char*)alloc_fn(bytes);
    if (!out) return NULL;
    if (need && WideCharToMultiByte(CP_UTF8, flags, text, in, out, need, NULL, NULL) != need) {
        free_fn(out);
        return NULL;
    }
    out[bytes - 1] = '\0';
    if (out_len) *out_len = bytes - 1;
    return out;
}

#endif /* _WIN32 */
#endif /* SPL_WIN_UTF16_PRIVATE_H */
