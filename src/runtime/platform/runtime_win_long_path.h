/*
 * Shared Windows long-path helper.
 *
 * Widen a UTF-8 path to UTF-16 and, when it is long enough to hit the
 * MAX_PATH (260) ceiling, resolve it to an absolute path and add the
 * `\\?\` extended-length prefix. A WIDE Win32 call (CreateFileW, etc.) is
 * NOT by itself exempt from MAX_PATH -- it still caps unless the path
 * carries the prefix, which is why a 266-character diagnostic file could be
 * written but not read back (2026-09-25).
 *
 * This used to be a byte-identical `static` copy pasted independently into
 * runtime.c, runtime_legacy_core.c and runtime_native.c. That was fragile by
 * construction: whichever TU's copy an archive linked first was a coin flip,
 * and two of the three copies were fixed for the MAX_PATH bug on different
 * days before someone noticed the third was still stale. Pulling it into one
 * header used by all Windows open/create/stat/rename/remove call sites means
 * there is exactly one place left to fix.
 *
 * `static inline` (not extern) so every translation unit that includes this
 * header still gets its own local definition -- no new cross-TU symbol, no
 * new baseline row needed for the push-rt-dual-implementation ratchet, and
 * no ODR risk from differing TU-local `static` copies (there is only one
 * copy of the *text* now, so they cannot diverge again).
 *
 * UNC (`\\...`) and already-prefixed paths are left untouched; a short
 * drive-absolute path is left untouched too since it cannot be long enough
 * to matter. Anything else is resolved via GetFullPathNameW and prefixed
 * only once the resolved length is >= 248 wide chars (a small safety margin
 * under 260). Caller frees the returned buffer with `free`.
 */
#ifndef SIMPLE_RUNTIME_WIN_LONG_PATH_H
#define SIMPLE_RUNTIME_WIN_LONG_PATH_H

#if defined(_WIN32)

#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <windows.h>

static inline wchar_t* rt_win_long_path_widen(const char* path) {
    static const wchar_t sep = (wchar_t)92;
    int wide_len = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, NULL, 0);
    if (wide_len <= 0) return NULL;
    wchar_t* wide = (wchar_t*)malloc((size_t)wide_len * sizeof(wchar_t));
    if (!wide) return NULL;
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1, wide, wide_len)) {
        free(wide);
        return NULL;
    }
    /* A short relative spelling can still resolve beyond MAX_PATH. Only skip
     * resolution for a short drive-absolute path; UNC/extended paths retain
     * their existing spelling. */
    if (wide[0] == sep && wide[1] == sep) return wide;
    if (wide_len - 1 < 248 && wide_len > 3 && wide[1] == L':' &&
        (wide[2] == sep || wide[2] == L'/')) return wide;
    {
        wchar_t* scan;
        DWORD need;
        wchar_t* full;
        wchar_t* out;
        for (scan = wide; *scan; scan++) { if (*scan == L'/') *scan = sep; }
        need = GetFullPathNameW(wide, 0, NULL, NULL);
        if (need == 0) return wide;
        full = (wchar_t*)malloc(((size_t)need + 8) * sizeof(wchar_t));
        if (!full) return wide;
        {
            DWORD written = GetFullPathNameW(wide, need, full, NULL);
            if (written == 0 || written >= need) { free(full); return wide; }
        }
        if (wcslen(full) < 248) { free(full); return wide; }
        out = (wchar_t*)malloc(((size_t)wcslen(full) + 8) * sizeof(wchar_t));
        if (!out) { free(full); return wide; }
        out[0] = sep; out[1] = sep; out[2] = L'?'; out[3] = sep;
        memcpy(out + 4, full, (wcslen(full) + 1) * sizeof(wchar_t));
        free(full);
        free(wide);
        return out;
    }
}

/* Legacy name kept as a macro alias so every existing call site
 * (`rt_widen_long_path_rc(...)`) keeps working without a rename pass. */
#define rt_widen_long_path_rc(path) rt_win_long_path_widen(path)

/*
 * Shared rename/move: MoveFileExW(MOVEFILE_REPLACE_EXISTING) for a FILE
 * destination, matching the POSIX rename(2) / Rust std::fs::rename contract
 * every caller here already assumes; plain MoveFileExW (flags 0) for a
 * DIRECTORY destination, since MOVEFILE_REPLACE_EXISTING is rejected for
 * directory moves (observed: SCV snapshot staging -> snapshots/<rev> failed
 * "snapshot-publish-failed" with the replace flag set). Both old_path and
 * new_path are narrow (UTF-8) paths; this widens and long-path-normalizes
 * both before the call. Falls back to plain CRT rename() only when a path
 * cannot be widened (never silently for the "destination exists" case, which
 * is the entire reason this helper exists). Returns nonzero on success. */
static inline int rt_win_long_path_rename(const char* old_path, const char* new_path) {
    wchar_t* wide_old = rt_win_long_path_widen(old_path);
    wchar_t* wide_new = wide_old ? rt_win_long_path_widen(new_path) : NULL;
    if (wide_old && wide_new) {
        DWORD attrs = GetFileAttributesW(wide_old);
        DWORD flags = (attrs != INVALID_FILE_ATTRIBUTES &&
                       (attrs & FILE_ATTRIBUTE_DIRECTORY)) ? 0 : MOVEFILE_REPLACE_EXISTING;
        BOOL ok = MoveFileExW(wide_old, wide_new, flags);
        free(wide_old); free(wide_new);
        return ok != 0;
    }
    free(wide_old); free(wide_new);
    return rename(old_path, new_path) == 0;
}

#endif /* _WIN32 */

#endif /* SIMPLE_RUNTIME_WIN_LONG_PATH_H */
