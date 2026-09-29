/*
 * Core-C exports for symbols stranded in the uncompiled runtime.c.
 *
 * Group E of the Stage 2 Windows unresolved-symbol inventory
 * (doc/08_tracking/bug/stage2_windows_unresolved_inventory_2026-08-31.md):
 * seven rt_* entry points whose only definitions live in
 * src/runtime/runtime.c, which is NOT in the core-C source list
 * (native_project/tools.rs, build_c_runtime_library) and must not be added
 * wholesale -- measured, runtime.c's 121 rt_* definitions collide with 53
 * symbols in the core-C supplement objects and 69 in the Rust runtime
 * authority archives (same trap as the disproved "just add runtime_native.c"
 * fix, 8ca87866c6: 475 collisions). This TU therefore defines EXACTLY the
 * seven missing symbols, self-contained, with every helper static:
 *
 *   rt_mkdir, rt_random_i64,
 *   rt_readdir, rt_readdir_count, rt_readdir_entry, rt_readdir_free,
 *   rt_shell_output
 *
 * ABI (2026-08-31 fix -- the first landing of this TU copied runtime.c's
 * `const char*` signatures, which are WRONG for the native lane): none of
 * these names appear in text_arg_indices (src/compiler/50.mir/
 * text_extern_abi.spl) nor in the Rust twin (codegen/instr/calls.rs), so
 * native codegen passes every `text` argument as ONE tagged runtime value
 * and reads a `text` return as a tagged value (precedent:
 * rt_file_read_text_rv(path: RuntimeValue) -> RuntimeValue,
 * runtime/src/value/sffi/file_io/file_ops.rs). runtime.c's char* versions
 * were never linked into any native binary (that is why these were
 * unresolved), so there is no working char* caller to preserve. Decode
 * text args with rt_string_data/rt_string_len; build text returns with
 * rt_string_new.
 *
 * Semantics oracles:
 *   - rt_readdir family: interpreter shim (interpreter_extern/file_io.rs
 *     rt_readdir*): missing dir -> handle 0; "." and ".." excluded;
 *     entry out of range -> empty text; free is idempotent-safe on 0.
 *   - rt_mkdir: interpreter shim: 0 on success, -errno on failure
 *     (EEXIST stays an error, matching create_dir).
 *   - rt_random_i64: OS CSPRNG (interpreter uses OsRng; runtime.c uses
 *     /dev/urandom; Windows uses BCryptGenRandom).
 *   - rt_shell_output: runtime.c spl_shell_output: capture stdout
 *     verbatim (no newline trim), empty text on any failure.
 *
 * Unlike runtime.c (whose _WIN32 branch stubs readdir/mkdir to failure),
 * the Windows paths here are real implementations -- this lane exists
 * because the Windows MSVC Stage 2 link needs them. Windows paths are
 * treated as UTF-8 and converted to UTF-16 for the filesystem calls
 * (FindFirstFileW/_wmkdir), matching the Rust runtime's std::fs
 * behaviour; the ANSI A-functions silently fail on non-ACP characters.
 *
 * Keep zero-overlap (llvm-nm --defined-only, LC_ALL=C comm) against
 * core_c_bootstrap_supplement *.obj, simple_native_all.lib and
 * simple_compiler_backfill.lib when extending this file.
 */

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>

#ifdef _WIN32
#include <windows.h>
#include <direct.h>
#else
#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#endif

/* ---- tagged-text decode helper (static; same shape as
 *      runtime_core_io_exports.c's core_io_text_arg) ---- */

static int core_exp_text_arg(int64_t value, char* buf, size_t buf_size) {
    int64_t len = rt_string_len(value);
    if (len < 0 || (uint64_t)len >= buf_size) return 0;
    const uint8_t* data = rt_string_data(value);
    if (!data && len != 0) return 0;
    if (len != 0) memcpy(buf, data, (size_t)len);
    buf[(size_t)len] = '\0';
    return 1;
}

/* Heap copy for values too long for a stack buffer (shell command lines).
 * NULL on failure; caller frees. */
static char* core_exp_text_arg_dup(int64_t value) {
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
/* UTF-8 -> UTF-16 for filesystem calls. Returns a malloc'd wide string,
 * NULL on failure; caller frees. */
static wchar_t* core_exp_utf8_to_wide(const char* utf8) {
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

/* UTF-16 -> UTF-8 into a malloc'd buffer, NULL on failure. */
static char* core_exp_wide_to_utf8(const wchar_t* wide) {
    int len = WideCharToMultiByte(CP_UTF8, 0, wide, -1, NULL, 0, NULL, NULL);
    if (len <= 0) return NULL;
    char* utf8 = (char*)malloc((size_t)len);
    if (!utf8) return NULL;
    if (WideCharToMultiByte(CP_UTF8, 0, wide, -1, utf8, len, NULL, NULL) <= 0) {
        free(utf8);
        return NULL;
    }
    return utf8;
}
#endif

/* ---- directory listing (interpreter shim's handle contract) ---- */

typedef struct {
    char** entries;
    int64_t count;
    int64_t cap;
} rt_core_dir_listing;

static rt_core_dir_listing* rt_core_dir_listing_new(void) {
    rt_core_dir_listing* dl = (rt_core_dir_listing*)calloc(1, sizeof(rt_core_dir_listing));
    if (!dl) return NULL;
    dl->cap = 64;
    dl->entries = (char**)malloc(sizeof(char*) * (size_t)dl->cap);
    if (!dl->entries) { free(dl); return NULL; }
    dl->count = 0;
    return dl;
}

static void rt_core_dir_listing_push(rt_core_dir_listing* dl, const char* name) {
    if (dl->count >= dl->cap) {
        dl->cap *= 2;
        char** grown = (char**)realloc(dl->entries, sizeof(char*) * (size_t)dl->cap);
        if (!grown) return;
        dl->entries = grown;
    }
    char* copy = (char*)malloc(strlen(name) + 1);
    if (!copy) return;
    memcpy(copy, name, strlen(name) + 1);
    dl->entries[dl->count++] = copy;
}

/* tagged text path -> opaque listing handle; 0 on any failure. */
int64_t rt_readdir(int64_t path_value) {
    char path[4096];
    if (!core_exp_text_arg(path_value, path, sizeof(path))) return 0;
#ifdef _WIN32
    wchar_t* wpath = core_exp_utf8_to_wide(path);
    if (!wpath) return 0;
    size_t wlen = wcslen(wpath);
    wchar_t* pattern = (wchar_t*)malloc(sizeof(wchar_t) * (wlen + 3));
    if (!pattern) { free(wpath); return 0; }
    memcpy(pattern, wpath, sizeof(wchar_t) * wlen);
    while (wlen > 0 && (pattern[wlen - 1] == L'\\' || pattern[wlen - 1] == L'/')) wlen--;
    pattern[wlen] = L'\\';
    pattern[wlen + 1] = L'*';
    pattern[wlen + 2] = L'\0';
    free(wpath);
    WIN32_FIND_DATAW fd;
    HANDLE h = FindFirstFileW(pattern, &fd);
    free(pattern);
    if (h == INVALID_HANDLE_VALUE) return 0;
    rt_core_dir_listing* dl = rt_core_dir_listing_new();
    if (!dl) { FindClose(h); return 0; }
    do {
        if (wcscmp(fd.cFileName, L".") == 0 || wcscmp(fd.cFileName, L"..") == 0) continue;
        char* name = core_exp_wide_to_utf8(fd.cFileName);
        if (!name) continue;
        rt_core_dir_listing_push(dl, name);
        free(name);
    } while (FindNextFileW(h, &fd));
    FindClose(h);
    return (int64_t)(uintptr_t)dl;
#else
    DIR* d = opendir(path);
    if (!d) return 0;
    rt_core_dir_listing* dl = rt_core_dir_listing_new();
    if (!dl) { closedir(d); return 0; }
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        rt_core_dir_listing_push(dl, ent->d_name);
    }
    closedir(d);
    return (int64_t)(uintptr_t)dl;
#endif
}

int64_t rt_readdir_count(int64_t handle) {
    if (!handle) return 0;
    return ((rt_core_dir_listing*)(uintptr_t)handle)->count;
}

/* -> tagged text (empty text when handle is 0 or index out of range). */
int64_t rt_readdir_entry(int64_t handle, int64_t index) {
    if (!handle) return rt_string_new(NULL, 0);
    rt_core_dir_listing* dl = (rt_core_dir_listing*)(uintptr_t)handle;
    if (index < 0 || index >= dl->count) return rt_string_new(NULL, 0);
    const char* name = dl->entries[index];
    return rt_string_new((const uint8_t*)name, (uint64_t)strlen(name));
}

void rt_readdir_free(int64_t handle) {
    if (!handle) return;
    rt_core_dir_listing* dl = (rt_core_dir_listing*)(uintptr_t)handle;
    for (int64_t i = 0; i < dl->count; i++) free(dl->entries[i]);
    free(dl->entries);
    free(dl);
}

/* ---- mkdir: tagged text path; 0 on success, -errno on failure
 *      (interpreter shim contract: EEXIST is an error) ---- */

int64_t rt_mkdir(int64_t path_value, int64_t mode) {
    char path[4096];
    if (!core_exp_text_arg(path_value, path, sizeof(path))) return -(int64_t)EINVAL;
#ifdef _WIN32
    (void)mode;
    wchar_t* wpath = core_exp_utf8_to_wide(path);
    if (!wpath) return -(int64_t)EINVAL;
    int rc = _wmkdir(wpath);
    free(wpath);
    if (rc == 0) return 0;
    return -(int64_t)errno;
#else
    if (mode == 0) mode = 0755;
    return mkdir(path, (mode_t)mode) == 0 ? 0 : -(int64_t)errno;
#endif
}

/* ---- cryptographically random i64 (mirrors runtime.c) ---- */

int64_t rt_random_i64(void) {
#ifdef _WIN32
    /* BCryptGenRandom via LoadLibrary: no bcrypt.lib link dependency. */
    int64_t val = 0;
    typedef long (WINAPI *BCryptGenRandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    HMODULE hLib = LoadLibraryA("bcrypt.dll");
    if (hLib) {
        BCryptGenRandomFn fn = (BCryptGenRandomFn)GetProcAddress(hLib, "BCryptGenRandom");
        if (fn) {
            /* BCRYPT_USE_SYSTEM_PREFERRED_RNG */
            fn(NULL, (unsigned char*)&val, sizeof(val), 0x00000002);
        }
        FreeLibrary(hLib);
    }
    return val;
#else
    int64_t val = 0;
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd >= 0) {
        size_t got = 0;
        while (got < sizeof(val)) {
            ssize_t n = read(fd, (unsigned char*)&val + got, sizeof(val) - got);
            if (n <= 0) {
                if (n < 0 && errno == EINTR) continue;
                break; /* short read: partial entropy is still better than 0 */
            }
            got += (size_t)n;
        }
        close(fd);
    }
    return val;
#endif
}

/* ---- shell output capture (self-contained: spl_shell_output lives in the
 *      uncompiled runtime.c, so it cannot be delegated to here).
 *      tagged text cmd -> tagged text stdout; empty text on failure. ---- */

int64_t rt_shell_output(int64_t cmd_value) {
#ifdef _WIN32
#define RT_CORE_POPEN _popen
#define RT_CORE_PCLOSE _pclose
#else
#define RT_CORE_POPEN popen
#define RT_CORE_PCLOSE pclose
#endif
    char* cmd = core_exp_text_arg_dup(cmd_value);
    if (!cmd) return rt_string_new(NULL, 0);
    FILE* pipe = RT_CORE_POPEN(cmd, "r");
    free(cmd);
    if (!pipe) return rt_string_new(NULL, 0);
    size_t cap = 4096, pos = 0;
    char* buf = (char*)malloc(cap);
    if (!buf) { RT_CORE_PCLOSE(pipe); return rt_string_new(NULL, 0); }
    char tmp[1024];
    size_t n;
    while ((n = fread(tmp, 1, sizeof(tmp), pipe)) > 0) {
        while (pos + n + 1 > cap) {
            cap *= 2;
            char* grown = (char*)realloc(buf, cap);
            if (!grown) { free(buf); RT_CORE_PCLOSE(pipe); return rt_string_new(NULL, 0); }
            buf = grown;
        }
        memcpy(buf + pos, tmp, n);
        pos += n;
    }
    RT_CORE_PCLOSE(pipe);
    int64_t result = rt_string_new((const uint8_t*)buf, (uint64_t)pos);
    free(buf);
    return result;
#undef RT_CORE_POPEN
#undef RT_CORE_PCLOSE
}
