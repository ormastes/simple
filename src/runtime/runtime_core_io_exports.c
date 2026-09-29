/*
 * Core-C exports for the 12 io/system externs with no native definition
 * anywhere in the tree.
 *
 * Groups F + G + I(rest) + J of the Stage 2 Windows unresolved-symbol
 * inventory (doc/08_tracking/bug/stage2_windows_unresolved_inventory_
 * 2026-08-31): these names existed only as Simple-side `extern fn`
 * declarations (none has an interpreter shim, a Rust-runtime extern "C"
 * definition, or a C definition -- verified per symbol against
 * src/runtime, src/compiler_rust/runtime/src and
 * interpreter_extern), so every native link left them unresolved.
 * This TU defines EXACTLY the twelve, self-contained, every helper static:
 *
 *   F  stdin/terminal : rt_stdin_read, rt_stdin_read_all,
 *                       rt_term_write, rt_term_flush
 *   G  sffi io singles: rt_file_modified, rt_file_modified_time,
 *                       rt_list_dir_recursive, rt_path_normalize
 *   I  system singles : rt_shell, rt_process_output
 *   J  string<->bytes : rt_string_to_byte_array, rt_string_from_byte_array
 *
 * ABI (same contract note as runtime_core_host_services.c): none of these
 * names appear in text_arg_indices (src/compiler/50.mir/text_extern_abi.spl)
 * nor in the Rust twin (codegen/instr/calls.rs), so every `text` argument
 * arrives as ONE tagged runtime value (decode via rt_string_data /
 * rt_string_len) and a `text` return is a tagged value built by
 * rt_string_new. `[u8]` / `[text]` values are tagged runtime arrays:
 * built with rt_array_new + rt_array_push, elements read with
 * rt_array_len_safe + rt_array_get -- the rt_dir_walk / rt_text_to_bytes
 * convention. A [u8] element is an inline tagged int (TAG_INT == 0,
 * payload << 3), mirroring RuntimeValue::from_int (runtime/src/value/
 * core.rs:237) and the freestanding kernel oracle
 * (src/os/kernel/arch/riscv64/boot/freestanding_runtime.c:3482).
 *
 * Per-symbol oracles (pinned here because several functions have only the
 * facade as an in-tree caller):
 *   - rt_stdin_read(size) -> [u8]: ONE-SHOT read of up to `size` bytes.
 *     pipe.spl's Stdin.read_exact loops on this and treats a 0-length
 *     chunk as EOF, so partial reads are part of the contract -- hence
 *     read()/_read(), never fread(). Empty array on EOF/error/size<=0.
 *   - rt_stdin_read_all() -> [u8]: loop until EOF. Windows: both switch
 *     stdin to _O_BINARY once so bytes are not CRLF-translated ([u8] is a
 *     byte contract).
 *   - rt_term_write(text) -> i64 bytes written; rt_term_flush() -> i32
 *     (0 ok, -1 error). Terminal == stdout, matching the pipe.spl/host.spl
 *     facades that pair them with rt_stdout_*.
 *   - rt_file_modified_time(path) -> i64: st_mtime SECONDS since the epoch,
 *     negative on failure (io.spl's @unsafe note; cache_validator.spl and
 *     the watcher only compare values and test > 0).
 *   - rt_file_modified(path) -> i64: signature-only oracle ("raw filesystem
 *     path modified-state ABI"); deliberately the same mtime-seconds
 *     contract as rt_file_modified_time so the two facades can never
 *     disagree about the same file.
 *   - rt_list_dir_recursive(path, ext) -> [text]: recursive file walk
 *     (directories descended, not emitted), FULL paths, platform separator
 *     -- rt_dir_walk's shape (runtime.c:2300) -- filtered to names ending
 *     in `ext` (leading dot optional; empty ext = every file).
 *   - rt_path_normalize(path) -> text: signature-only oracle; LEXICAL
 *     normalization, no filesystem access: both separators accepted, '/'
 *     emitted, duplicate separators collapsed, "." dropped, ".." resolved
 *     against a prior real segment only. Empty/degenerate input -> ".".
 *   - rt_shell(cmd) -> i64: system() through the platform shell, EXIT CODE
 *     (io_runtime.spl "raw shell command text and exit-status ABI";
 *     rt_shell_exec/rt_shell_exit_code sibling convention). -1 when the
 *     shell could not run or the child died on a signal.
 *   - rt_process_output(cmd, args) -> text: run cmd with args, capture
 *     STDOUT; empty text on failure (system.spl's @unsafe note says empty
 *     conflates empty output with failure -- that is the declared ABI).
 *     Args are best-effort double-quoted; cmd.exe quoting is inherently
 *     lossy for adversarial args, which this lane accepts.
 *   - rt_string_to_byte_array / rt_string_from_byte_array: exact mirrors of
 *     the Rust runtime's rt_text_to_bytes / rt_bytes_to_text
 *     (value/sffi/file_io/file_ops.rs:1415,1439); the interpreter registers
 *     rt_string_from_byte_array as an ALIAS of rt_bytes_to_text
 *     (interpreter_extern/mod.rs:287). Failure returns empty text/array
 *     (the facade convention; Rust's NIL would poison a non-optional text).
 *
 * Verified zero-overlap (llvm-nm --defined-only, LC_ALL=C comm -12) against
 * libspl_objects.a, core_c_bootstrap_supplement *.obj, simple_native_all.lib
 * and simple_compiler_backfill.lib before landing; keep it that way when
 * extending this file.
 */

#ifndef _POSIX_C_SOURCE
#define _POSIX_C_SOURCE 200809L
#endif

#include "runtime.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include <windows.h>
#include <io.h>
#include <fcntl.h>
#include <sys/stat.h>
#undef max
#else
#include <dirent.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

/* ---- shared decode/build helpers (all static) ---- */

/* Copy a tagged text argument into buf as a NUL-terminated C string.
 * Returns 0 when the value is not a text or does not fit.
 * (Same shape as runtime_core_host_services.c's core_host_text_arg.) */
static int core_io_text_arg(int64_t value, char* buf, size_t buf_size) {
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
static char* core_io_text_arg_dup(int64_t value) {
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

static int64_t core_io_empty_text(void) {
    return rt_string_new(NULL, 0);
}

#ifdef _WIN32
/* Paths cross this ABI as UTF-8. The ANSI A-functions interpret bytes in
 * the active codepage, which only matches UTF-8 on hosts with ACP 65001 --
 * measured 2026-08-31: this exact mismatch made _stat64/FindFirstFileA
 * fail on non-ASCII names under a legacy ACP. Convert and use the W APIs
 * (same fix as runtime_core_exports.c). Malloc'd result, NULL on failure. */
static wchar_t* core_io_utf8_to_wide(const char* utf8) {
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

/* UTF-16 -> UTF-8 into buf; returns 0 when it does not fit. */
static int core_io_wide_to_utf8_buf(const wchar_t* wide, char* buf, size_t buf_size) {
    int len = WideCharToMultiByte(CP_UTF8, 0, wide, -1, buf, (int)buf_size, NULL, NULL);
    return len > 0;
}
#endif

/* Build a tagged [u8] array from raw bytes: rt_array_new + per-element
 * inline tagged ints (byte << 3), mirroring Rust rt_text_to_bytes. */
static int64_t core_io_bytes_to_array(const uint8_t* bytes, size_t len) {
    SplArray* arr = rt_array_new((int64_t)len);
    if (!arr) return (int64_t)(uintptr_t)rt_array_new(0);
    for (size_t i = 0; i < len; i++) {
        rt_array_push(arr, (int64_t)bytes[i] << 3);
    }
    return (int64_t)(uintptr_t)arr;
}

/* ==================================================================
 * Group F: stdin / terminal
 * ================================================================== */

#ifdef _WIN32
/* [u8] is a byte contract: switch stdin to binary once so the CRT does not
 * CRLF-translate or stop at Ctrl-Z. Idempotent; only the byte-read entry
 * points below trigger it (rt_stdin_read_line stays untouched). */
static void core_io_stdin_binary(void) {
    static int done = 0;
    if (!done) {
        _setmode(_fileno(stdin), _O_BINARY);
        done = 1;
    }
}
#endif

/* One-shot read of up to `size` bytes from stdin -> [u8].
 * Partial reads are contractual (Stdin.read_exact loops, 0 bytes = EOF). */
int64_t rt_stdin_read(int64_t size) {
    if (size <= 0) return (int64_t)(uintptr_t)rt_array_new(0);
    /* Cap a single request at 16 MiB so a corrupt size cannot OOM. */
    if (size > (int64_t)(16u * 1024u * 1024u)) size = (int64_t)(16u * 1024u * 1024u);
    uint8_t* buf = (uint8_t*)malloc((size_t)size);
    if (!buf) return (int64_t)(uintptr_t)rt_array_new(0);
#ifdef _WIN32
    core_io_stdin_binary();
    int n = _read(_fileno(stdin), buf, (unsigned int)size);
#else
    /* EINTR must not read as EOF: Stdin.read_exact (pipe.spl) treats a
     * 0-length chunk as end-of-stream, so a signal would truncate input. */
    ssize_t n;
    do {
        n = read(0, buf, (size_t)size);
    } while (n < 0 && errno == EINTR);
#endif
    int64_t result = (n > 0)
        ? core_io_bytes_to_array(buf, (size_t)n)
        : (int64_t)(uintptr_t)rt_array_new(0);
    free(buf);
    return result;
}

/* Read stdin to EOF -> [u8]. */
int64_t rt_stdin_read_all(void) {
    size_t cap = 65536, len = 0;
    uint8_t* buf = (uint8_t*)malloc(cap);
    if (!buf) return (int64_t)(uintptr_t)rt_array_new(0);
#ifdef _WIN32
    core_io_stdin_binary();
#endif
    for (;;) {
        if (len == cap) {
            cap *= 2;
            uint8_t* grown = (uint8_t*)realloc(buf, cap);
            if (!grown) break;
            buf = grown;
        }
#ifdef _WIN32
        int n = _read(_fileno(stdin), buf + len, (unsigned int)(cap - len));
#else
        ssize_t n = read(0, buf + len, cap - len);
        if (n < 0 && errno == EINTR) continue; /* signal, not EOF */
#endif
        if (n <= 0) break;
        len += (size_t)n;
    }
    int64_t result = core_io_bytes_to_array(buf, len);
    free(buf);
    return result;
}

/* Write text to the terminal (stdout); returns bytes written. */
int64_t rt_term_write(int64_t text_value) {
    int64_t len = rt_string_len(text_value);
    if (len <= 0) return 0;
    const uint8_t* data = rt_string_data(text_value);
    if (!data) return 0;
    size_t written = fwrite(data, 1, (size_t)len, stdout);
    return (int64_t)written;
}

/* Flush the terminal (stdout); 0 on success, -1 on error. */
int32_t rt_term_flush(void) {
    return fflush(stdout) == 0 ? 0 : -1;
}

/* ==================================================================
 * Group G: sffi io singles
 * ================================================================== */

/* st_mtime as whole seconds since the Unix epoch; -1 on failure. */
static int64_t core_io_mtime_seconds(const char* path) {
#ifdef _WIN32
    wchar_t* wpath = core_io_utf8_to_wide(path);
    if (!wpath) return -1;
    struct __stat64 st;
    int rc = _wstat64(wpath, &st);
    free(wpath);
    if (rc != 0) return -1;
    return (int64_t)st.st_mtime;
#else
    struct stat st;
    if (stat(path, &st) != 0) return -1;
    return (int64_t)st.st_mtime;
#endif
}

/* Deliberately the same contract as rt_file_modified_time (see header). */
int64_t rt_file_modified(int64_t path_value) {
    char path[4096];
    if (!core_io_text_arg(path_value, path, sizeof(path))) return -1;
    return core_io_mtime_seconds(path);
}

int64_t rt_file_modified_time(int64_t path_value) {
    char path[4096];
    if (!core_io_text_arg(path_value, path, sizeof(path))) return -1;
    return core_io_mtime_seconds(path);
}

/* Does `name` end with `suffix`? Empty suffix matches everything. */
static int core_io_has_suffix(const char* name, const char* suffix) {
    size_t nl = strlen(name), sl = strlen(suffix);
    if (sl == 0) return 1;
    if (nl < sl) return 0;
    return memcmp(name + (nl - sl), suffix, sl) == 0;
}

static void core_io_list_dir_impl(const char* path, const char* suffix, int64_t* result, int depth) {
    if (depth > 64) return; /* symlink-cycle / runaway-nesting guard */
#ifdef _WIN32
    char pattern[4096];
    if (snprintf(pattern, sizeof(pattern), "%s\\*", path) >= (int)sizeof(pattern)) return;
    wchar_t* wpattern = core_io_utf8_to_wide(pattern);
    if (!wpattern) return;
    WIN32_FIND_DATAW fd;
    HANDLE h = FindFirstFileW(wpattern, &fd);
    free(wpattern);
    if (h == INVALID_HANDLE_VALUE) return;
    do {
        if (wcscmp(fd.cFileName, L".") == 0 || wcscmp(fd.cFileName, L"..") == 0) continue;
        char name[1024];
        if (!core_io_wide_to_utf8_buf(fd.cFileName, name, sizeof(name))) continue;
        char full[4096];
        if (snprintf(full, sizeof(full), "%s\\%s", path, name) >= (int)sizeof(full)) continue;
        if ((fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            !(fd.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)) {
            core_io_list_dir_impl(full, suffix, result, depth + 1);
        } else if (core_io_has_suffix(name, suffix)) {
            rt_array_push((SplArray*)(uintptr_t)*result,
                          rt_string_new((const uint8_t*)full, (uint64_t)strlen(full)));
        }
    } while (FindNextFileW(h, &fd));
    FindClose(h);
#else
    DIR* dir = opendir(path);
    if (!dir) return;
    struct dirent* ent;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        char full[4096];
        /* Truncation would silently stat/emit the WRONG path -- skip. */
        if (snprintf(full, sizeof(full), "%s/%s", path, ent->d_name) >= (int)sizeof(full)) continue;
        struct stat st;
        if (lstat(full, &st) != 0) continue;
        if (S_ISDIR(st.st_mode)) {
            core_io_list_dir_impl(full, suffix, result, depth + 1);
        } else if (core_io_has_suffix(ent->d_name, suffix)) {
            rt_array_push((SplArray*)(uintptr_t)*result,
                          rt_string_new((const uint8_t*)full, (uint64_t)strlen(full)));
        }
    }
    closedir(dir);
#endif
}

/* Recursive file listing filtered by extension -> [text] of full paths.
 * `ext` may be "spl" or ".spl"; empty ext lists every file. */
int64_t rt_list_dir_recursive(int64_t path_value, int64_t ext_value) {
    int64_t result = (int64_t)(uintptr_t)rt_array_new(0);
    char path[4096];
    char ext[256];
    if (!core_io_text_arg(path_value, path, sizeof(path))) return result;
    if (!core_io_text_arg(ext_value, ext, sizeof(ext) - 1)) ext[0] = '\0';
    char suffix[260];
    if (ext[0] == '\0') {
        suffix[0] = '\0';
    } else if (ext[0] == '.') {
        snprintf(suffix, sizeof(suffix), "%s", ext);
    } else {
        snprintf(suffix, sizeof(suffix), ".%s", ext);
    }
    core_io_list_dir_impl(path, suffix, &result, 0);
    return result;
}

/* Lexical path normalization (no filesystem access): both separators
 * accepted, '/' emitted, duplicate separators collapsed, "." removed,
 * ".." folded against a preceding real segment only. */
int64_t rt_path_normalize(int64_t path_value) {
    char in[4096];
    if (!core_io_text_arg(path_value, in, sizeof(in))) return core_io_empty_text();
    size_t inlen = strlen(in);
    if (inlen == 0) return rt_string_new((const uint8_t*)".", 1);

    char out[4096];
    size_t pos = 0;
    size_t i = 0;

    /* Preserve a Windows drive prefix ("C:") verbatim. */
    if (inlen >= 2 && in[1] == ':' &&
        ((in[0] >= 'A' && in[0] <= 'Z') || (in[0] >= 'a' && in[0] <= 'z'))) {
        out[pos++] = in[0];
        out[pos++] = ':';
        i = 2;
    }
    int rooted = 0;
    if (in[i] == '/' || in[i] == '\\') {
        out[pos++] = '/';
        rooted = 1;
        while (in[i] == '/' || in[i] == '\\') i++;
    }
    size_t body_start = pos; /* first byte after prefix/root */

    while (in[i] != '\0') {
        /* take one segment */
        size_t seg_start = i;
        while (in[i] != '\0' && in[i] != '/' && in[i] != '\\') i++;
        size_t seg_len = i - seg_start;
        while (in[i] == '/' || in[i] == '\\') i++;

        if (seg_len == 0 || (seg_len == 1 && in[seg_start] == '.')) continue;
        if (seg_len == 2 && in[seg_start] == '.' && in[seg_start + 1] == '.') {
            /* pop the previous segment if it exists and is not itself ".." */
            if (pos > body_start) {
                size_t j = pos;
                if (j > body_start && out[j - 1] == '/') j--;
                size_t prev_end = j;
                while (j > body_start && out[j - 1] != '/') j--;
                if (!(prev_end - j == 2 && out[j] == '.' && out[j + 1] == '.')) {
                    pos = j;
                    continue;
                }
            } else if (rooted) {
                continue; /* "/.." stays at root */
            }
            /* fall through: keep a leading/stacked ".." */
        }
        if (pos > body_start && out[pos - 1] != '/') out[pos++] = '/';
        if (pos + seg_len >= sizeof(out)) return core_io_empty_text();
        memcpy(out + pos, in + seg_start, seg_len);
        pos += seg_len;
    }

    /* strip one trailing separator left by a pop, unless it IS the root */
    if (pos > body_start && out[pos - 1] == '/') pos--;
    if (pos == 0) return rt_string_new((const uint8_t*)".", 1);
    return rt_string_new((const uint8_t*)out, (uint64_t)pos);
}

/* ==================================================================
 * Group I (rest): system singles
 * ================================================================== */

/* Run cmd through the platform shell; return its exit code, -1 on failure
 * (shell unavailable, launch failure, or child killed by a signal). */
int64_t rt_shell(int64_t cmd_value) {
    char* cmd = core_io_text_arg_dup(cmd_value);
    if (!cmd) return -1;
    int rc = system(cmd);
    free(cmd);
#ifdef _WIN32
    return (int64_t)rc; /* cmd.exe exit code; -1 already means failure */
#else
    if (rc == -1) return -1;
    if (WIFEXITED(rc)) return (int64_t)WEXITSTATUS(rc);
    return -1;
#endif
}

/* Append src to a growing buffer; returns 0 on OOM (buffer freed). */
static int core_io_buf_append(char** buf, size_t* len, size_t* cap,
                              const char* src, size_t n) {
    while (*len + n + 1 > *cap) {
        *cap *= 2;
        char* grown = (char*)realloc(*buf, *cap);
        if (!grown) { free(*buf); *buf = NULL; return 0; }
        *buf = grown;
    }
    memcpy(*buf + *len, src, n);
    *len += n;
    (*buf)[*len] = '\0';
    return 1;
}

/* Run `cmd` with `args`, capture stdout -> text; empty text on failure
 * (the declared ABI conflates the two -- see header). Args are wrapped in
 * double quotes with embedded quotes backslash-escaped; best-effort on
 * cmd.exe, whose quoting rules are inherently lossy. */
int64_t rt_process_output(int64_t cmd_value, int64_t args_value) {
    char* cmd = core_io_text_arg_dup(cmd_value);
    if (!cmd) return core_io_empty_text();

    size_t cap = 4096, len = 0;
    char* line = (char*)malloc(cap);
    if (!line) { free(cmd); return core_io_empty_text(); }
    line[0] = '\0';
    if (!core_io_buf_append(&line, &len, &cap, cmd, strlen(cmd))) {
        free(cmd);
        return core_io_empty_text();
    }
    free(cmd);

    int64_t argc = rt_array_len_safe(args_value);
    for (int64_t idx = 0; idx < argc; idx++) {
        int64_t arg_value = rt_array_get((SplArray*)(uintptr_t)args_value, idx);
        int64_t alen = rt_string_len(arg_value);
        const uint8_t* adata = rt_string_data(arg_value);
        if (alen < 0 || (!adata && alen != 0)) continue;
        if (!core_io_buf_append(&line, &len, &cap, " \"", 2)) return core_io_empty_text();
        for (int64_t b = 0; b < alen; b++) {
            char c = (char)adata[b];
            if (c == '"' || c == '\\') {
                char esc[2] = { '\\', c };
                if (!core_io_buf_append(&line, &len, &cap, esc, 2)) return core_io_empty_text();
            } else {
                if (!core_io_buf_append(&line, &len, &cap, &c, 1)) return core_io_empty_text();
            }
        }
        if (!core_io_buf_append(&line, &len, &cap, "\"", 1)) return core_io_empty_text();
    }

#ifdef _WIN32
    FILE* pipe = _popen(line, "r");
#else
    FILE* pipe = popen(line, "r");
#endif
    free(line);
    if (!pipe) return core_io_empty_text();

    size_t ocap = 4096, olen = 0;
    char* out = (char*)malloc(ocap);
    if (!out) {
#ifdef _WIN32
        _pclose(pipe);
#else
        pclose(pipe);
#endif
        return core_io_empty_text();
    }
    char tmp[4096];
    size_t n;
    while ((n = fread(tmp, 1, sizeof(tmp), pipe)) > 0) {
        if (!core_io_buf_append(&out, &olen, &ocap, tmp, n)) {
#ifdef _WIN32
            _pclose(pipe);
#else
            pclose(pipe);
#endif
            return core_io_empty_text();
        }
    }
#ifdef _WIN32
    _pclose(pipe);
#else
    pclose(pipe);
#endif
    int64_t result = rt_string_new((const uint8_t*)out, (uint64_t)olen);
    free(out);
    return result;
}

/* ==================================================================
 * Group J: string <-> byte array
 * ================================================================== */

/* Mirror of Rust rt_text_to_bytes: text -> [u8] of inline tagged ints. */
int64_t rt_string_to_byte_array(int64_t text_value) {
    int64_t len = rt_string_len(text_value);
    const uint8_t* data = rt_string_data(text_value);
    if (len <= 0 || !data) return (int64_t)(uintptr_t)rt_array_new(0);
    return core_io_bytes_to_array(data, (size_t)len);
}

/* Mirror of Rust rt_bytes_to_text (aliased to this name by the
 * interpreter): [u8] -> text. Any non-int element or byte outside 0..255
 * fails to empty text (facade convention; Rust returns NIL, which a
 * non-optional `text` cannot carry safely). */
int64_t rt_string_from_byte_array(int64_t array_value) {
    int64_t len = rt_array_len_safe(array_value);
    if (len <= 0) return core_io_empty_text();
    uint8_t* buf = (uint8_t*)malloc((size_t)len);
    if (!buf) return core_io_empty_text();
    for (int64_t i = 0; i < len; i++) {
        int64_t v = rt_array_get((SplArray*)(uintptr_t)array_value, i);
        if ((v & 7) != 0) { free(buf); return core_io_empty_text(); }
        int64_t byte = v >> 3; /* arithmetic shift undoes the inline tag */
        if (byte < 0 || byte > 255) { free(buf); return core_io_empty_text(); }
        buf[i] = (uint8_t)byte;
    }
    int64_t result = rt_string_new(buf, (uint64_t)len);
    free(buf);
    return result;
}
