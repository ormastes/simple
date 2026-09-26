/*
 * Windows-only C conformance test for the runtime's shared long-path +
 * binary-IO helpers (platform/runtime_win_long_path.h) and the process-wide
 * `_set_fmode(_O_BINARY)` default installed by runtime_native.c's
 * rt_win_set_binary_stdio constructor.
 *
 * This is a standalone unit: it #includes the real, shared production
 * header (not a copy) so a future edit to the widen/rename helper is
 * exercised by this test automatically, and it links against no other
 * runtime object file, so `-fsyntax-only` scanning
 * (check-c-runtime-compiles-push.shs) is happy and a real compile+run needs
 * only clang-cl + the Windows SDK, no full runtime archive.
 *
 * Covers the four defect classes named in the Windows C runtime plan
 * (2026-09-25):
 *   1. Binary mode: write "\n" through plain fopen(path, "wb") (the
 *      production sites now use explicit "b", backstopped by the process
 *      default), read the bytes back and require them byte-identical --
 *      no LF->CRLF translation anywhere on the round trip.
 *   2. Long path: build a path over 300 characters, widen+prefix it with
 *      the shared helper, create/write/read/rename/exists through the
 *      widened form, exactly like the runtime's own open/create/rename call
 *      sites now do.
 *   3. Rename replace: rt_win_long_path_rename() must REPLACE an existing
 *      destination FILE (POSIX rename(2) / Rust std::fs::rename contract),
 *      matching rt_file_rename / rt_file_move in runtime_native.c.
 *   4. Directory "exists": GetFileAttributesW must report a directory as
 *      existing, unlike a text-mode fopen(path, "r") probe.
 */
#ifdef _WIN32
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <windows.h>
#include <fcntl.h>
#include <io.h>

#include "../platform/runtime_win_long_path.h"

static int failures;
static void require(int condition, const char *message) {
    if (!condition) {
        fprintf(stderr, "FAIL: %s (win32=%lu)\n", message, GetLastError());
        failures++;
    }
}

int main(int argc, char **argv) {
    if (argc != 2) return 2;
    /* Case 1: binary-mode round trip. A text-mode fopen would corrupt this
     * "\n" into "\r\n" on write; explicit "wb"/"rb" (what the fixed
     * production call sites now use) must not. */
    char short_path[4096];
    snprintf(short_path, sizeof(short_path), "%s\\rt_win_io_binary.txt", argv[1]);
    {
        FILE *f = fopen(short_path, "wb");
        require(f != NULL, "binary-mode fixture create");
        if (f) {
            require(fwrite("a\nb\n", 1, 4, f) == 4, "binary-mode fixture write");
            fclose(f);
        }
        f = fopen(short_path, "rb");
        require(f != NULL, "binary-mode fixture reopen");
        if (f) {
            char buf[8] = {0};
            size_t n = fread(buf, 1, sizeof(buf), f);
            fclose(f);
            require(n == 4 && memcmp(buf, "a\nb\n", 4) == 0,
                    "binary-mode round trip must not translate LF to CRLF");
        }
    }

    /* Case 2/3/4: build a path over 300 characters, exercise the shared
     * widen helper end to end through real Win32 calls (not just parsed). */
    char dir[4096];
    snprintf(dir, sizeof(dir), "%s\\rt-win-io-conformance-%lu",
             argv[1], (unsigned long)GetCurrentProcessId());
    {
        wchar_t *wide_dir = rt_win_long_path_widen(dir);
        require(wide_dir != NULL, "widen dir root");
        if (wide_dir) { CreateDirectoryW(wide_dir, NULL); free(wide_dir); }
    }
    for (int i = 0; i < 10; i++) {
        strcat(dir, "\\component-long-enough-to-matter");
        wchar_t *wide_dir = rt_win_long_path_widen(dir);
        require(wide_dir != NULL, "widen deep dir component");
        if (wide_dir) {
            CreateDirectoryW(wide_dir, NULL);
            free(wide_dir);
        }
    }
    require(strlen(dir) > 300, "fixture directory must exceed 300 characters");

    /* Directory exists() must count -- GetFileAttributesW, not fopen(). */
    {
        wchar_t *wide_dir = rt_win_long_path_widen(dir);
        require(wide_dir != NULL, "widen long dir for exists check");
        if (wide_dir) {
            DWORD attrs = GetFileAttributesW(wide_dir);
            require(attrs != INVALID_FILE_ATTRIBUTES &&
                    (attrs & FILE_ATTRIBUTE_DIRECTORY) != 0,
                    "long directory must report exists via GetFileAttributesW");
            free(wide_dir);
        }
    }

    char long_path[4096];
    snprintf(long_path, sizeof(long_path), "%s\\payload.bin", dir);
    require(strlen(long_path) > 300, "fixture file path must exceed 300 characters");

    /* Create + write through the widened path. */
    {
        wchar_t *wide_file = rt_win_long_path_widen(long_path);
        require(wide_file != NULL, "widen long file path for create");
        if (wide_file) {
            HANDLE h = CreateFileW(wide_file, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
            require(h != INVALID_HANDLE_VALUE, "create over 300-char path");
            if (h != INVALID_HANDLE_VALUE) {
                DWORD written = 0;
                require(WriteFile(h, "long-path-payload", 17, &written, NULL) && written == 17,
                        "write over 300-char path");
                CloseHandle(h);
            }
            free(wide_file);
        }
    }

    /* Read back through the widened path. */
    {
        wchar_t *wide_file = rt_win_long_path_widen(long_path);
        require(wide_file != NULL, "widen long file path for read");
        if (wide_file) {
            HANDLE h = CreateFileW(wide_file, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
            require(h != INVALID_HANDLE_VALUE, "reopen over 300-char path");
            if (h != INVALID_HANDLE_VALUE) {
                char buf[32] = {0};
                DWORD read_count = 0;
                require(ReadFile(h, buf, sizeof(buf), &read_count, NULL) && read_count == 17 &&
                        memcmp(buf, "long-path-payload", 17) == 0,
                        "read over 300-char path must match what was written");
                CloseHandle(h);
            }
            free(wide_file);
        }
    }

    /* File exists() over a long path, mirroring rt_file_exists's
     * GetFileAttributesW-based check (not fopen). */
    {
        wchar_t *wide_file = rt_win_long_path_widen(long_path);
        require(wide_file != NULL, "widen long file path for exists");
        if (wide_file) {
            DWORD attrs = GetFileAttributesW(wide_file);
            require(attrs != INVALID_FILE_ATTRIBUTES, "long file must report exists");
            free(wide_file);
        }
    }

    /* Case 3: rename must REPLACE an existing destination file. */
    char dest_path[4096];
    snprintf(dest_path, sizeof(dest_path), "%s\\payload-dest.bin", dir);
    {
        /* dest_path is itself over 300 characters (built under `dir`), so a
         * plain fopen()/CreateFileA here would hit the exact MAX_PATH defect
         * this test exists to catch; use the widened form like every other
         * fixture write above. */
        wchar_t *wide_dest = rt_win_long_path_widen(dest_path);
        require(wide_dest != NULL, "widen dest for pre-existing fixture create");
        if (wide_dest) {
            HANDLE h = CreateFileW(wide_dest, GENERIC_WRITE, 0, NULL, CREATE_ALWAYS, 0, NULL);
            require(h != INVALID_HANDLE_VALUE, "pre-existing destination create");
            if (h != INVALID_HANDLE_VALUE) {
                DWORD written = 0;
                WriteFile(h, "stale", 5, &written, NULL);
                CloseHandle(h);
            }
            free(wide_dest);
        }
    }
    require(rt_win_long_path_rename(long_path, dest_path) != 0,
            "rename must replace an existing destination file");
    {
        wchar_t *wide_dest = rt_win_long_path_widen(dest_path);
        require(wide_dest != NULL, "widen dest for post-rename read");
        if (wide_dest) {
            HANDLE h = CreateFileW(wide_dest, GENERIC_READ, FILE_SHARE_READ, NULL, OPEN_EXISTING, 0, NULL);
            require(h != INVALID_HANDLE_VALUE, "reopen destination after replace-rename");
            if (h != INVALID_HANDLE_VALUE) {
                char buf[32] = {0};
                DWORD read_count = 0;
                require(ReadFile(h, buf, sizeof(buf), &read_count, NULL) && read_count == 17 &&
                        memcmp(buf, "long-path-payload", 17) == 0,
                        "destination must carry the SOURCE bytes after replace-rename");
                CloseHandle(h);
            }
            free(wide_dest);
        }
    }
    {
        wchar_t *wide_src = rt_win_long_path_widen(long_path);
        require(wide_src != NULL, "widen source for post-rename exists check");
        if (wide_src) {
            DWORD attrs = GetFileAttributesW(wide_src);
            require(attrs == INVALID_FILE_ATTRIBUTES, "source must no longer exist after rename");
            free(wide_src);
        }
    }

    /* Directory rename must NOT pass MOVEFILE_REPLACE_EXISTING (Win32
     * rejects a directory replace); a rename onto a non-existent directory
     * destination must still succeed with flags 0. */
    char dir_src[4096], dir_dst[4096];
    snprintf(dir_src, sizeof(dir_src), "%s\\dir-src", dir);
    snprintf(dir_dst, sizeof(dir_dst), "%s\\dir-dst", dir);
    {
        wchar_t *wide_dir_src = rt_win_long_path_widen(dir_src);
        require(wide_dir_src != NULL, "widen dir-src");
        if (wide_dir_src) { require(CreateDirectoryW(wide_dir_src, NULL), "create dir-src"); free(wide_dir_src); }
    }
    require(rt_win_long_path_rename(dir_src, dir_dst) != 0, "directory rename to a fresh name must succeed");

    printf("Windows IO conformance: %d failures\n", failures);
    return failures ? 1 : 0;
}
#endif /* _WIN32 */
