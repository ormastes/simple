/* Focused C selfcheck for rt_lexer_source_set / rt_lexer_source_slice
 * (ASCII fast path + forward/backward/random UTF-8 cursor memoization),
 * rt_file_read_bytes (failure cleanup, binary NUL preservation, missing/empty),
 * and rt_file_read_text (quiet on missing file unless SIMPLE_RT_FILE_READ_TEXT_DIAG=1).
 *
 * Standalone build:
 *   clang -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *     -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -Isrc/runtime -Isrc/runtime/platform \
 *     src/runtime/test/rt_lexer_slice_and_file_read_selfcheck.c
 */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#if defined(_WIN32) && (!defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0602)
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0602
#endif
#if defined(_WIN32)
#include <winsock2.h>
#include <ws2tcpip.h>
#endif
#include <stdio.h>
#include <stddef.h>

static int g_fail_next_fread = 0;
static size_t test_hook_fread(void* ptr, size_t size, size_t count, FILE* stream) {
    if (g_fail_next_fread) {
        g_fail_next_fread = 0;
        return 0;
    }
    return fread(ptr, size, count, stream);
}
#define fread(p, s, n, f) test_hook_fread((p), (s), (n), (f))
#include "../runtime_native.c"
#undef fread

#ifndef SIMPLE_TEST_CORE_RUNTIME
void spl_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg ? msg : "");
    exit(101);
}
#endif
int64_t rt_text_slice_audit_level(void) { return 0; }
int64_t rt_text_slice_audit_note(int site_id, const char* site_name, int64_t start, int64_t end,
                                 const uint8_t* src, uint64_t src_len, const uint8_t* out, uint64_t out_len) {
    (void)site_id; (void)site_name; (void)start; (void)end;
    (void)src; (void)src_len; (void)out; (void)out_len;
    return 0;
}

static unsigned g_checks = 0;
static unsigned g_failures = 0;

#define CHECK(cond) do { \
    ++g_checks; \
    if (!(cond)) { \
        ++g_failures; \
        fprintf(stderr, "FAIL line=%d check=%u: %s\n", __LINE__, g_checks, #cond); \
    } \
} while (0)

static int text_equals_bytes(int64_t v, const char* want, size_t want_len) {
    int64_t n = rt_string_len(v);
    const uint8_t* d = rt_string_data(v);
    if (n != (int64_t)want_len) return 0;
    if (want_len == 0) return 1;
    return d != NULL && memcmp(d, want, want_len) == 0;
}

static int text_equals_cstr(int64_t v, const char* want) {
    return text_equals_bytes(v, want, strlen(want));
}

static void make_temp_path(char* out, size_t cap, const char* tag) {
#if defined(_WIN32)
    char dir[MAX_PATH];
    DWORD len = GetTempPathA((DWORD)sizeof(dir), dir);
    CHECK(len > 0 && len < sizeof(dir));
    UINT n = GetTempFileNameA(dir, tag, 0, out);
    CHECK(n != 0);
    (void)cap;
#else
    snprintf(out, cap, "/tmp/%s_XXXXXX", tag);
    int fd = mkstemp(out);
    CHECK(fd >= 0);
    if (fd >= 0) close(fd);
#endif
}

static void set_env_val(const char* name, const char* val) {
#if defined(_WIN32)
    _putenv_s(name, val ? val : "");
#else
    if (val) setenv(name, val, 1);
    else unsetenv(name);
#endif
}

static void test_lexer_source_slicing(void) {
    /* Invalid and empty source handling */
    CHECK(!rt_lexer_source_set(NULL, 5));
    CHECK(rt_lexer_source_set(NULL, 0));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 0), ""));
    CHECK(rt_lexer_source_slice(0, 1) == rt_core_nil());
    CHECK(rt_lexer_source_slice(-1, 0) == rt_core_nil());
    CHECK(rt_lexer_source_slice(2, 1) == rt_core_nil());

    /* ASCII fast path */
    const char* ascii_src = "fn main():\n    val x = 12345\n    x + 1\n";
    size_t ascii_len = strlen(ascii_src);
    CHECK(rt_lexer_source_set((const uint8_t*)ascii_src, (uint64_t)ascii_len));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 2), "fn"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(3, 7), "main"));
    CHECK(text_equals_cstr(rt_lexer_source_slice((int64_t)ascii_len - 6, (int64_t)ascii_len), "x + 1\n"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(15, 20), "val x"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 0), ""));
    CHECK(rt_lexer_source_slice((int64_t)ascii_len, (int64_t)ascii_len + 1) == rt_core_nil());

    /* Large ASCII sweep: sequential forward + backward */
    enum { ASCII_N = 8192 };
    char big_ascii[ASCII_N + 1];
    for (int i = 0; i < ASCII_N; i++) {
        big_ascii[i] = (char)('a' + (i % 26));
    }
    big_ascii[ASCII_N] = '\0';
    CHECK(rt_lexer_source_set((const uint8_t*)big_ascii, ASCII_N));
    for (int i = 0; i < ASCII_N; i += 97) {
        char expect_ch[2] = { big_ascii[i], '\0' };
        CHECK(text_equals_cstr(rt_lexer_source_slice(i, i + 1), expect_ch));
    }
    for (int i = ASCII_N - 1; i >= 0; i -= 131) {
        char expect_ch[2] = { big_ascii[i], '\0' };
        CHECK(text_equals_cstr(rt_lexer_source_slice(i, i + 1), expect_ch));
    }

    /* UTF-8 multi-byte codepoints (1, 2, 3, 4 byte UTF-8) */
    const char* unit = "a\xC3\xA9\xE4\xB8\xAD\xF0\x9F\x98\x80z"; /* 5 code points, 11 bytes */
    const int64_t unit_cps = 5;
    enum { REPS = 600 };
    size_t unit_len = strlen(unit);
    size_t utf_len = unit_len * REPS;
    char* utf_buf = (char*)malloc(utf_len + 1);
    CHECK(utf_buf != NULL);
    for (int r = 0; r < REPS; r++) {
        memcpy(utf_buf + (size_t)r * unit_len, unit, unit_len);
    }
    utf_buf[utf_len] = '\0';

    CHECK(rt_lexer_source_set((const uint8_t*)utf_buf, (uint64_t)utf_len));
    int64_t total_cps = unit_cps * REPS;

    /* Forward sequential scan across all code points */
    for (int64_t cp = 0; cp < total_cps; cp++) {
        int64_t mod = cp % unit_cps;
        const char* expected =
            mod == 0 ? "a" :
            mod == 1 ? "\xC3\xA9" :
            mod == 2 ? "\xE4\xB8\xAD" :
            mod == 3 ? "\xF0\x9F\x98\x80" : "z";
        int64_t s = rt_lexer_source_slice(cp, cp + 1);
        if (!text_equals_cstr(s, expected)) {
            CHECK(0);
            break;
        }
    }

    /* Backward sequential scan from end down to 0 */
    for (int64_t cp = total_cps - 1; cp >= 0; cp--) {
        int64_t mod = cp % unit_cps;
        const char* expected =
            mod == 0 ? "a" :
            mod == 1 ? "\xC3\xA9" :
            mod == 2 ? "\xE4\xB8\xAD" :
            mod == 3 ? "\xF0\x9F\x98\x80" : "z";
        int64_t s = rt_lexer_source_slice(cp, cp + 1);
        if (!text_equals_cstr(s, expected)) {
            CHECK(0);
            break;
        }
    }

    /* Random jumps: forward, small backward, large backward to near 0, repeat */
    const int64_t jump_starts[] = {
        2500, 2496, 2501, 5, 2995, 2990, 2990, 12, 1500, 1495, 0, total_cps
    };
    for (size_t j = 0; j < sizeof(jump_starts) / sizeof(jump_starts[0]); j++) {
        int64_t pos = jump_starts[j];
        if (pos == total_cps) {
            CHECK(text_equals_cstr(rt_lexer_source_slice(pos, pos), ""));
            CHECK(rt_lexer_source_slice(pos, pos + 1) == rt_core_nil());
        } else {
            int64_t end = pos + unit_cps <= total_cps ? pos + unit_cps : total_cps;
            if (pos % unit_cps == 0 && end == pos + unit_cps) {
                CHECK(text_equals_cstr(rt_lexer_source_slice(pos, end), unit));
            } else {
                int64_t mod = pos % unit_cps;
                const char* expected =
                    mod == 0 ? "a" :
                    mod == 1 ? "\xC3\xA9" :
                    mod == 2 ? "\xE4\xB8\xAD" :
                    mod == 3 ? "\xF0\x9F\x98\x80" : "z";
                CHECK(text_equals_cstr(rt_lexer_source_slice(pos, pos + 1), expected));
            }
        }
    }

    /* Stray leading continuation byte matches original scanner semantics */
    const uint8_t stray[] = { 0x80, 'x', 'y' };
    CHECK(rt_lexer_source_set(stray, sizeof(stray)));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 1), "x"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(1, 2), "y"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 2), "xy"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(1, 2), "y"));
    CHECK(text_equals_cstr(rt_lexer_source_slice(0, 1), "x"));

    /* Switching back to ASCII after UTF-8 resets state properly */
    CHECK(rt_lexer_source_set((const uint8_t*)"hello", 5));
    CHECK(text_equals_cstr(rt_lexer_source_slice(1, 4), "ell"));

    free(utf_buf);
}

static void test_file_read_bytes(void) {
    /* Missing file -> nil */
    const char* missing = "C:/nonexistent_wave2_g6_probe_file_404.bin";
    CHECK(rt_file_read_bytes((const uint8_t*)missing, strlen(missing)) == rt_core_nil());

    /* Empty file -> empty [u8] */
    char empty_path[512];
    make_temp_path(empty_path, sizeof(empty_path), "g6e");
    int64_t empty_val = rt_file_read_bytes((const uint8_t*)empty_path, strlen(empty_path));
    CHECK(empty_val != rt_core_nil());
    CHECK(rt_array_len((SplArray*)(uintptr_t)empty_val) == 0);
    rt_array_free((SplArray*)(uintptr_t)empty_val);

    /* Binary file with embedded NULs */
    char bin_path[512];
    make_temp_path(bin_path, sizeof(bin_path), "g6b");
    const uint8_t payload[] = { 'A', 0x00, 'B', 0xFF, 0x00, 'C', 0x7F, 0x80, 'Z' };
    FILE* wf = fopen(bin_path, "wb");
    CHECK(wf != NULL);
    if (wf) {
        CHECK(fwrite(payload, 1, sizeof(payload), wf) == sizeof(payload));
        fclose(wf);
    }

    int64_t bytes_val = rt_file_read_bytes((const uint8_t*)bin_path, strlen(bin_path));
    CHECK(bytes_val != rt_core_nil());
    SplArray* arr = (SplArray*)(uintptr_t)bytes_val;
    CHECK(rt_array_len(arr) == (int64_t)sizeof(payload));
    for (size_t i = 0; i < sizeof(payload); i++) {
        CHECK(rt_array_get(arr, (int64_t)i) == (int64_t)payload[i]);
    }
    rt_array_free(arr);

    /* Read failure after allocation must free & unregister result (zero aux-byte leak) */
    int64_t aux_before = atomic_load_explicit(&g_core_aux_live_bytes, memory_order_relaxed);
    g_fail_next_fread = 1;
    int64_t failed_val = rt_file_read_bytes((const uint8_t*)bin_path, strlen(bin_path));
    int64_t aux_after = atomic_load_explicit(&g_core_aux_live_bytes, memory_order_relaxed);
    CHECK(failed_val == rt_core_nil());
    CHECK(aux_after == aux_before);

    remove(empty_path);
    remove(bin_path);
}

static void test_file_read_text_diag_gated(void) {
    char capture_path[512];
    make_temp_path(capture_path, sizeof(capture_path), "g6d");

    const char* missing = "/tmp/nonexistent_wave2_g6_missing_text_probe.spl";

    /* Default (unset): missing-file probe must emit zero stderr diagnostic bytes */
    set_env_val("SIMPLE_RT_FILE_READ_TEXT_DIAG", NULL);
    fflush(stderr);
#if defined(_WIN32)
    int saved_fd = _dup(_fileno(stderr));
#else
    int saved_fd = dup(fileno(stderr));
#endif
    CHECK(saved_fd >= 0);
    FILE* redir = freopen(capture_path, "wb", stderr);
    CHECK(redir != NULL);

    int64_t r1 = rt_file_read_text((const uint8_t*)missing, (uint64_t)strlen(missing));
    fflush(stderr);

#if defined(_WIN32)
    _dup2(saved_fd, _fileno(stderr));
    _close(saved_fd);
#else
    dup2(saved_fd, fileno(stderr));
    close(saved_fd);
#endif
    clearerr(stderr);
    CHECK(r1 == rt_core_nil());

    FILE* rf = fopen(capture_path, "rb");
    CHECK(rf != NULL);
    char buf[512];
    size_t got = rf ? fread(buf, 1, sizeof(buf) - 1, rf) : 0;
    if (rf) fclose(rf);
    buf[got] = '\0';
    CHECK(got == 0);

    /* Explicit SIMPLE_RT_FILE_READ_TEXT_DIAG=1 emits [rt_file_read_text-diag] */
    set_env_val("SIMPLE_RT_FILE_READ_TEXT_DIAG", "1");
    fflush(stderr);
#if defined(_WIN32)
    saved_fd = _dup(_fileno(stderr));
#else
    saved_fd = dup(fileno(stderr));
#endif
    CHECK(saved_fd >= 0);
    redir = freopen(capture_path, "wb", stderr);
    CHECK(redir != NULL);

    int64_t r2 = rt_file_read_text((const uint8_t*)missing, (uint64_t)strlen(missing));
    fflush(stderr);

#if defined(_WIN32)
    _dup2(saved_fd, _fileno(stderr));
    _close(saved_fd);
#else
    dup2(saved_fd, fileno(stderr));
    close(saved_fd);
#endif
    clearerr(stderr);
    set_env_val("SIMPLE_RT_FILE_READ_TEXT_DIAG", NULL);
    CHECK(r2 == rt_core_nil());

    rf = fopen(capture_path, "rb");
    CHECK(rf != NULL);
    got = rf ? fread(buf, 1, sizeof(buf) - 1, rf) : 0;
    if (rf) fclose(rf);
    buf[got] = '\0';
    CHECK(got > 0);
    CHECK(strstr(buf, "[rt_file_read_text-diag]") != NULL);

    remove(capture_path);
}

int main(void) {
    test_lexer_source_slicing();
    test_file_read_bytes();
    test_file_read_text_diag_gated();
    if (g_failures > 0) {
        fprintf(stderr, "FAIL: %u/%u checks failed\n", g_failures, g_checks);
        return 1;
    }
    printf("PASS: %u checks passed\n", g_checks);
    return 0;
}
