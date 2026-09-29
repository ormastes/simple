/*
 * Behavioural selfcheck for the 19 core-C export symbols in
 * runtime_core_exports.c (Group E) and runtime_core_io_exports.c
 * (Groups F/G/I/J) -- the Stage 2 Windows unresolved-symbol fix.
 *
 * Build (MSYS2 mingw64, from repo root):
 *   gcc -std=c99 -Wall -I src/runtime \
 *       src/runtime/test/rt_core_exports_behaviour_selfcheck.c \
 *       src/runtime/runtime_core_exports.c \
 *       src/runtime/runtime_core_io_exports.c \
 *       -o build/rt_core_exports_selfcheck.exe
 *
 * The driver provides SHIM implementations of the tagged string/array API
 * (rt_string_new/len/data, rt_array_new/push/get/len_safe) faithful to the
 * runtime.h contract. This is deliberate: the functions under test treat
 * those values as opaque handles (verified -- neither TU dereferences
 * SplArray fields directly), so the shims exercise the TU logic while the
 * real ABI conformance is pinned by the tagged-value conventions checked
 * statically against text_extern_abi.spl / codegen/instr/calls.rs.
 * The [u8] inline-int tag (byte << 3) is round-tripped verbatim through the
 * shims and decoded with >> 3 in the assertions, so a tagging mistake in
 * the TUs would still fail here.
 *
 * Subcommands (fresh process per stdin case -- core_io_stdin_binary is a
 * one-shot static):
 *   core            all non-stdin tests (default)
 *   stdin_read N    rt_stdin_read(N), hex dump to stdout
 *   stdin_read_all  rt_stdin_read_all(), hex dump to stdout
 *   term            rt_term_write + rt_term_flush; bytes to stdout,
 *                   return values on stderr
 */

#include "runtime.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef _WIN32
#include <direct.h>
#include <windows.h>
#else
#include <sys/stat.h>
#include <unistd.h>
#endif

/* ===== shims: memtrack ===== */
int g_memtrack_enabled = 0;
void spl_memtrack_record(void* ptr, int64_t size, const char* tag) {
    (void)ptr; (void)size; (void)tag;
}
void spl_memtrack_unrecord(void* ptr) { (void)ptr; }

/* ===== shims: tagged text ===== */
typedef struct {
    int64_t len;
    uint8_t* data;
} ShimStr;

int64_t rt_string_new(const uint8_t* bytes, uint64_t len) {
    ShimStr* s = (ShimStr*)malloc(sizeof(ShimStr));
    if (!s) return 0;
    s->len = (int64_t)len;
    s->data = (uint8_t*)malloc(len ? len : 1);
    if (!s->data) { free(s); return 0; }
    if (len && bytes) memcpy(s->data, bytes, len);
    return (int64_t)(uintptr_t)s;
}

int64_t rt_string_len(int64_t string) {
    if (!string) return -1;
    return ((ShimStr*)(uintptr_t)string)->len;
}

const uint8_t* rt_string_data(int64_t string) {
    if (!string) return NULL;
    return ((ShimStr*)(uintptr_t)string)->data;
}

/* ===== shims: tagged array (runtime.h SplArray layout) ===== */
SplArray* rt_array_new(int64_t cap) {
    SplArray* a = (SplArray*)malloc(sizeof(SplArray));
    if (!a) return NULL;
    if (cap < 1) cap = 1;
    a->items = (SplValue*)malloc(sizeof(SplValue) * (size_t)cap);
    if (!a->items) { free(a); return NULL; }
    a->len = 0;
    a->cap = cap;
    return a;
}

int8_t rt_array_push(SplArray* array, int64_t value) {
    if (!array) return 0;
    if (array->len >= array->cap) {
        int64_t ncap = array->cap * 2;
        SplValue* grown = (SplValue*)realloc(array->items, sizeof(SplValue) * (size_t)ncap);
        if (!grown) return 0;
        array->items = grown;
        array->cap = ncap;
    }
    SplValue v;
    v.tag = SPL_INT;
    v.as_int = value; /* round-trip verbatim: preserves the <<3 inline tag */
    array->items[array->len++] = v;
    return 1;
}

int64_t rt_array_len_safe(int64_t value) {
    if (!value) return 0;
    return ((SplArray*)(uintptr_t)value)->len;
}

int64_t rt_array_get(SplArray* array, int64_t idx) {
    if (!array || idx < 0 || idx >= array->len) return 0;
    return array->items[idx].as_int;
}

/* ===== symbols under test (tagged ABI; see the two TUs) ===== */
int64_t rt_readdir(int64_t path_value);
int64_t rt_readdir_count(int64_t handle);
int64_t rt_readdir_entry(int64_t handle, int64_t index);
void rt_readdir_free(int64_t handle);
int64_t rt_mkdir(int64_t path_value, int64_t mode);
int64_t rt_random_i64(void);
/* rt_shell_output: declared in runtime.h */
int64_t rt_stdin_read(int64_t size);
int64_t rt_stdin_read_all(void);
int64_t rt_term_write(int64_t text_value);
int32_t rt_term_flush(void);
int64_t rt_file_modified(int64_t path_value);
int64_t rt_file_modified_time(int64_t path_value);
int64_t rt_list_dir_recursive(int64_t path_value, int64_t ext_value);
int64_t rt_path_normalize(int64_t path_value);
int64_t rt_shell(int64_t cmd_value);
int64_t rt_process_output(int64_t cmd_value, int64_t args_value);
int64_t rt_string_to_byte_array(int64_t text_value);
int64_t rt_string_from_byte_array(int64_t array_value);

/* ===== tiny harness ===== */
static int g_fail = 0;
static int g_pass = 0;

static int64_t mk_text(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

/* NUL-terminated copy of a tagged text into a static buffer for printing. */
static const char* text_cstr(int64_t v) {
    static char buf[8192];
    int64_t len = rt_string_len(v);
    if (len < 0 || len >= (int64_t)sizeof(buf)) return "<bad-text>";
    const uint8_t* d = rt_string_data(v);
    if (len && !d) return "<null-data>";
    if (len) memcpy(buf, d, (size_t)len);
    buf[len] = '\0';
    return buf;
}

static void ok(const char* name) {
    g_pass++;
    printf("PASS %s\n", name);
}

static void fail(const char* name, const char* detail) {
    g_fail++;
    printf("FAIL %s: %s\n", name, detail);
}

static void expect_text(const char* name, int64_t got, const char* want) {
    int64_t len = rt_string_len(got);
    if (len == (int64_t)strlen(want) && strcmp(text_cstr(got), want) == 0) {
        ok(name);
    } else {
        char d[8600];
        snprintf(d, sizeof(d), "got \"%s\" (len %lld), want \"%s\"",
                 text_cstr(got), (long long)len, want);
        fail(name, d);
    }
}

static void expect_i64(const char* name, int64_t got, int64_t want) {
    if (got == want) {
        ok(name);
    } else {
        char d[128];
        snprintf(d, sizeof(d), "got %lld, want %lld", (long long)got, (long long)want);
        fail(name, d);
    }
}

static void expect_true(const char* name, int cond, const char* detail) {
    if (cond) ok(name); else fail(name, detail);
}

/* ===== fixture helpers (driver-side, standard C only) ===== */
static int write_file(const char* path, const char* content) {
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    fwrite(content, 1, strlen(content), f);
    fclose(f);
    return 1;
}

static int host_mkdir(const char* path) {
#ifdef _WIN32
    return _mkdir(path) == 0 || errno == EEXIST;
#else
    return mkdir(path, 0755) == 0 || errno == EEXIST;
#endif
}

/* ===== test groups ===== */

static void test_path_normalize(void) {
    struct { const char* in; const char* want; const char* name; } cases[] = {
        { "", ".", "normalize.empty" },
        { ".", ".", "normalize.dot" },
        { "..", "..", "normalize.dotdot" },
        { "/", "/", "normalize.root" },
        { "/..", "/", "normalize.root_dotdot" },
        { "foo/../bar/./baz", "bar/baz", "normalize.mixed" },
        { "a/../../b", "../b", "normalize.escape_up" },
        { "a//b///c", "a/b/c", "normalize.dup_seps" },
        { "a/./b/.", "a/b", "normalize.trailing_dot" },
        { "a/b/", "a/b", "normalize.trailing_sep" },
        { "a/b/../..", ".", "normalize.collapse_all" },
        { "../x", "../x", "normalize.keep_leading_up" },
        { "..\\..\\a", "../../a", "normalize.backslash_up" },
        { "C:\\x\\..\\y", "C:/y", "normalize.drive_abs" },
        { "C:", "C:", "normalize.drive_only" },
        { "C:/", "C:/", "normalize.drive_root" },
        { "C:foo/../bar", "C:bar", "normalize.drive_relative" },
        { "src\\lib\\..\\runtime\\x.c", "src/runtime/x.c", "normalize.win_typical" },
        { "path with spaces/./sub", "path with spaces/sub", "normalize.spaces" },
        { "caf\xc3\xa9/../\xc3\xbc", "\xc3\xbc", "normalize.utf8" },
    };
    for (size_t i = 0; i < sizeof(cases) / sizeof(cases[0]); i++) {
        expect_text(cases[i].name, rt_path_normalize(mk_text(cases[i].in)), cases[i].want);
    }
    /* Overlong input (> 4095 bytes) is a decode failure: empty text, never
     * a fabricated ".". */
    {
        char* longp = (char*)malloc(6000);
        memset(longp, 'a', 5999);
        longp[5999] = '\0';
        int64_t v = rt_path_normalize(rt_string_new((const uint8_t*)longp, 5999));
        expect_i64("normalize.overlong_is_empty", rt_string_len(v), 0);
        free(longp);
    }
    /* UNC limitation (documented): the leading double separator collapses. */
    expect_text("normalize.unc_collapses_documented",
                rt_path_normalize(mk_text("\\\\server\\share\\x")), "/server/share/x");
}

static void test_mkdir_readdir(const char* sandbox) {
    char p[1024];

    snprintf(p, sizeof(p), "%s/newdir", sandbox);
    expect_i64("mkdir.create", rt_mkdir(mk_text(p), 0), 0);
    expect_i64("mkdir.eexist", rt_mkdir(mk_text(p), 0), -(int64_t)EEXIST);

    snprintf(p, sizeof(p), "%s/no_parent_xyz/child", sandbox);
    expect_i64("mkdir.missing_parent", rt_mkdir(mk_text(p), 0), -(int64_t)ENOENT);

    snprintf(p, sizeof(p), "%s/dir with spaces", sandbox);
    expect_i64("mkdir.spaces", rt_mkdir(mk_text(p), 0), 0);

    /* unicode (UTF-8) directory name -- exercises the wide-API branch */
    snprintf(p, sizeof(p), "%s/t\xc3\xabst_\xce\xb4", sandbox);
    expect_i64("mkdir.unicode", rt_mkdir(mk_text(p), 0), 0);

    /* overlong path: decode failure sentinel */
    {
        char* longp = (char*)malloc(6000);
        memset(longp, 'b', 5999);
        longp[5999] = '\0';
        expect_true("mkdir.overlong_fails",
                    rt_mkdir(rt_string_new((const uint8_t*)longp, 5999), 0) < 0,
                    "expected negative");
        free(longp);
    }

    /* readdir: missing dir -> handle 0 */
    snprintf(p, sizeof(p), "%s/definitely_missing_dir", sandbox);
    expect_i64("readdir.missing_is_0", rt_readdir(mk_text(p)), 0);

    /* readdir: empty dir -> valid handle, count 0 (distinct from missing) */
    snprintf(p, sizeof(p), "%s/newdir", sandbox);
    {
        int64_t h = rt_readdir(mk_text(p));
        expect_true("readdir.empty_handle_nonzero", h != 0, "handle was 0");
        expect_i64("readdir.empty_count", rt_readdir_count(h), 0);
        expect_text("readdir.empty_entry_oob", rt_readdir_entry(h, 0), "");
        rt_readdir_free(h);
    }

    /* readdir: populated dir (ascii, spaces, unicode names) */
    snprintf(p, sizeof(p), "%s/list", sandbox);
    host_mkdir(p);
    {
        char f[1200];
        snprintf(f, sizeof(f), "%s/a.txt", p);
        write_file(f, "a");
        snprintf(f, sizeof(f), "%s/b c.txt", p);
        write_file(f, "b");
        snprintf(f, sizeof(f), "%s/\xc3\xbc.txt", p);
        write_file(f, "u");

        int64_t h = rt_readdir(mk_text(p));
        expect_true("readdir.handle_nonzero", h != 0, "handle was 0");
        expect_i64("readdir.count3", rt_readdir_count(h), 3);
        int seen_a = 0, seen_bc = 0, seen_u = 0;
        for (int64_t i = 0; i < rt_readdir_count(h); i++) {
            const char* e = text_cstr(rt_readdir_entry(h, i));
            if (strcmp(e, "a.txt") == 0) seen_a = 1;
            if (strcmp(e, "b c.txt") == 0) seen_bc = 1;
            if (strcmp(e, "\xc3\xbc.txt") == 0) seen_u = 1;
        }
        expect_true("readdir.names", seen_a && seen_bc && seen_u,
                    "missing expected entry (ascii/space/unicode)");
        expect_text("readdir.entry_oob", rt_readdir_entry(h, 99), "");
        expect_text("readdir.entry_negative", rt_readdir_entry(h, -1), "");
        rt_readdir_free(h);
        rt_readdir_free(0); /* must not crash */
        ok("readdir.free_zero_safe");
    }

    /* readdir on a FILE (not a dir): FindFirstFileW would match the file
     * itself; the contract (interpreter: fs::read_dir fails) is handle 0. */
    {
        char f[1200];
        snprintf(f, sizeof(f), "%s/list/a.txt", sandbox);
        expect_i64("readdir.on_file_is_0", rt_readdir(mk_text(f)), 0);
    }
}

static void test_file_modified(const char* sandbox) {
    char p[1024];
    snprintf(p, sizeof(p), "%s/mtime.txt", sandbox);
    write_file(p, "x");

    int64_t now = (int64_t)time(NULL);
    int64_t m1 = rt_file_modified(mk_text(p));
    int64_t m2 = rt_file_modified_time(mk_text(p));

    expect_true("file_modified.recent", m1 > 1500000000 && m1 <= now + 86400,
                "mtime not within sane range of now");
    expect_i64("file_modified.twins_agree", m1, m2);
    expect_i64("file_modified.missing_is_neg",
               rt_file_modified(mk_text("definitely/missing/file.xyz")) < 0 ? -1 : 0, -1);
    expect_i64("file_modified_time.missing_is_neg",
               rt_file_modified_time(mk_text("definitely/missing/file.xyz")) < 0 ? -1 : 0, -1);
    /* directory mtime is valid too (watcher walks dirs) */
    expect_true("file_modified.dir", rt_file_modified(mk_text(sandbox)) > 0,
                "directory mtime <= 0");
    /* unicode path */
    snprintf(p, sizeof(p), "%s/m\xc3\xa4time.txt", sandbox);
    write_file(p, "x");
    expect_true("file_modified.unicode", rt_file_modified(mk_text(p)) > 0,
                "unicode path mtime <= 0");
}

static void test_list_dir_recursive(const char* sandbox) {
    char p[1024], f[1200];
    snprintf(p, sizeof(p), "%s/walk", sandbox);
    host_mkdir(p);
    snprintf(f, sizeof(f), "%s/walk/one.spl", sandbox);
    write_file(f, "1");
    snprintf(f, sizeof(f), "%s/walk/two.txt", sandbox);
    write_file(f, "2");
    snprintf(p, sizeof(p), "%s/walk/sub dir", sandbox);
    host_mkdir(p);
    snprintf(f, sizeof(f), "%s/walk/sub dir/three.spl", sandbox);
    write_file(f, "3");
    snprintf(f, sizeof(f), "%s/walk/f\xc3\xb6ur.spl", sandbox); /* unicode name */
    write_file(f, "4");

    char root[1024];
    snprintf(root, sizeof(root), "%s/walk", sandbox);

    int64_t arr = rt_list_dir_recursive(mk_text(root), mk_text("spl"));
    expect_i64("list_dir.ext_no_dot_count", rt_array_len_safe(arr), 3);

    int64_t arr2 = rt_list_dir_recursive(mk_text(root), mk_text(".spl"));
    expect_i64("list_dir.ext_dot_count", rt_array_len_safe(arr2), 3);

    int64_t arr3 = rt_list_dir_recursive(mk_text(root), mk_text(""));
    expect_i64("list_dir.ext_empty_lists_all", rt_array_len_safe(arr3), 4);

    /* entries are FULL paths that exist and end with the suffix */
    int full_paths_ok = 1, found_subdir_file = 0;
    for (int64_t i = 0; i < rt_array_len_safe(arr); i++) {
        int64_t e = rt_array_get((SplArray*)(uintptr_t)arr, i);
        const char* s = text_cstr(e);
        if (strstr(s, "walk") == NULL) full_paths_ok = 0;
        size_t n = strlen(s);
        if (n < 4 || strcmp(s + n - 4, ".spl") != 0) full_paths_ok = 0;
        if (strstr(s, "three.spl")) found_subdir_file = 1;
        if (rt_file_modified(e) <= 0) full_paths_ok = 0; /* path must resolve */
    }
    expect_true("list_dir.full_paths_resolve", full_paths_ok,
                "an entry was not a resolvable full path ending in .spl");
    expect_true("list_dir.descends_spaced_subdir", found_subdir_file,
                "three.spl in 'sub dir' not found");

    expect_i64("list_dir.missing_dir_empty",
               rt_array_len_safe(rt_list_dir_recursive(mk_text("no/such/dir/xyz"), mk_text(""))), 0);
}

static void test_shell(void) {
    expect_i64("shell.exit0", rt_shell(mk_text("exit 0")), 0);
    expect_i64("shell.exit3", rt_shell(mk_text("exit 3")), 3);
    expect_true("shell.unknown_cmd_nonzero",
                rt_shell(mk_text("definitely_not_a_command_xyz_123 2>nul")) != 0,
                "expected nonzero exit");

    /* shell_output: verbatim stdout capture */
    {
        int64_t out = rt_shell_output(mk_text("echo hi"));
        const char* s = text_cstr(out);
        expect_true("shell_output.echo", strncmp(s, "hi", 2) == 0 && rt_string_len(out) >= 3,
                    "expected \"hi\" + newline");
    }
    expect_i64("shell_output.silent_cmd_empty",
               rt_string_len(rt_shell_output(mk_text("cd ."))), 0);
    {
        /* failing command: stdout empty (stderr not captured) */
        int64_t out = rt_shell_output(mk_text("definitely_not_a_command_xyz_123 2>nul"));
        expect_i64("shell_output.unknown_cmd_empty", rt_string_len(out), 0);
    }
    /* multi-line capture, no trimming */
    {
        int64_t out = rt_shell_output(mk_text("echo a&& echo b"));
        const char* s = text_cstr(out);
        expect_true("shell_output.multiline",
                    strstr(s, "a") != NULL && strstr(s, "b") != NULL &&
                    rt_string_len(out) >= 4,
                    "expected two lines");
    }
}

static void test_process_output(void) {
    {
        /* Representative caller shape (package.registry: process_output
         * ("curl", ["-sL", url])): a real executable + individual args.
         * NOT `cmd` + `/c ...`: cmd.exe refuses a quoted "/c ..." tail --
         * that is the documented cmd-quoting lossiness of this ABI. */
        int64_t args = (int64_t)(uintptr_t)rt_array_new(0);
        rt_array_push((SplArray*)(uintptr_t)args, mk_text("--version"));
        int64_t out = rt_process_output(mk_text("git"), args);
        const char* s = text_cstr(out);
        expect_true("process_output.git_version",
                    strncmp(s, "git version", 11) == 0,
                    "expected \"git version ...\" from git --version");
    }
    {
        /* arg with spaces survives quoting: findstr pattern with a space */
        int64_t args = (int64_t)(uintptr_t)rt_array_new(0);
        rt_array_push((SplArray*)(uintptr_t)args, mk_text("log"));
        rt_array_push((SplArray*)(uintptr_t)args, mk_text("--format=%H %s"));
        rt_array_push((SplArray*)(uintptr_t)args, mk_text("-1"));
        int64_t out = rt_process_output(mk_text("git"), args);
        expect_true("process_output.spaced_arg",
                    rt_string_len(out) > 40,
                    "expected \"<sha> <subject>\" line from git log");
    }
    {
        int64_t out = rt_process_output(mk_text("definitely_not_a_command_xyz_123 2>nul"),
                                        (int64_t)(uintptr_t)rt_array_new(0));
        expect_i64("process_output.failure_empty", rt_string_len(out), 0);
    }
    {
        /* empty args array, quiet success */
        int64_t out = rt_process_output(mk_text("cd"), (int64_t)(uintptr_t)rt_array_new(0));
        expect_true("process_output.no_args", rt_string_len(out) >= 0, "negative len");
    }
}

static void test_string_bytes(void) {
    /* round trip incl. UTF-8 and an embedded NUL (length-carried, no strlen) */
    static const uint8_t raw[] = { 'h', 0xC3, 0xA9, 0x00, 'x', 0xFF };
    int64_t txt = rt_string_new(raw, sizeof(raw));
    int64_t arr = rt_string_to_byte_array(txt);
    expect_i64("bytes.len", rt_array_len_safe(arr), (int64_t)sizeof(raw));
    int tags_ok = 1, vals_ok = 1;
    for (int64_t i = 0; i < rt_array_len_safe(arr); i++) {
        int64_t v = rt_array_get((SplArray*)(uintptr_t)arr, i);
        if ((v & 7) != 0) tags_ok = 0;
        if ((v >> 3) != (int64_t)raw[i]) vals_ok = 0;
    }
    expect_true("bytes.inline_int_tag", tags_ok, "element not <<3-tagged");
    expect_true("bytes.values", vals_ok, "byte value mismatch");

    int64_t back = rt_string_from_byte_array(arr);
    expect_true("bytes.round_trip",
                rt_string_len(back) == (int64_t)sizeof(raw) &&
                memcmp(rt_string_data(back), raw, sizeof(raw)) == 0,
                "round trip mismatch");

    /* empty both ways */
    expect_i64("bytes.empty_text_to_empty_array",
               rt_array_len_safe(rt_string_to_byte_array(mk_text(""))), 0);
    expect_i64("bytes.empty_array_to_empty_text",
               rt_string_len(rt_string_from_byte_array((int64_t)(uintptr_t)rt_array_new(0))), 0);

    /* corrupt elements -> empty text */
    {
        int64_t bad = (int64_t)(uintptr_t)rt_array_new(0);
        rt_array_push((SplArray*)(uintptr_t)bad, (65 << 3) | 1); /* wrong tag */
        expect_i64("bytes.bad_tag_empty", rt_string_len(rt_string_from_byte_array(bad)), 0);
    }
    {
        int64_t bad = (int64_t)(uintptr_t)rt_array_new(0);
        rt_array_push((SplArray*)(uintptr_t)bad, 300 << 3); /* out of byte range */
        expect_i64("bytes.oob_byte_empty", rt_string_len(rt_string_from_byte_array(bad)), 0);
    }
}

static void test_random(void) {
    int64_t a = rt_random_i64();
    int64_t b = rt_random_i64();
    expect_true("random.nonconstant", a != b || a != 0,
                "two draws identical AND zero -- RNG dead");
    int64_t c = rt_random_i64();
    expect_true("random.nonzero_witness", a != 0 || b != 0 || c != 0,
                "three zero draws -- RNG dead");
}

static int run_core(const char* sandbox) {
    if (!host_mkdir(sandbox)) {
        printf("FAIL setup: cannot create sandbox %s\n", sandbox);
        return 1;
    }
    test_path_normalize();
    test_mkdir_readdir(sandbox);
    test_file_modified(sandbox);
    test_list_dir_recursive(sandbox);
    test_shell();
    test_process_output();
    test_string_bytes();
    test_random();
    printf("RESULT pass=%d fail=%d\n", g_pass, g_fail);
    return g_fail ? 1 : 0;
}

static void hex_dump_array(int64_t arr) {
    int64_t n = rt_array_len_safe(arr);
    for (int64_t i = 0; i < n; i++) {
        int64_t v = rt_array_get((SplArray*)(uintptr_t)arr, i);
        printf("%02x", (unsigned)((v >> 3) & 0xFF));
    }
    printf("\n");
}

int main(int argc, char** argv) {
    const char* cmd = argc > 1 ? argv[1] : "core";
    if (strcmp(cmd, "core") == 0) {
        const char* sandbox = argc > 2 ? argv[2] : "build/rt_core_selfcheck_sandbox";
        return run_core(sandbox);
    }
    if (strcmp(cmd, "stdin_read") == 0) {
        int64_t size = argc > 2 ? atoll(argv[2]) : 4;
        hex_dump_array(rt_stdin_read(size));
        return 0;
    }
    if (strcmp(cmd, "stdin_read_all") == 0) {
        hex_dump_array(rt_stdin_read_all());
        return 0;
    }
    if (strcmp(cmd, "term") == 0) {
        /* "h\xc3\xabllo\n" is 7 bytes: return value must be the BYTE count */
        int64_t txt = mk_text("h\xc3\xabllo\n");
        int64_t wrote = rt_term_write(txt);
        int32_t fl = rt_term_flush();
        fprintf(stderr, "wrote=%lld flush=%d empty=%lld\n",
                (long long)wrote, fl, (long long)rt_term_write(mk_text("")));
        return 0;
    }
    if (strcmp(cmd, "probe_mkdir") == 0 && argc > 2) {
        printf("%lld\n", (long long)rt_mkdir(mk_text(argv[2]), 0));
        return 0;
    }
    if (strcmp(cmd, "probe_mtime") == 0 && argc > 2) {
        printf("%lld\n", (long long)rt_file_modified(mk_text(argv[2])));
        return 0;
    }
    fprintf(stderr, "unknown subcommand %s\n", cmd);
    return 2;
}
