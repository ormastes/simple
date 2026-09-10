/* Stage2 bootstrap link (core-C-only lane): behavioural proof for the 10
 * `rt_*` symbols added to runtime_native.c to close part of the remaining
 * undefined-symbol set found when relinking the real Stage2 failed-link
 * object set (native-objects-8HIZif, run22, 2026-09-07) with
 * `-Wl,--error-limit=0` -- see
 * doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md,
 * "Bucket 2 deferred: Rust-only, core-C-bootstrap lane gap" table.
 *
 * Covers: rt_env_home, rt_env_vars (env_process.rs); rt_file_open,
 * rt_file_close (descriptor.rs); rt_file_exists_str, rt_file_hash
 * (cli_sffi.rs); rt_file_canonicalize, rt_file_read_lines,
 * rt_file_mmap_read_bytes (file_ops.rs); rt_dir_glob (directory.rs).
 *
 * Does NOT cover (deliberately out of scope, see the census/bug doc):
 * rt_array_sum / rt_array_sorted (operate on the Rust-tagged RuntimeArray
 * representation, not this lane's RtCoreArray), rt_cli_handle_compile /
 * rt_cli_run_tests_process_args (call into the compiler/test-runner
 * pipeline), rt_mmap / rt_execute_native (capability-sandboxed, need
 * security_runtime.rs), rt_file_atomic_write_mode / rt_file_list_dir /
 * rt_file_mode / rt_fs_read_text (no implementation on either side).
 *
 * Build (same recipe as rt_bootstrap_c_lane_atomic_math_time_selfcheck.c
 * beside this file):
 *   cc -c -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -DSIMPLE_RUNTIME_MEMORY_OWNER=1 -DSIMPLE_RUNTIME_PROCESS_OWNED_STRING_FREE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 -Wl,--gc-sections \
 *      src/runtime/test/rt_bootstrap_c_lane_fs_env_selfcheck.c \
 *      rn.o -lpthread -lm -ldl -o selfcheck && ./selfcheck
 */
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* SplArray is opaque outside runtime_native.c; test code, like any other
 * translation unit, only ever sees it as a pointer handed back through
 * rt_array_* accessors. */
typedef struct SplArray SplArray;

extern int64_t rt_env_home(void);
extern int64_t rt_env_vars(void);
extern int32_t rt_file_open(const uint8_t* path_ptr, uint64_t path_len, int32_t mode);
extern int8_t  rt_file_close(int32_t fd);
extern int8_t  rt_file_exists_str(int64_t path_value);
extern int64_t rt_file_hash(int64_t path_value);
extern int64_t rt_file_canonicalize(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_read_lines(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_file_mmap_read_bytes(const uint8_t* path_ptr, uint64_t path_len);
extern int64_t rt_dir_glob(const uint8_t* pattern_ptr, uint64_t pattern_len);

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t string);
extern const uint8_t* rt_string_data(int64_t string);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_array_get(SplArray* array, int64_t idx);
extern int64_t rt_tuple_get(int64_t tuple, int64_t idx);

/* rt_core_nil(): (0 << 3) | RT_VALUE_TAG_SPECIAL, and RT_VALUE_TAG_SPECIAL is
 * 0x3 (runtime_native.c:247-248) -- not exported, so the concrete tagged
 * value is reproduced here rather than linking an internal static inline. */
#define RT_TEST_NIL 3

/* rt_file_canonicalize calls rt_getcwd() / spl_strdup(), both declared in
 * runtime.h and DEFINED in runtime.c -- not this file, and not linked into
 * this standalone selfcheck (same isolation as
 * rt_bootstrap_c_lane_atomic_math_time_selfcheck.c beside this file, which
 * links only runtime_native.o). Trivial libc-backed stand-ins, sufficient
 * for this real-filesystem exercise. */
char* spl_strdup(const char* s) {
    if (!s) return NULL;
    size_t len = strlen(s) + 1;
    char* out = (char*)malloc(len);
    if (out) memcpy(out, s, len);
    return out;
}
char* rt_getcwd(void) {
    char buf[4096];
    if (!getcwd(buf, sizeof(buf))) return NULL;
    return spl_strdup(buf);
}

static int failures = 0;
#define CHECK(cond, msg) do { \
    if (!(cond)) { fprintf(stderr, "FAIL: %s\n", msg); failures++; } \
    else { fprintf(stderr, "ok:   %s\n", msg); } \
} while (0)

static char* read_string_value(int64_t handle, uint64_t* len_out) {
    if (handle == RT_TEST_NIL) { if (len_out) *len_out = 0; return NULL; }
    int64_t len = rt_string_len(handle);
    const uint8_t* data = rt_string_data(handle);
    if (len_out) *len_out = (uint64_t)(len > 0 ? len : 0);
    if (len < 0) return NULL;
    char* out = (char*)malloc((size_t)len + 1);
    if (len > 0 && data) memcpy(out, data, (size_t)len);
    out[len] = '\0';
    return out;
}

int main(void) {
    /* ---- rt_env_home: reflects a real, just-set HOME ---- */
    setenv("HOME", "/tmp/rt_selfcheck_home", 1);
    char* home_str = read_string_value(rt_env_home(), NULL);
    CHECK(home_str && strcmp(home_str, "/tmp/rt_selfcheck_home") == 0,
          "rt_env_home reflects a real HOME change");
    free(home_str);

    /* ---- rt_env_vars: array of (key, value) tuples, includes a fresh var ---- */
    setenv("RT_SELFCHECK_MARKER", "marker-value-42", 1);
    SplArray* vars_arr = (SplArray*)(uintptr_t)rt_env_vars();
    int64_t n = rt_array_len(vars_arr);
    int found_marker = 0;
    for (int64_t i = 0; i < n; i++) {
        int64_t pair = rt_array_get(vars_arr, i);
        char* key_str = read_string_value(rt_tuple_get(pair, 0), NULL);
        char* value_str = read_string_value(rt_tuple_get(pair, 1), NULL);
        if (key_str && value_str && strcmp(key_str, "RT_SELFCHECK_MARKER") == 0 &&
            strcmp(value_str, "marker-value-42") == 0) {
            found_marker = 1;
        }
        free(key_str);
        free(value_str);
    }
    CHECK(n > 0 && found_marker, "rt_env_vars includes a freshly-set environment variable");

    /* ---- rt_file_open / rt_file_close / rt_file_exists_str ---- */
    const char* path = "/tmp/rt_selfcheck_file.txt";
    const char* content = "line one\nline two\r\nline three";
    FILE* setup = fopen(path, "wb");
    fwrite(content, 1, strlen(content), setup);
    fclose(setup);

    int64_t path_boxed = rt_string_new((const uint8_t*)path, (uint64_t)strlen(path));
    CHECK(rt_file_exists_str(path_boxed) == 1, "rt_file_exists_str finds a real file");

    const char* missing_path = "/tmp/rt_selfcheck_missing_xyz";
    int64_t missing_boxed = rt_string_new((const uint8_t*)missing_path, (uint64_t)strlen(missing_path));
    CHECK(rt_file_exists_str(missing_boxed) == 0, "rt_file_exists_str rejects a missing path");

    int32_t fd = rt_file_open((const uint8_t*)path, (uint64_t)strlen(path), 0);
    CHECK(fd >= 0, "rt_file_open opens an existing file read-only");
    char buf[16];
    ssize_t got = read(fd, buf, 8);
    CHECK(got == 8 && memcmp(buf, "line one", 8) == 0, "fd from rt_file_open reads real content");
    CHECK(rt_file_close(fd) == 1, "rt_file_close reports success on a real fd");
    CHECK(rt_file_close(fd) == 0, "rt_file_close reports failure closing an already-closed fd");

    int32_t bad_fd = rt_file_open((const uint8_t*)missing_path, (uint64_t)strlen(missing_path), 0);
    CHECK(bad_fd == -1, "rt_file_open returns -1 for a missing file");

    /* ---- rt_file_hash: known SHA-256 test vector ---- */
    const char* hash_path = "/tmp/rt_selfcheck_hash.txt";
    FILE* hf = fopen(hash_path, "wb");
    fwrite("abc", 1, 3, hf);
    fclose(hf);
    int64_t hash_path_boxed = rt_string_new((const uint8_t*)hash_path, (uint64_t)strlen(hash_path));
    char* hash_str = read_string_value(rt_file_hash(hash_path_boxed), NULL);
    CHECK(hash_str && strcmp(hash_str,
        "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad") == 0,
        "rt_file_hash matches the known SHA-256(\"abc\") test vector");
    free(hash_str);

    char* hash_missing = read_string_value(rt_file_hash(missing_boxed), NULL);
    CHECK(hash_missing && strlen(hash_missing) == 0,
          "rt_file_hash returns an EMPTY (not nil) text for a missing file, matching the Rust body");
    free(hash_missing);

    /* ---- rt_file_canonicalize: lexical ".." popping + cwd-relative join ---- */
    const char* dotdot_path = "/tmp/rt_selfcheck_dir/../rt_selfcheck_file.txt";
    char* canon = read_string_value(
        rt_file_canonicalize((const uint8_t*)dotdot_path, (uint64_t)strlen(dotdot_path)), NULL);
    CHECK(canon && strcmp(canon, "/tmp/rt_selfcheck_file.txt") == 0,
          "rt_file_canonicalize pops a \"..\" component lexically");
    free(canon);

    char cwd[4096];
    if (getcwd(cwd, sizeof(cwd))) {
        char expected[8192];
        snprintf(expected, sizeof(expected), "%s/rt_selfcheck_relative.txt", cwd);
        const char* rel_path = "rt_selfcheck_relative.txt";
        char* canon_rel = read_string_value(
            rt_file_canonicalize((const uint8_t*)rel_path, (uint64_t)strlen(rel_path)), NULL);
        CHECK(canon_rel && strcmp(canon_rel, expected) == 0,
              "rt_file_canonicalize joins a relative path onto the real cwd");
        free(canon_rel);
    }

    /* ---- rt_file_read_lines: real \n / \r\n split, no spurious trailing line ---- */
    SplArray* lines = (SplArray*)(uintptr_t)
        rt_file_read_lines((const uint8_t*)path, (uint64_t)strlen(path));
    CHECK(rt_array_len(lines) == 3, "rt_file_read_lines splits into exactly 3 lines");
    char* line0 = read_string_value(rt_array_get(lines, 0), NULL);
    char* line1 = read_string_value(rt_array_get(lines, 1), NULL);
    char* line2 = read_string_value(rt_array_get(lines, 2), NULL);
    CHECK(line0 && strcmp(line0, "line one") == 0, "rt_file_read_lines line 0 is exact");
    CHECK(line1 && strcmp(line1, "line two") == 0, "rt_file_read_lines strips a trailing \\r");
    CHECK(line2 && strcmp(line2, "line three") == 0, "rt_file_read_lines last line (no trailing newline) is exact");
    free(line0); free(line1); free(line2);

    /* ---- rt_file_mmap_read_bytes: real byte content, including a NUL byte ---- */
    const char* bin_path = "/tmp/rt_selfcheck_bytes.bin";
    unsigned char raw[4] = { 0x00, 0xFF, 0x10, 0x42 };
    FILE* bf = fopen(bin_path, "wb");
    fwrite(raw, 1, sizeof(raw), bf);
    fclose(bf);
    SplArray* bytes = (SplArray*)(uintptr_t)
        rt_file_mmap_read_bytes((const uint8_t*)bin_path, (uint64_t)strlen(bin_path));
    CHECK(rt_array_len(bytes) == 4, "rt_file_mmap_read_bytes returns the exact byte count");
    int bytes_ok = 1;
    for (int i = 0; i < 4; i++) {
        if (rt_array_get(bytes, i) != raw[i]) bytes_ok = 0;
    }
    CHECK(bytes_ok, "rt_file_mmap_read_bytes preserves every byte value, including 0x00 and 0xFF");

    /* ---- rt_dir_glob: real filesystem match against a real pattern ---- */
    system("rm -rf /tmp/rt_selfcheck_glob && mkdir -p /tmp/rt_selfcheck_glob");
    FILE* g1 = fopen("/tmp/rt_selfcheck_glob/a.marker", "wb"); fclose(g1);
    FILE* g2 = fopen("/tmp/rt_selfcheck_glob/b.marker", "wb"); fclose(g2);
    FILE* g3 = fopen("/tmp/rt_selfcheck_glob/c.other", "wb"); fclose(g3);
    const char* pattern = "/tmp/rt_selfcheck_glob/*.marker";
    SplArray* glob_result = (SplArray*)(uintptr_t)
        rt_dir_glob((const uint8_t*)pattern, (uint64_t)strlen(pattern));
    int64_t glob_n = rt_array_len(glob_result);
    int has_a = 0, has_b = 0, has_other = 0;
    for (int64_t i = 0; i < glob_n; i++) {
        char* p = read_string_value(rt_array_get(glob_result, i), NULL);
        if (p && strstr(p, "a.marker")) has_a = 1;
        if (p && strstr(p, "b.marker")) has_b = 1;
        if (p && strstr(p, "c.other")) has_other = 1;
        free(p);
    }
    CHECK(glob_n == 2 && has_a && has_b && !has_other,
          "rt_dir_glob matches exactly the two *.marker files, not the .other file");

    if (failures == 0) {
        fprintf(stderr, "PASS: bootstrap core-C lane fs/env additions behave correctly\n");
        return 0;
    }
    fprintf(stderr, "FAILED: %d check(s) failed\n", failures);
    return 1;
}
