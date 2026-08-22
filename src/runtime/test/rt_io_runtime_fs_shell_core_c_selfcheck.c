/* Core-C definitions for the std.io_runtime fs/shell externs.
 *
 * rt_dir_list, rt_dir_remove, rt_file_copy, rt_file_rename,
 * rt_file_hash_sha256 and rt_shell_exec are declared by
 * src/lib/nogc_sync_mut/io_runtime.spl and emitted by native codegen, but until
 * 2026-08-22 only the Rust runtime / interpreter defined them. The core-C
 * archive had no definition, the native link tolerated the undefined symbol,
 * and test_core_c_lane_simple_lsp_mcp_startup_initialize_reduced_source failed
 * with "7 runtime symbol(s) referenced by generated code have no definition".
 *
 * Build (exact TU the core-C archive is made from):
 *   cc -c -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -c -std=gnu11 -ffunction-sections -Isrc/runtime \
 *      src/runtime/runtime_legacy_core.c -o lc.o
 *   cc -std=gnu11 -Wl,--gc-sections \
 *      src/runtime/test/rt_io_runtime_fs_shell_core_c_selfcheck.c rn.o lc.o \
 *      -lpthread -lm -ldl -o fs_shell && ./fs_shell
 */
#define _XOPEN_SOURCE 700
#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static int failures = 0;
#define CHECK(cond, what) do { if (!(cond)) { fprintf(stderr, "FAIL: %s\n", what); failures++; } } while (0)

static int64_t t(const char* s) { return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s)); }
#define PL(s) (const uint8_t*)(s), (uint64_t)strlen(s)

static int text_is(int64_t value, const char* expected) {
    if (rt_string_len(value) != (int64_t)strlen(expected)) return 0;
    return memcmp(rt_string_data(value), expected, strlen(expected)) == 0;
}

int main(void) {
    char root[] = "/tmp/rt_fs_shell_selfcheck_XXXXXX";
    CHECK(mkdtemp(root) != NULL, "mkdtemp");
    char a[256], b[256], sub[256];
    snprintf(a, sizeof a, "%s/a.txt", root);
    snprintf(b, sizeof b, "%s/b.txt", root);
    snprintf(sub, sizeof sub, "%s/sub", root);

    FILE* f = fopen(a, "wb");
    CHECK(f && fputs("abc", f) >= 0 && fclose(f) == 0, "write a.txt");

    /* sha256("abc") is the canonical FIPS 180 test vector. */
    int64_t hash = rt_file_hash_sha256(PL(a));
    CHECK(text_is(hash, "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
          "rt_file_hash_sha256(abc) == FIPS vector");
    CHECK(rt_is_none(rt_file_hash_sha256(PL("/nonexistent/zz"))), "hash of missing file is nil");

    CHECK(rt_file_copy(PL(a), PL(b)) == 1, "rt_file_copy");
    CHECK(text_is(rt_file_hash_sha256(PL(b)), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
          "copy is byte-identical");
    CHECK(rt_file_copy(PL("/nonexistent/zz"), PL(b)) == 0, "copy of missing src fails");

    CHECK(rt_dir_create(PL(sub), false), "mkdir sub");
    int64_t listing = rt_dir_list(PL(root));
    CHECK(!rt_is_none(listing), "rt_dir_list returns an array");
    CHECK(rt_array_len((SplArray*)(uintptr_t)listing) == 3, "listing has a.txt, b.txt, sub (no . / ..)");
    int saw_a = 0, saw_sub = 0;
    for (int64_t i = 0; i < 3; i++) {
        int64_t name = rt_array_get((SplArray*)(uintptr_t)listing, i);
        if (text_is(name, "a.txt")) saw_a = 1;
        if (text_is(name, "sub")) saw_sub = 1;
    }
    CHECK(saw_a && saw_sub, "listing carries entry NAMES, not paths");
    int64_t missing = rt_dir_list(PL("/nonexistent/zz"));
    CHECK(!rt_is_none(missing) && rt_array_len((SplArray*)(uintptr_t)missing) == 0,
          "rt_dir_list of missing dir is an EMPTY array (runtime.c contract, [text] is non-optional)");

    char c[256];
    snprintf(c, sizeof c, "%s/c.txt", sub);
    CHECK(rt_file_rename(PL(b), PL(c)), "rt_file_rename into sub");
    CHECK(access(b, F_OK) != 0 && access(c, F_OK) == 0, "rename moved the file");
    CHECK(!rt_file_rename(PL(b), PL(c)), "rename of missing src fails");

    CHECK(!rt_dir_remove(PL(sub), false), "non-recursive remove refuses a non-empty dir");
    CHECK(rt_dir_remove(PL(sub), true), "recursive remove succeeds");
    CHECK(access(sub, F_OK) != 0, "sub is gone");
    CHECK(rt_dir_create(PL(sub), false) && rt_dir_remove(PL(sub), false), "non-recursive remove of empty dir");

    int64_t out = rt_shell_exec(t("printf 'hello %s' world"));
    CHECK(text_is(out, "hello world"), "rt_shell_exec captures stdout");
    CHECK(text_is(rt_shell_exec(t("true")), ""), "empty stdout is empty text, not nil");
    CHECK(rt_is_none(rt_shell_exec(rt_value_int(3))), "non-text cmd is nil");

    unlink(a);
    rmdir(root);
    if (failures == 0) printf("PASS: core-C io_runtime fs/shell externs\n");
    return failures == 0 ? 0 : 1;
}
