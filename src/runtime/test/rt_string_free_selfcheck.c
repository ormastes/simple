#define _POSIX_C_SOURCE 200809L

/* Self-check for rt_string_free, the tombstoned immortal registry, and the
 * standalone core I/O providers linked into the capsule.
 *
 * The registry is open-addressed and, until rt_string_free existed, had NO
 * deletion. Erasing by writing 0 would truncate any probe chain running
 * through that slot, so unrelated LIVE strings would silently start reading as
 * unregistered. Case 5 is the one that catches that: it frees every other
 * string out of a large batch and then re-checks that all survivors are still
 * usable. It fails loudly on a naive (tombstone-less) erase.
 *
 * Build + run:
 *   cc -std=gnu11 -O1 -o /tmp/rtsf src/runtime/test/rt_string_free_selfcheck.c \
 *      src/runtime/runtime_native.c -lm -lpthread && /tmp/rtsf
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <errno.h>
#include <sys/stat.h>
#include <unistd.h>

typedef struct SplArray SplArray;

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_new_literal(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_free(int64_t value);
extern int64_t rt_heap_registry_count(void);
extern int64_t rt_string_len(int64_t value);
extern const uint8_t* rt_string_data(int64_t value);
extern int64_t rt_array_len(SplArray* array);
extern int64_t rt_array_get(SplArray* array, int64_t index);
extern int64_t rt_array_free_deep(int64_t value);
extern int8_t rt_file_copy(const uint8_t* src, uint64_t src_len,
                           const uint8_t* dst, uint64_t dst_len);
extern int8_t rt_file_rename(const uint8_t* src, uint64_t src_len,
                             const uint8_t* dst, uint64_t dst_len);
extern int64_t rt_file_hash_sha256(const uint8_t* path, uint64_t path_len);
extern int8_t rt_process_exists(int64_t pid);
extern int64_t rt_dir_list(const uint8_t* path, uint64_t path_len);
extern int8_t rt_dir_remove(const uint8_t* path, uint64_t path_len,
                            int8_t recursive);

static int failures = 0;

static void check(int cond, const char* what) {
    if (cond) {
        printf("  ok   %s\n", what);
    } else {
        printf("  FAIL %s\n", what);
        failures++;
    }
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

static int string_equals(int64_t value, const char* expected) {
    int64_t len = rt_string_len(value);
    return len == (int64_t)strlen(expected) &&
           memcmp(rt_string_data(value), expected, (size_t)len) == 0;
}

static int array_contains_text(int64_t value, const char* expected) {
    SplArray* array = (SplArray*)(uintptr_t)value;
    int64_t count = rt_array_len(array);
    for (int64_t i = 0; i < count; i++) {
        if (string_equals(rt_array_get(array, i), expected)) return 1;
    }
    return 0;
}

static int write_fixture(const char* path, const char* content) {
    FILE* file = fopen(path, "wb");
    if (!file) return 0;
    size_t len = strlen(content);
    int ok = fwrite(content, 1, len, file) == len;
    return fclose(file) == 0 && ok;
}

static int fixture_equals(const char* path, const char* expected) {
    FILE* file = fopen(path, "rb");
    if (!file) return 0;
    char actual[64];
    size_t expected_len = strlen(expected);
    size_t actual_len = fread(actual, 1, sizeof actual, file);
    int ok = expected_len <= sizeof actual &&
             actual_len == expected_len &&
             memcmp(actual, expected, expected_len) == 0 &&
             !ferror(file);
    return fclose(file) == 0 && ok;
}

int main(void) {
    /* 1. an ordinary heap string is reclaimed, and the registry shrinks */
    int64_t before = rt_heap_registry_count();
    int64_t a = mkstr("a reasonably long unique string for case one");
    check(rt_heap_registry_count() == before + 1, "new string registers (+1)");
    check(rt_string_free(a) == 1, "ordinary string is freed");
    check(rt_heap_registry_count() == before, "registry count returns to baseline");

    /* 2. double free is refused, not a crash or a second decrement */
    int64_t after_first = rt_heap_registry_count();
    check(rt_string_free(a) == 0, "double free refused");
    check(rt_heap_registry_count() == after_first, "refused free does not decrement");

    /* 3. process-wide short-string cache entries are refused.
     *    len<=1 goes through rt_core_short_string_cache and is shared by every
     *    caller, so freeing one would corrupt all the others. */
    int64_t sh = mkstr("x");
    check(rt_string_free(sh) == 0, "short/cached string refused");
    int64_t sh2 = mkstr("x");
    check(rt_string_len(sh2) == 1, "short string still usable after refused free");

    /* 4. interned literals are refused (same object per literal site) */
    static const uint8_t lit[] = "an interned literal value";
    int64_t l1 = rt_string_new_literal(lit, sizeof(lit) - 1);
    check(rt_string_free(l1) == 0, "interned literal refused");
    int64_t l2 = rt_string_new_literal(lit, sizeof(lit) - 1);
    check(l1 == l2, "literal interning still returns the same object");
    check(rt_string_len(l2) == (int64_t)(sizeof(lit) - 1), "interned literal intact");

    /* 5. PROBE-CHAIN INTEGRITY -- the case a tombstone-less erase fails.
     *    Allocate many strings (forcing collisions and growth), free every
     *    other one, then confirm every survivor is still registered and
     *    readable. Freeing must not strand entries later in a probe chain. */
    enum { N = 4096 };
    static int64_t v[N];
    char buf[64];
    for (int i = 0; i < N; i++) {
        snprintf(buf, sizeof buf, "probe-chain-integrity-string-%d", i);
        v[i] = mkstr(buf);
    }
    int64_t peak = rt_heap_registry_count();
    int freed = 0;
    for (int i = 0; i < N; i += 2) {
        if (rt_string_free(v[i]) == 1) freed++;
    }
    check(freed == N / 2, "every even-indexed string freed");
    check(rt_heap_registry_count() == peak - freed, "registry dropped by exactly the freed count");

    int survivors_ok = 1;
    for (int i = 1; i < N; i += 2) {
        snprintf(buf, sizeof buf, "probe-chain-integrity-string-%d", i);
        if (rt_string_len(v[i]) != (int64_t)strlen(buf)) { survivors_ok = 0; break; }
    }
    check(survivors_ok, "all survivors still readable after interleaved frees");

    /* survivors must still be freeable -- proves they were never stranded */
    int refreed = 0;
    for (int i = 1; i < N; i += 2) {
        if (rt_string_free(v[i]) == 1) refreed++;
    }
    check(refreed == N / 2, "every survivor still found in the registry and freed");

    /* 6. reuse after heavy churn: the table must still accept inserts */
    int64_t r = mkstr("post-churn allocation must still register and free");
    check(r != 0, "allocation works after churn");
    check(rt_string_free(r) == 1, "post-churn string frees");

    /* 7. Every standalone core I/O provider executes once through the exact
     * archive ABI. Libc performs setup and verifies cleanup. */
    check(rt_process_exists((int64_t)getpid()) == 1, "current process exists");
    char root[] = "/tmp/simple-core-io-selfcheck-XXXXXX";
    char* created = mkdtemp(root);
    check(created != NULL, "core I/O fixture directory created");
    if (created) {
        char source[256];
        char copy[256];
        char renamed[256];
        char empty[256];
        char nested[256];
        char nested_file[256];
        char one[256];
        snprintf(source, sizeof source, "%s/source.txt", root);
        snprintf(copy, sizeof copy, "%s/copy.txt", root);
        snprintf(renamed, sizeof renamed, "%s/renamed.txt", root);
        snprintf(empty, sizeof empty, "%s/empty", root);
        snprintf(nested, sizeof nested, "%s/nested", root);
        snprintf(nested_file, sizeof nested_file, "%s/child.txt", nested);
        snprintf(one, sizeof one, "%s/x", root);
        check(write_fixture(source, "abc"), "known file created");
        check(mkdir(empty, 0700) == 0, "empty directory created");
        check(mkdir(nested, 0700) == 0, "nested directory created");
        check(write_fixture(nested_file, "nested"), "nested file created");
        check(write_fixture(one, "x"), "one-character entry created");

        check(rt_file_copy((const uint8_t*)source, strlen(source),
                           (const uint8_t*)copy, strlen(copy)) == 1,
              "file copy provider succeeds");
        int64_t hash = rt_file_hash_sha256(
            (const uint8_t*)copy, strlen(copy)
        );
        check(string_equals(
                  hash,
                  "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
              ),
              "file hash provider matches SHA-256 of abc");
        check(rt_string_free(hash) == 1, "hash result freed");
        check(rt_file_rename((const uint8_t*)copy, strlen(copy),
                             (const uint8_t*)renamed, strlen(renamed)) == 1,
              "file rename provider succeeds");
        check(access(copy, F_OK) != 0 && access(renamed, F_OK) == 0,
              "rename moved the copied file");

#if !defined(_WIN32)
        char dot_source[256];
        char dot_alias[256];
        char symlink_source[256];
        char symlink_alias[256];
        char hardlink_source[256];
        char hardlink_alias[256];
        snprintf(dot_source, sizeof dot_source, "%s/copy-dot.txt", root);
        snprintf(dot_alias, sizeof dot_alias, "%s/./copy-dot.txt", root);
        snprintf(symlink_source, sizeof symlink_source,
                 "%s/copy-symlink.txt", root);
        snprintf(symlink_alias, sizeof symlink_alias,
                 "%s/copy-symlink-alias.txt", root);
        snprintf(hardlink_source, sizeof hardlink_source,
                 "%s/copy-hardlink.txt", root);
        snprintf(hardlink_alias, sizeof hardlink_alias,
                 "%s/copy-hardlink-alias.txt", root);

        check(write_fixture(dot_source, "copy-alias-sentinel"),
              "dot-alias source created");
        check(rt_file_copy(
                  (const uint8_t*)dot_source, strlen(dot_source),
                  (const uint8_t*)dot_alias, strlen(dot_alias)
              ) == 0,
              "file copy rejects dot-path self alias");
        check(fixture_equals(dot_source, "copy-alias-sentinel"),
              "dot-path refusal preserves source");
        check(unlink(dot_source) == 0, "dot-alias source removed");

        check(write_fixture(symlink_source, "copy-alias-sentinel"),
              "symlink-alias source created");
        if (symlink("copy-symlink.txt", symlink_alias) == 0) {
            check(rt_file_copy(
                      (const uint8_t*)symlink_source, strlen(symlink_source),
                      (const uint8_t*)symlink_alias, strlen(symlink_alias)
                  ) == 0,
                  "file copy rejects symlink self alias");
            check(fixture_equals(symlink_source, "copy-alias-sentinel"),
                  "symlink refusal preserves source");
            check(unlink(symlink_alias) == 0, "copy symlink removed");
        } else {
            check(errno == EPERM || errno == EACCES || errno == ENOSYS ||
                  errno == EOPNOTSUPP,
                  "copy symlink unavailable only for supported reason");
        }
        check(unlink(symlink_source) == 0, "symlink-alias source removed");

        check(write_fixture(hardlink_source, "copy-alias-sentinel"),
              "hardlink-alias source created");
        if (link(hardlink_source, hardlink_alias) == 0) {
            check(rt_file_copy(
                      (const uint8_t*)hardlink_source, strlen(hardlink_source),
                      (const uint8_t*)hardlink_alias, strlen(hardlink_alias)
                  ) == 0,
                  "file copy rejects hardlink self alias");
            check(fixture_equals(hardlink_source, "copy-alias-sentinel"),
                  "hardlink refusal preserves source");
            check(unlink(hardlink_alias) == 0, "copy hardlink removed");
        } else {
            check(errno == EPERM || errno == EACCES || errno == ENOSYS ||
                  errno == EOPNOTSUPP || errno == EMLINK,
                  "copy hardlink unavailable only for supported reason");
        }
        check(unlink(hardlink_source) == 0, "hardlink-alias source removed");
#endif

        int64_t missing_hash = rt_file_hash_sha256(
            (const uint8_t*)copy, strlen(copy)
        );
        check((((uint64_t)missing_hash & 7ULL) == 1ULL) &&
              rt_string_len(missing_hash) == 0 &&
              rt_string_data(missing_hash) != NULL,
              "missing file hash returns tagged empty string");
        check(rt_string_free(missing_hash) == 1,
              "missing hash result freed");

        int64_t missing_listing = rt_dir_list(
            (const uint8_t*)copy, strlen(copy)
        );
        check((((uint64_t)missing_listing & 7ULL) == 1ULL) &&
              rt_array_len((SplArray*)(uintptr_t)missing_listing) == 0,
              "missing directory returns tagged empty listing");
        check(rt_array_free_deep(missing_listing) == 1,
              "missing directory listing freed");

        int64_t listing = rt_dir_list((const uint8_t*)root, strlen(root));
        check(array_contains_text(listing, "source.txt") &&
              array_contains_text(listing, "renamed.txt") &&
              array_contains_text(listing, "empty") &&
              array_contains_text(listing, "nested") &&
              array_contains_text(listing, "x"),
              "directory list provider returns fixture entries");
        check(rt_array_free_deep(listing) == 1, "directory listing freed");
        check(rt_dir_remove((const uint8_t*)empty, strlen(empty), 0) == 1,
              "nonrecursive directory remove succeeds");
        check(access(empty, F_OK) != 0, "empty directory removed");

#if !defined(_WIN32)
        char alias[] = "/tmp/simple-core-io-selfcheck-link-XXXXXX";
        int alias_fd = mkstemp(alias);
        int alias_ready = alias_fd >= 0;
        if (alias_ready) {
            close(alias_fd);
            alias_ready = unlink(alias) == 0 && symlink(root, alias) == 0;
        }
        check(alias_ready, "recursive-remove symlink fixture created");
        if (alias_ready) {
            check(rt_dir_remove(
                      (const uint8_t*)alias, strlen(alias), 1
                  ) == 0,
                  "recursive directory remove refuses top-level symlink");
            check(access(root, F_OK) == 0,
                  "symlink refusal leaves target directory intact");
            check(unlink(alias) == 0, "symlink fixture removed");
        } else if (alias_fd >= 0) {
            (void)unlink(alias);
        }
#endif

        const char* current_home = getenv("HOME");
        int home_was_set = current_home != NULL;
        char* saved_home = current_home ? strdup(current_home) : NULL;
        int home_saved = !home_was_set || saved_home != NULL;
        check(home_saved, "HOME snapshot allocated");
        if (home_saved) {
            int home_set = setenv("HOME", root, 1) == 0;
            check(home_set, "HOME temporarily points at fixture");
            if (home_set) {
                check(rt_dir_remove(
                          (const uint8_t*)root, strlen(root), 1
                      ) == 0,
                      "recursive directory remove refuses HOME");
                check(access(root, F_OK) == 0,
                      "HOME fixture remains after refused removal");
            }
            check(home_was_set
                      ? setenv("HOME", saved_home, 1) == 0
                      : unsetenv("HOME") == 0,
                  "HOME restored before fixture cleanup");
        }
        free(saved_home);

        check(rt_dir_remove((const uint8_t*)root, strlen(root), 1) == 1,
              "recursive directory remove succeeds");
        check(access(root, F_OK) != 0, "fixture tree removed");
        const char* cleanup_home = getenv("HOME");
        if (access(root, F_OK) == 0 &&
            (!cleanup_home || strcmp(cleanup_home, root) != 0)) {
            (void)unlink(source);
            (void)unlink(copy);
            (void)unlink(renamed);
            (void)unlink(one);
            (void)unlink(nested_file);
            (void)rmdir(empty);
            (void)rmdir(nested);
            (void)rmdir(root);
            check(access(root, F_OK) != 0,
                  "libc fallback removed fixture tree");
        }
    }

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
