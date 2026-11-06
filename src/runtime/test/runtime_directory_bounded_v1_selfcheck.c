/* Real POSIX filesystem calls against the exact shared native owner. Text
 * handles use a minimal ABI shim; this does not qualify Simple code generation. */
#include "runtime.h"
#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <dirent.h>
#include <fcntl.h>
#include <unistd.h>
#include <sched.h>
#include <sys/stat.h>

typedef struct { const uint8_t *data; int64_t size; } test_text;
int64_t rt_string_len(int64_t t) { return t ? ((test_text *)(uintptr_t)t)->size : -1; }
const uint8_t *rt_string_data(int64_t t) { return t ? ((test_text *)(uintptr_t)t)->data : NULL; }
int64_t rt_string_new(const uint8_t *p, uint64_t n) {
    test_text *t = malloc(sizeof(*t) + (size_t)n + 1);
    assert(t);
    uint8_t *copy = (uint8_t *)(t + 1);
    if (n) memcpy(copy, p, (size_t)n);
    copy[n] = 0; t->data = copy; t->size = (int64_t)n;
    return (int64_t)(uintptr_t)t;
}
static _Atomic size_t outstanding, peak, calls, fail_call;
typedef struct { size_t size; } allocation_header;
static void *checked_alloc(size_t n) {
    ++calls;
    if (fail_call && calls == fail_call) return NULL;
    allocation_header *a = malloc(sizeof(*a) + n);
    assert(a); a->size = n; outstanding += n;
    if (outstanding > peak) peak = outstanding;
    return a + 1;
}
static void checked_free(void *p) {
    if (!p) return;
    allocation_header *a = (allocation_header *)p - 1;
    assert(outstanding >= a->size); outstanding -= a->size; free(a);
}
static int close_calls, fail_close;
static int checked_closedir(DIR *d) {
    ++close_calls;
    int result = closedir(d);
    return fail_close ? -1 : result;
}
/* Test-only compile-time hook: fail after one real non-dot entry has been
 * returned, so the provider must discard already allocated partial results. */
static _Atomic int inject_readdir_error, returned_real_entries;
static struct dirent *checked_readdir(DIR *directory) {
    if (inject_readdir_error && returned_real_entries >= 1) {
        errno = EIO;
        return NULL;
    }
    struct dirent *entry = readdir(directory);
    if (entry && strcmp(entry->d_name, ".") && strcmp(entry->d_name, ".."))
        ++returned_real_entries;
    return entry;
}
#define SIMPLE_DIRECTORY_READDIR_V1 checked_readdir
#define SIMPLE_DIRECTORY_ALLOC_V1 checked_alloc
#define SIMPLE_DIRECTORY_FREE_V1 checked_free
#define SIMPLE_DIRECTORY_CLOSEDIR_V1 checked_closedir
#include "runtime_core_exports.c"

static int64_t list(const char *path, int64_t entries, int64_t bytes) {
    test_text t = {(const uint8_t *)path, (int64_t)strlen(path)};
    return rt_directory_list_bounded_v1((int64_t)(uintptr_t)&t, entries, bytes);
}
static int64_t probe(const char *path) {
    test_text t = {(const uint8_t *)path, (int64_t)strlen(path)};
    return rt_directory_path_probe_v1((int64_t)(uintptr_t)&t);
}
static void write_file(const char *path) {
    int fd = open(path, O_WRONLY | O_CREAT | O_EXCL, 0600);
    assert(fd >= 0); assert(write(fd, "abc", 3) == 3); assert(close(fd) == 0);
}
static _Atomic int64_t racing_token;
static _Atomic int reader_ready;
static void *race_reader(void *unused) {
    (void)unused;
    atomic_store(&reader_ready, 1);
    for (int i = 0; i < 20000; ++i) {
        int64_t token = atomic_load(&racing_token);
        int64_t count = rt_directory_list_count_v1(token);
        assert(count == -1 || count == 1);
        int64_t kind = rt_directory_entry_kind_v1(token, 0);
        int64_t size = rt_directory_entry_size_v1(token, 0);
        assert(kind == -1 || kind == 1);
        assert(size == -1 || size == 3);
        int64_t name = rt_directory_entry_name_v1(token, 0);
        int64_t length = rt_string_len(name);
        assert(length == 0 || (length == 1 && rt_string_data(name)[0] == 'a'));
        free((void *)(uintptr_t)name);
    }
    return NULL;
}
static int new_controls(void) {
    char root[] = "/tmp/simple-bounded-directory-race-XXXXXX";
    assert(mkdtemp(root));
    char a[4096]; snprintf(a, sizeof(a), "%s/a", root); write_file(a);
    int closed_before = close_calls;
    returned_real_entries = 0; inject_readdir_error = 1;
    assert(list(root, 4, 100) == -4);
    assert(returned_real_entries == 1 && outstanding == 0);
    assert(close_calls == closed_before + 1);
    inject_readdir_error = 0;
    pthread_t reader;
    assert(pthread_create(&reader, NULL, race_reader, NULL) == 0);
    while (!atomic_load(&reader_ready)) sched_yield();
    for (int i = 0; i < 2000; ++i) {
        int64_t token = list(root, 1, 2);
        assert(token > 0);
        atomic_store(&racing_token, token);
        assert(rt_directory_list_free_v1(token) == 1);
        assert(rt_directory_list_free_v1(token) == -1);
    }
    assert(pthread_join(reader, NULL) == 0);
    assert(rt_directory_list_count_v1(atomic_load(&racing_token)) == -1);
    assert(outstanding == 0);
    assert(unlink(a) == 0 && rmdir(root) == 0);
    puts("PASS new native controls: readdir errno after partial allocation; concurrent accessor/free/reuse");
    return 0;
}
int main(int argc, char **argv) {
    if (argc == 2 && strcmp(argv[1], "--new-controls") == 0) return new_controls();

    char root[] = "/tmp/simple-bounded-directory-XXXXXX";
    assert(mkdtemp(root));
    int64_t h = list(root, 0, 0);
    assert(h > 0 && rt_directory_list_count_v1(h) == 0);
    assert(rt_directory_list_free_v1(h) == 1);
    assert(rt_directory_list_free_v1(h) == -1);
    assert(rt_directory_list_count_v1(h) == -1);
    int64_t old = h;
    h = probe(root);
    assert(h > 0 && h != old && rt_directory_entry_kind_v1(h, 0) == 2);
    assert(rt_directory_list_count_v1(old) == -1);
    assert(rt_directory_entry_kind_v1(INT64_MAX, 0) == -1);
    assert(rt_directory_list_free_v1(h) == 1);
    assert(outstanding == 0);

    char a[4096], b[4096], loop[4096], missing[4096];
    snprintf(a, sizeof(a), "%s/a", root); snprintf(b, sizeof(b), "%s/b", root);
    snprintf(loop, sizeof(loop), "%s/loop", root); snprintf(missing, sizeof(missing), "%s/missing", root);
    write_file(a); write_file(b);
    calls = 0; peak = 0;
    assert(list(root, 1, 100) == -2 && outstanding == 0);
    assert(calls == 3); /* listing + fixed metadata + ONE name, never second */
    assert(peak <= sizeof(spl_directory_listing_v1) + sizeof(spl_directory_entry_v1) + 2);
    calls = 0;
    assert(list(root, 2, 1) == -3 && outstanding == 0);
    assert(calls == 2); /* no name allocation before its budget admission */
    h = list(root, 2, 4);
    assert(h > 0 && rt_directory_list_count_v1(h) == 2);
    for (int i = 0; i < 2; ++i) {
        assert(rt_directory_entry_kind_v1(h, i) == 1);
        assert(rt_directory_entry_size_v1(h, i) == 3);
        int64_t name = rt_directory_entry_name_v1(h, i);
        assert(rt_string_len(name) == 1); free((void *)(uintptr_t)name);
    }
    assert(rt_directory_list_free_v1(h) == 1 && outstanding == 0);
    assert(symlink(root, loop) == 0);
    h = list(root, 3, 9);
    assert(h > 0 && rt_directory_list_count_v1(h) == 3);
    int saw_link = 0;
    for (int i = 0; i < 3; ++i) if (rt_directory_entry_kind_v1(h, i) == 3) ++saw_link;
    assert(saw_link == 1 && rt_directory_list_free_v1(h) == 1);
    assert(list(loop, 4, 100) == -7); /* no traversal of cycle */
    char trailing[4100];
    snprintf(trailing, sizeof(trailing), "%s/", loop);
    assert(list(trailing, 4, 100) == -7);
    h = probe(trailing);
    assert(h > 0 && rt_directory_entry_kind_v1(h, 0) == 3);
    assert(rt_directory_list_free_v1(h) == 1);
    assert(list(a, 4, 100) == -7);
    assert(list(missing, 4, 100) == -4);
    h = probe(missing);
    assert(h > 0 && rt_directory_entry_kind_v1(h, 0) == 0);
    assert(rt_directory_list_free_v1(h) == 1);
    h = probe(loop);
    assert(h > 0 && rt_directory_entry_kind_v1(h, 0) == 3);
    assert(rt_directory_list_free_v1(h) == 1);
    assert(list(root, 65537, 1) == -1 && list(root, 1, 16777217) == -1);
    test_text nul = {(const uint8_t *)"/tmp\0suffix", 11};
    assert(rt_directory_path_probe_v1((int64_t)(uintptr_t)&nul) == -1);

    for (size_t failure = 1; failure <= 3; ++failure) {
        calls = 0; fail_call = failure; int closed_before = close_calls;
        assert(list(root, 3, 100) == -6);
        assert(outstanding == 0 && close_calls == closed_before + 1);
    }
    fail_call = 0; fail_close = 1;
    assert(list(root, 3, 100) == -4 && outstanding == 0);
    fail_close = 0;
    int64_t owners[64];
    for (int i = 0; i < 64; ++i) { owners[i] = probe(missing); assert(owners[i] > 0); }
    assert(probe(root) == -9);
    for (int i = 0; i < 64; ++i) assert(rt_directory_list_free_v1(owners[i]) == 1);
    assert(outstanding == 0);
    assert(unlink(loop) == 0 && unlink(a) == 0 && unlink(b) == 0 && rmdir(root) == 0);
    puts("PASS native bounded directory: complete EOF, preallocation budgets, nofollow kinds, errors, close, stale owners, 64-owner cap");
    return 0;
}
