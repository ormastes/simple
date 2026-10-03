#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_sosix_directory_roots_v1.h"
#include <assert.h>
#include <time.h>
#if defined(_WIN32)
#include <direct.h>
#define make_directory(p) _mkdir(p)
#else
#include <sys/mount.h>
#define make_directory(p) mkdir(p, 0700)
#endif

static void path(char *out, const char *base, const char *leaf) {
    int count = snprintf(out, RT_SDR_PATH_V1, "%s/%s", base, leaf);
    assert(count > 0 && count < RT_SDR_PATH_V1);
}
typedef struct ProbeWorker { const char *shared; const char *private_root; int failed; } ProbeWorker;
#if defined(_WIN32)
static DWORD WINAPI concurrent_check(void *input) {
#else
static void *concurrent_check(void *input) {
#endif
    ProbeWorker *worker = (ProbeWorker *)input;
    for (int i = 0; i < 32; ++i)
        if (rt_sdr_check_v1(worker->shared, worker->private_root) != 0) worker->failed = 1;
    return 0;
}
int main(int argc, char **argv) {
#if defined(__linux__)
    if (argc == 3 && !strcmp(argv[1], "--linux-backslash")) {
        assert(make_directory(argv[2]) == 0);
        char shared[RT_SDR_PATH_V1], private_root[RT_SDR_PATH_V1];
        char normalized[RT_SDR_PATH_V1], literal[RT_SDR_PATH_V1];
        path(shared, argv[2], "shared"); path(private_root, argv[2], "private");
        path(normalized, shared, "alias"); path(literal, argv[2], "shared\\alias");
        assert(make_directory(shared) == 0 && make_directory(private_root) == 0);
        assert(make_directory(normalized) == 0 && symlink(private_root, literal) == 0);
        int64_t token = rt_sdr_open_v1(normalized, private_root); assert(token > 0);
        assert(rt_sdr_close_v1(token) == 0);
        assert(rt_sdr_open_v1(literal, private_root) < 0);
        assert(rt_sdr_check_v1(literal, private_root) < 0);
        puts("directory-pair backslash PASS: normalized sibling accepted, original literal symlink rejected");
        return 0;
    }
    if (argc == 3 && !strcmp(argv[1], "--linux-mounts")) {
        assert(make_directory(argv[2]) == 0);
        char shared[RT_SDR_PATH_V1], backing[RT_SDR_PATH_V1], alias[RT_SDR_PATH_V1];
        char moved[RT_SDR_PATH_V1], shared_alias[RT_SDR_PATH_V1], child[RT_SDR_PATH_V1];
        path(shared, argv[2], "shared"); path(backing, argv[2], "backing");
        path(alias, argv[2], "alias"); path(moved, shared, "moved");
        path(shared_alias, argv[2], "shared-alias"); path(child, shared, "child-mount");
        assert(make_directory(shared) == 0 && make_directory(backing) == 0);
        assert(make_directory(alias) == 0 && make_directory(shared_alias) == 0);
        assert(make_directory(child) == 0);
        assert(mount(backing, alias, NULL, MS_BIND, NULL) == 0);
        int64_t token = rt_sdr_open_v1(shared, alias); assert(token > 0);
        assert(rename(backing, moved) == 0);
        assert(rt_sdr_revalidate_v1(token) == RT_SDR_CHANGED_V1);
        assert(rt_sdr_close_v1(token) == 0);
        assert(rt_sdr_open_v1(shared, alias) == RT_SDR_OVERLAP_V1);
        assert(mount(shared, shared_alias, NULL, MS_BIND, NULL) == 0);
        assert(rt_sdr_open_v1(shared, shared_alias) == RT_SDR_OVERLAP_V1);
        assert(mount("tmpfs", child, "tmpfs", 0, "size=1m") == 0);
        assert(rt_sdr_open_v1(shared, child) == RT_SDR_OVERLAP_V1);
        assert(umount(child) == 0 && umount(shared_alias) == 0 && umount(alias) == 0);
        assert(make_directory(backing) == 0);
        token = rt_sdr_open_v1(shared, alias); assert(token > 0);
        assert(mount(backing, alias, NULL, MS_BIND, NULL) == 0);
        assert(rt_sdr_revalidate_v1(token) == RT_SDR_CHANGED_V1);
        assert(rt_sdr_close_v1(token) == 0 && umount(alias) == 0);
        puts("directory-pair mount PASS: bind alias, moving backing ancestry, child filesystem, replacement");
        return 0;
    }
#endif
    if (argc == 4) {
        int64_t token = rt_sdr_open_v1(argv[2], argv[3]);
        int success = (!strcmp(argv[1], "--overlap") && token == RT_SDR_OVERLAP_V1) ||
            (!strcmp(argv[1], "--reject") && token < 0) ||
            (!strcmp(argv[1], "--accept") && token > 0 && rt_sdr_revalidate_v1(token) == 0);
        printf("directory-pair case=%s result=%lld accepted=%d\n", argv[1], (long long)token, success);
        if (token > 0) assert(rt_sdr_close_v1(token) == 0);
        return success ? 0 : 1;
    }
    if (argc != 2) return 64;
    /* The caller supplies a new isolated diagnostic root. No recursive cleanup. */
    assert(make_directory(argv[1]) == 0);
    char shared[RT_SDR_PATH_V1], private_root[RT_SDR_PATH_V1], nested[RT_SDR_PATH_V1];
    char moved[RT_SDR_PATH_V1], alias[RT_SDR_PATH_V1];
    path(shared, argv[1], "shared"); path(private_root, argv[1], "private");
    path(nested, shared, "nested"); path(moved, argv[1], "private-moved");
    path(alias, argv[1], "alias");
    assert(make_directory(shared) == 0 && make_directory(private_root) == 0 && make_directory(nested) == 0);
    int64_t token = rt_sdr_open_v1(shared, private_root);
    if (token <= 0) { fprintf(stderr, "positive root admission failed: %lld\n", (long long)token); return 1; }
    uint64_t receipt[RT_SDR_WORDS_V1];
    assert(rt_sdr_snapshot_v1(token, receipt, sizeof(receipt)) == 0);
    assert(receipt[1] != 0 && receipt[4] != 0 && receipt[6] == (uint64_t)token && receipt[7] == 1);
    assert(receipt[0] != receipt[3] || receipt[1] != receipt[4] || receipt[2] != receipt[5]);
    assert(rt_sdr_revalidate_v1(token) == 0);
    assert(rt_sdr_open_v1(shared, shared) == RT_SDR_OVERLAP_V1);
    assert(rt_sdr_open_v1(shared, nested) == RT_SDR_OVERLAP_V1);
    assert(rt_sdr_open_v1(nested, shared) == RT_SDR_OVERLAP_V1);
    assert(rt_sdr_open_v1("relative/path", private_root) < 0);
    assert(rt_sdr_open_v1(NULL, private_root) < 0);
#if defined(__linux__)
    assert(symlink(shared, alias) == 0);
    assert(rt_sdr_open_v1(alias, private_root) < 0);
    assert(rename(private_root, moved) == 0 && make_directory(private_root) == 0);
    assert(rt_sdr_revalidate_v1(token) == RT_SDR_CHANGED_V1);
#elif defined(_WIN32)
    /* Held ancestor handles deny DELETE sharing, blocking root replacement. */
    assert(rename(private_root, moved) != 0);
    char ancestor_moved[RT_SDR_PATH_V1];
    assert(snprintf(ancestor_moved, sizeof(ancestor_moved), "%s-moved", argv[1]) > 0);
    assert(rename(argv[1], ancestor_moved) != 0);
    assert(rt_sdr_revalidate_v1(token) == 0);
#endif
    assert(rt_sdr_close_v1(token) == 0);
    assert(rt_sdr_close_v1(token) == -EBADF);
    assert(rt_sdr_revalidate_v1(token) == -EBADF);
    assert(rt_sdr_snapshot_v1(token, receipt, sizeof(receipt)) == -EBADF);
    for (size_t i = 0; i < RT_SDR_WORDS_V1; ++i) assert(receipt[i] == 0);
    int64_t replacement = rt_sdr_open_v1(shared, private_root);
    assert(replacement > token);
    assert(rt_sdr_close_v1(replacement) == 0);
    int64_t slots[RT_SDR_SLOTS_V1];
    for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i) {
        slots[i] = rt_sdr_open_v1(shared, private_root); assert(slots[i] > 0);
    }
    assert(rt_sdr_open_v1(shared, private_root) == -EMFILE);
    for (size_t i = 0; i < RT_SDR_SLOTS_V1; ++i) assert(rt_sdr_close_v1(slots[i]) == 0);
    char cold[RT_SDR_PATH_V1], forbidden[RT_SDR_PATH_V1], absent[RT_SDR_PATH_V1];
    path(cold, argv[1], "cold/frontend"); path(forbidden, shared, "must-not-create/frontend");
    path(absent, shared, "must-not-create");
    assert(rt_sdr_check_v1(shared, cold) == 0);
    assert(rt_sdr_check_v1(shared, forbidden) == RT_SDR_OVERLAP_V1);
#if defined(_WIN32)
    assert(GetFileAttributesA(absent) == INVALID_FILE_ATTRIBUTES);
    HANDLE threads[4];
#else
    struct stat untouched; assert(lstat(absent, &untouched) != 0 && errno == ENOENT);
    pthread_t threads[4];
#endif
    ProbeWorker workers[4];
    for (size_t i = 0; i < 4; ++i) {
        workers[i].shared = shared; workers[i].private_root = cold; workers[i].failed = 0;
#if defined(_WIN32)
        threads[i] = CreateThread(NULL, 0, concurrent_check, &workers[i], 0, NULL);
        assert(threads[i] != NULL);
#else
        assert(pthread_create(&threads[i], NULL, concurrent_check, &workers[i]) == 0);
#endif
    }
    for (size_t i = 0; i < 4; ++i) {
#if defined(_WIN32)
        assert(WaitForSingleObject(threads[i], 30000) == WAIT_OBJECT_0); CloseHandle(threads[i]);
#else
        assert(pthread_join(threads[i], NULL) == 0);
#endif
        assert(!workers[i].failed);
    }
    clock_t begin = clock();
    for (int i = 0; i < 256; ++i) assert(rt_sdr_check_v1(shared, cold) == 0);
    printf("directory-pair warm_checks=256 cpu_ms=%.3f\n", 1000.0 * (clock() - begin) / CLOCKS_PER_SEC);
#if defined(__linux__)
    char cold_moved[RT_SDR_PATH_V1]; path(cold_moved, argv[1], "cold-moved");
    assert(rename(cold, cold_moved) == 0 && make_directory(cold) == 0);
    assert(rt_sdr_check_v1(shared, cold) == RT_SDR_CHANGED_V1);
    assert(rmdir(cold) == 0 && rename(cold_moved, cold) == 0);
    assert(rt_sdr_check_v1(shared, cold) == RT_SDR_CHANGED_V1);
#endif
    puts("directory-pair selfcheck PASS: siblings, identity, overlap, lifecycle, replacement, bounds, cold-create, concurrency");
    return 0;
}
