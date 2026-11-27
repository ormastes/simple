/* Regression: a slow operation on one cache-host capability must not stall
 * operations on any other capability (the global list lock used to be held
 * across the 64 MB pread + verify re-read and across fsync/rename), and
 * closing a capability while another thread holds a reference must not be a
 * use-after-free.
 *
 * Deterministic slow I/O: the provider is #included so the read primitive
 * (ReadFile on Windows, pread on Unix) can be wrapped; the wrapper sleeps
 * HOLD_MS per call on one chosen file only.  No product-code hook is needed.
 *
 * Build (clang + lld only; add -fsanitize=address,undefined or thread where
 * the target supports it):
 *   clang -std=c11 -O1 -g rt_cache_host_per_cap_lock_selfcheck.c -o t.exe   (Windows)
 *   clang -std=c11 -O1 -g -pthread rt_cache_host_per_cap_lock_selfcheck.c -o t (Unix)
 * Exit 0 and a final "PASS" line on success. */
#ifdef _WIN32
#include <windows.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define HOLD_MS 10
static HANDLE slow_file;
static BOOL probe_ReadFile(HANDLE h, LPVOID b, DWORD n, LPDWORD g, LPOVERLAPPED o) {
    if (h == slow_file) Sleep(HOLD_MS);
    return ReadFile(h, b, n, g, o);
}
#define ReadFile probe_ReadFile
#include "../runtime_cache_host_authority_v1.c"
#undef ReadFile
typedef HANDLE thread_t;
#define THREAD_FN(name) static DWORD WINAPI name(LPVOID arg)
#define THREAD_RET return 0
static thread_t spawn(DWORD (WINAPI *f)(LPVOID), void *a) { return CreateThread(NULL, 0, f, a, 0, NULL); }
static void join(thread_t t) { WaitForSingleObject(t, INFINITE); CloseHandle(t); }
static void sleep_ms(int ms) { Sleep((DWORD)ms); }
static double now_ms(void) { LARGE_INTEGER f, c; QueryPerformanceFrequency(&f); QueryPerformanceCounter(&c); return 1000.0 * (double)c.QuadPart / (double)f.QuadPart; }
#else
#define _GNU_SOURCE
#include <unistd.h>
#include <time.h>
#include <sched.h>
#define HOLD_MS 10
static int slow_fd = -1;
static ssize_t probe_pread(int fd, void *b, size_t n, off_t o) {
    if (fd == slow_fd) { struct timespec ts = {0, HOLD_MS * 1000000L}; nanosleep(&ts, NULL); }
    return pread(fd, b, n, o);
}
#define pread probe_pread
#include "../runtime_cache_host_authority_v1.c"
#undef pread
typedef pthread_t thread_t;
#define THREAD_FN(name) static void *name(void *arg)
#define THREAD_RET return NULL
static thread_t spawn(void *(*f)(void *), void *a) { pthread_t t; pthread_create(&t, NULL, f, a); return t; }
static void join(thread_t t) { pthread_join(t, NULL); }
static void sleep_ms(int ms) { struct timespec ts = {ms / 1000, (ms % 1000) * 1000000L}; nanosleep(&ts, NULL); }
static double now_ms(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (double)t.tv_sec * 1000.0 + (double)t.tv_nsec / 1e6; }
#endif

#define BIG_BYTES 65536  /* 17 slow reads per pread_receipt => ~170 ms hold */
#define CHECK(x) do { if (!(x)) { fprintf(stderr, "FAIL line %d: %s\n", __LINE__, #x); exit(1); } } while (0)

static int64_t g_root, g_big, g_small;
static volatile int g_big_done;
static int64_t g_big_results[8];

static int cmp_double(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return x < y ? -1 : x > y; }

static void write_file(const char *dir, const char *name, size_t n) {
    char path[512]; snprintf(path, sizeof path, "%s/%s", dir, name);
    FILE *f = fopen(path, "wb"); CHECK(f);
    for (size_t i = 0; i < n; ++i) fputc((int)(i * 31 + 7) & 0xff, f);
    CHECK(fclose(f) == 0);
}
static int64_t open_named(int64_t root, const char *name) {
    return rt_cache_host_open_read_v1(root, (const uint8_t *)name, (int64_t)strlen(name));
}
#ifdef _WIN32
static HANDLE file_of(int64_t token) { struct cw_cap *c = cw_find(token); return c ? cw_file(c) : NULL; }
#else
static int fd_of(int64_t token) { struct cache_cap *c = find_cap(token); return c ? c->fd : -1; }
#endif

THREAD_FN(big_reader) {
    (void)arg;
    static uint8_t out[BIG_BYTES];
    for (int i = 0; i < 6; ++i) g_big_results[i] = rt_cache_host_pread_receipt_v1(g_big, 0, out, BIG_BYTES);
    g_big_done = 1;
    THREAD_RET;
}

/* Part 1: p99 latency of an unrelated capability while a slow receipt read runs. */
static void stress_other_cap_latency(void) {
    enum { N = 300 };
    static double lat[N];
    thread_t t = spawn(big_reader, NULL);
    sleep_ms(20); /* let the reader enter its slow section */
    int samples = 0;
    while (samples < N && !g_big_done) {
        double t0 = now_ms();
        int64_t r = rt_cache_host_size_v1(g_small, 1 << 20);
        lat[samples++] = now_ms() - t0;
        CHECK(r == 4096);
        sleep_ms(1);
    }
    join(t);
    for (int i = 0; i < 6; ++i) CHECK(g_big_results[i] == BIG_BYTES);
    CHECK(samples >= 1);
    qsort(lat, (size_t)samples, sizeof lat[0], cmp_double);
    double p99 = lat[(samples * 99) / 100], max = lat[samples - 1];
    printf("other-cap size_v1: %d samples, p99=%.2f ms, max=%.2f ms (slow reader holds ~%d ms per call)\n", samples, p99, max, 17 * HOLD_MS);
    CHECK(p99 < 25.0);
}

struct hammer { int64_t token; volatile int stop; };
THREAD_FN(hammer_thread) {
    struct hammer *h = (struct hammer *)arg;
    uint8_t out[4096];
    while (!h->stop) {
        (void)rt_cache_host_size_v1(h->token, 1 << 20);
        (void)rt_cache_host_pread_receipt_v1(h->token, 0, out, sizeof out);
        (void)rt_cache_host_fsync_v1(h->token);
    }
    THREAD_RET;
}
THREAD_FN(close_in_flight) { (void)arg; static uint8_t out[BIG_BYTES]; g_big_results[0] = rt_cache_host_pread_receipt_v1(g_big, 0, out, BIG_BYTES); THREAD_RET; }

/* Part 2: close while another thread holds a reference. */
static void close_with_reference_held(void) {
    /* 2a: a slow in-flight read holds a reference; close must wait for it, not free under it. */
    g_big_results[0] = 12345;
    thread_t t = spawn(close_in_flight, NULL);
    sleep_ms(30);
    int64_t rc = rt_cache_host_close_v1(g_big);
    join(t);
    CHECK(rc >= 0 || rc == -1);
    CHECK(g_big_results[0] == BIG_BYTES || g_big_results[0] < 0);
    CHECK(rt_cache_host_size_v1(g_big, 1 << 20) == -1);      /* token is dead */
    CHECK(rt_cache_host_close_v1(g_big) == -1);              /* double close rejected */

    /* 2b: hammer a token from several threads while closing it, repeatedly. */
    for (int round = 0; round < 200; ++round) {
        struct hammer h; h.token = open_named(g_root, "small.bin"); h.stop = 0; CHECK(h.token > 0);
        thread_t th[4]; for (int i = 0; i < 4; ++i) th[i] = spawn(hammer_thread, &h);
        sleep_ms(round % 3);
        CHECK(rt_cache_host_close_v1(h.token) == 0);
        h.stop = 1; for (int i = 0; i < 4; ++i) join(th[i]);
        CHECK(rt_cache_host_size_v1(h.token, 1 << 20) == -1);
    }
}

int main(void) {
    char dir[512];
#ifdef _WIN32
    char tmp[400]; DWORD n = GetTempPathA(sizeof tmp, tmp); CHECK(n > 0 && n < sizeof tmp);
    snprintf(dir, sizeof dir, "%sper_cap_lock_%lu_%lu", tmp, (unsigned long)GetCurrentProcessId(), (unsigned long)GetTickCount());
    CHECK(CreateDirectoryA(dir, NULL));
#else
    snprintf(dir, sizeof dir, "/tmp/per-cap-lock-XXXXXX"); CHECK(mkdtemp(dir));
#endif
    write_file(dir, "big.bin", BIG_BYTES);
    write_file(dir, "small.bin", 4096);
    g_root = rt_cache_host_open_root_v1((const uint8_t *)dir, (int64_t)strlen(dir)); CHECK(g_root > 0);
    g_big = open_named(g_root, "big.bin"); g_small = open_named(g_root, "small.bin");
    CHECK(g_big > 0 && g_small > 0);
#ifdef _WIN32
    slow_file = file_of(g_big); CHECK(slow_file);
#else
    slow_fd = fd_of(g_big); CHECK(slow_fd >= 0);
#endif
    stress_other_cap_latency();
    close_with_reference_held();
    CHECK(rt_cache_host_close_v1(g_small) == 0);
    CHECK(rt_cache_host_close_v1(g_root) == 0);
    printf("PASS\n");
    return 0;
}
