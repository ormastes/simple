/* rt_thread_local_{get,set}_i64 must round-trip full 64-bit values on every
 * target, including 32-bit ones (i686 Windows), where the TLS slot is 4 bytes,
 * and boxed cells must not leak or double-free on thread exit or key free. */
#ifdef _WIN32
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0600
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0600
#endif
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>

int64_t rt_thread_local_new(void);
int64_t rt_thread_local_get_i64(int64_t handle);
void rt_thread_local_set_i64(int64_t handle, int64_t value);
void rt_thread_local_free(int64_t handle);

#ifdef SIMPLE_SCALAR_TLS_SELFCHECK
int64_t spl_scalar_tls_selfcheck_allocs(void);
int64_t spl_scalar_tls_selfcheck_frees(void);
int64_t spl_scalar_tls_selfcheck_live(void);
void spl_scalar_tls_selfcheck_reset(void);
#endif

#if defined(SCALAR_TLS_FORCE_BOXED) || (UINTPTR_MAX < UINT64_MAX)
#define TEST_SCALAR_TLS_BOXED 1
#else
#define TEST_SCALAR_TLS_BOXED 0
#endif

/* Link stubs: runtime_thread.c references these, but the scalar TLS path
 * exercised here never calls them. */
int g_memtrack_enabled = 0;
int64_t rt_closure_func_ptr(int64_t c) { (void)c; return 0; }
void rt_closure_release(int64_t c) { (void)c; }
void rt_closure_retain(int64_t c) { (void)c; }
int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_value_unbox_int(int64_t v) { return v; }
void spl_memtrack_record(void) {}
void spl_memtrack_unrecord(void) {}
#if defined(SIMPLE_CORE_C_STANDALONE) && !defined(SIMPLE_RUNTIME_THREAD_CPU_COUNT_OWNER)
int64_t spl_thread_cpu_count(void) { return 1; }
#endif

typedef struct {
    int64_t k1;
    int64_t k2;
    int index;
    int ok;
} WorkerTask;

static int run_worker_body(WorkerTask* task) {
    if (rt_thread_local_get_i64(task->k1) != 0) return 0;
    if (task->k2 > 0 && rt_thread_local_get_i64(task->k2) != 0) return 0;

    int64_t v1a = (int64_t)(0x1000000000000000ULL + (uint64_t)task->index);
    int64_t v1b = (int64_t)(0x2222333344445555ULL ^ (uint64_t)(task->index + 1));
    rt_thread_local_set_i64(task->k1, v1a);
    if (rt_thread_local_get_i64(task->k1) != v1a) return 0;
    /* Overwrite on same thread+key to verify boxed cell reuse (no leak). */
    rt_thread_local_set_i64(task->k1, v1b);
    if (rt_thread_local_get_i64(task->k1) != v1b) return 0;

    if (task->k2 > 0) {
        int64_t v2 = -1000LL - (int64_t)task->index;
        rt_thread_local_set_i64(task->k2, v2);
        if (rt_thread_local_get_i64(task->k2) != v2) return 0;
        if (rt_thread_local_get_i64(task->k1) != v1b) return 0;
    }
    return 1;
}

#ifdef _WIN32
static DWORD WINAPI win_worker_proc(LPVOID opaque) {
    WorkerTask* task = (WorkerTask*)opaque;
    task->ok = run_worker_body(task);
    return 0;
}

static int run_worker_batch(int count, int64_t k1, int64_t k2) {
    WorkerTask tasks[8];
    HANDLE threads[8];
    if (count <= 0 || count > 8) return 0;
    for (int i = 0; i < count; i++) {
        tasks[i].k1 = k1;
        tasks[i].k2 = k2;
        tasks[i].index = i;
        tasks[i].ok = 0;
        threads[i] = CreateThread(NULL, 0, win_worker_proc, &tasks[i], 0, NULL);
        if (!threads[i]) {
            for (int j = 0; j < i; j++) {
                WaitForSingleObject(threads[j], INFINITE);
                CloseHandle(threads[j]);
            }
            return 0;
        }
    }
    int all_ok = 1;
    for (int i = 0; i < count; i++) {
        if (WaitForSingleObject(threads[i], INFINITE) != WAIT_OBJECT_0) all_ok = 0;
        CloseHandle(threads[i]);
        if (!tasks[i].ok) all_ok = 0;
    }
    return all_ok;
}
#else
static void* posix_worker_proc(void* opaque) {
    WorkerTask* task = (WorkerTask*)opaque;
    task->ok = run_worker_body(task);
    return NULL;
}

static int run_worker_batch(int count, int64_t k1, int64_t k2) {
    WorkerTask tasks[8];
    pthread_t threads[8];
    if (count <= 0 || count > 8) return 0;
    for (int i = 0; i < count; i++) {
        tasks[i].k1 = k1;
        tasks[i].k2 = k2;
        tasks[i].index = i;
        tasks[i].ok = 0;
        if (pthread_create(&threads[i], NULL, posix_worker_proc, &tasks[i]) != 0) {
            for (int j = 0; j < i; j++) pthread_join(threads[j], NULL);
            return 0;
        }
    }
    int all_ok = 1;
    for (int i = 0; i < count; i++) {
        if (pthread_join(threads[i], NULL) != 0) all_ok = 0;
        if (!tasks[i].ok) all_ok = 0;
    }
    return all_ok;
}
#endif

#if defined(SIMPLE_SCALAR_TLS_SELFCHECK) && defined(_WIN32)
typedef struct {
    int64_t key;
    HANDLE ready_event;
    HANDLE release_event;
    int ok;
} LiveWorkerArgs;

static DWORD WINAPI live_worker_proc(LPVOID opaque) {
    LiveWorkerArgs* args = (LiveWorkerArgs*)opaque;
    rt_thread_local_set_i64(args->key, 0x777788889999aaaall);
    args->ok = (rt_thread_local_get_i64(args->key) == 0x777788889999aaaall);
    SetEvent(args->ready_event);
    if (WaitForSingleObject(args->release_event, INFINITE) != WAIT_OBJECT_0) {
        args->ok = 0;
    }
    return 0;
}

static DWORD WINAPI readonly_worker_proc(LPVOID opaque) {
    int64_t key = *(int64_t*)opaque;
    return (rt_thread_local_get_i64(key) == 0) ? 0 : 1;
}
#endif

#ifdef SIMPLE_SCALAR_TLS_SELFCHECK
static int expect_counts(const char* label, int64_t exp_allocs, int64_t exp_frees, int64_t exp_live) {
    int64_t allocs = spl_scalar_tls_selfcheck_allocs();
    int64_t frees = spl_scalar_tls_selfcheck_frees();
    int64_t live = spl_scalar_tls_selfcheck_live();
    if (allocs != exp_allocs || frees != exp_frees || live != exp_live) {
        printf("FAIL %s: allocs=%" PRId64 " (exp %" PRId64 "), frees=%" PRId64
               " (exp %" PRId64 "), live=%" PRId64 " (exp %" PRId64 ")\n",
               label, allocs, exp_allocs, frees, exp_frees, live, exp_live);
        return 0;
    }
    return 1;
}
#endif

int main(void) {
    int64_t h = rt_thread_local_new();
    if (h <= 0) { puts("FAIL new"); return 1; }
    if (rt_thread_local_get_i64(h) != 0) { puts("FAIL default"); return 1; }
    const int64_t vals[] = {0x123456789abcdef0LL, -1, INT64_MIN, 42};
    for (int i = 0; i < 4; i++) {
        rt_thread_local_set_i64(h, vals[i]);
        if (rt_thread_local_get_i64(h) != vals[i]) { printf("FAIL value %d\n", i); return 1; }
    }
    rt_thread_local_free(h);
    int64_t h2 = rt_thread_local_new();
    if (h2 <= 0 || rt_thread_local_get_i64(h2) != 0) { puts("FAIL reuse default"); return 1; }
    rt_thread_local_set_i64(h2, 7);
    if (rt_thread_local_get_i64(h2) != 7) { puts("FAIL reuse value"); return 1; }
    rt_thread_local_free(h2);

#ifdef SIMPLE_SCALAR_TLS_SELFCHECK
    {
        int64_t exp_roundtrip = TEST_SCALAR_TLS_BOXED ? 2 : 0;
        if (!expect_counts("roundtrip", exp_roundtrip, exp_roundtrip, 0)) return 1;
    }
#endif

    /* Portable multi-thread round-trip + isolation without worker-side free. */
    {
        int64_t k1 = rt_thread_local_new();
        int64_t k2 = rt_thread_local_new();
        if (k1 <= 0 || k2 <= 0) { puts("FAIL mt new"); return 1; }
        rt_thread_local_set_i64(k1, 0x0f0e0d0c0b0a0908LL);
        rt_thread_local_set_i64(k2, -99);
        if (!run_worker_batch(8, k1, k2)) { puts("FAIL mt workers"); return 1; }
        if (rt_thread_local_get_i64(k1) != 0x0f0e0d0c0b0a0908LL ||
            rt_thread_local_get_i64(k2) != -99) {
            puts("FAIL mt main isolated");
            return 1;
        }
        rt_thread_local_free(k1);
        rt_thread_local_free(k2);
    }

#ifdef SIMPLE_SCALAR_TLS_SELFCHECK
    /* Case 1: Exiting worker threads release their cells before rt_thread_local_free,
     * and freeing keys afterwards does not double-free. */
    spl_scalar_tls_selfcheck_reset();
    {
        int64_t k1 = rt_thread_local_new();
        int64_t k2 = rt_thread_local_new();
        if (k1 <= 0 || k2 <= 0) { puts("FAIL exit-leak new"); return 1; }
        if (!run_worker_batch(8, k1, k2)) { puts("FAIL exit-leak workers"); return 1; }
        int64_t exp = TEST_SCALAR_TLS_BOXED ? 16 : 0;
        if (!expect_counts("after workers exit", exp, exp, 0)) return 1;
        rt_thread_local_free(k1);
        rt_thread_local_free(k2);
        if (!expect_counts("after free post-exit", exp, exp, 0)) return 1;
    }

    /* Case 2: Main thread sets + workers set and exit + main frees key (including
     * duplicate free): main's cell freed exactly once, zero leak, zero double-free. */
    spl_scalar_tls_selfcheck_reset();
    {
        int64_t k = rt_thread_local_new();
        if (k <= 0) { puts("FAIL main+workers new"); return 1; }
        rt_thread_local_set_i64(k, 0x5555555512345678LL);
        if (!run_worker_batch(4, k, 0)) { puts("FAIL main+workers batch"); return 1; }
        if (rt_thread_local_get_i64(k) != 0x5555555512345678LL) {
            puts("FAIL main+workers value");
            return 1;
        }
        if (!expect_counts("main+workers pre-free",
                           TEST_SCALAR_TLS_BOXED ? 5 : 0,
                           TEST_SCALAR_TLS_BOXED ? 4 : 0,
                           TEST_SCALAR_TLS_BOXED ? 1 : 0)) return 1;
        rt_thread_local_free(k);
        rt_thread_local_free(k);
        int64_t exp = TEST_SCALAR_TLS_BOXED ? 5 : 0;
        if (!expect_counts("main+workers post-free", exp, exp, 0)) return 1;
    }

#ifdef _WIN32
    /* Case 3 (Win32 FLS): Freeing key while another worker thread is still live
     * frees both main and live worker cells in FlsFree, and worker exit later
     * does not double-free. */
    spl_scalar_tls_selfcheck_reset();
    {
        int64_t k = rt_thread_local_new();
        if (k <= 0) { puts("FAIL live-free new"); return 1; }
        rt_thread_local_set_i64(k, 111);
        LiveWorkerArgs args;
        args.key = k;
        args.ready_event = CreateEventA(NULL, TRUE, FALSE, NULL);
        args.release_event = CreateEventA(NULL, TRUE, FALSE, NULL);
        args.ok = 0;
        if (!args.ready_event || !args.release_event) { puts("FAIL events"); return 1; }
        HANDLE th = CreateThread(NULL, 0, live_worker_proc, &args, 0, NULL);
        if (!th) { puts("FAIL live-free thread"); return 1; }
        if (WaitForSingleObject(args.ready_event, INFINITE) != WAIT_OBJECT_0) {
            puts("FAIL wait ready");
            return 1;
        }
        if (!expect_counts("live-free before free",
                           TEST_SCALAR_TLS_BOXED ? 2 : 0, 0,
                           TEST_SCALAR_TLS_BOXED ? 2 : 0)) return 1;
        rt_thread_local_free(k);
        if (!expect_counts("live-free after FlsFree",
                           TEST_SCALAR_TLS_BOXED ? 2 : 0,
                           TEST_SCALAR_TLS_BOXED ? 2 : 0, 0)) return 1;
        SetEvent(args.release_event);
        if (WaitForSingleObject(th, INFINITE) != WAIT_OBJECT_0 || !args.ok) {
            puts("FAIL live-free join");
            return 1;
        }
        CloseHandle(th);
        CloseHandle(args.ready_event);
        CloseHandle(args.release_event);
        if (!expect_counts("live-free post worker exit",
                           TEST_SCALAR_TLS_BOXED ? 2 : 0,
                           TEST_SCALAR_TLS_BOXED ? 2 : 0, 0)) return 1;
    }

    /* Case 4: Read-only key never allocates cells. */
    spl_scalar_tls_selfcheck_reset();
    {
        int64_t k = rt_thread_local_new();
        if (k <= 0 || rt_thread_local_get_i64(k) != 0) { puts("FAIL readonly"); return 1; }
        HANDLE th = CreateThread(NULL, 0, readonly_worker_proc, &k, 0, NULL);
        if (!th) { puts("FAIL readonly thread"); return 1; }
        DWORD code = 1;
        if (WaitForSingleObject(th, INFINITE) != WAIT_OBJECT_0 ||
            !GetExitCodeThread(th, &code) || code != 0) {
            puts("FAIL readonly join");
            return 1;
        }
        CloseHandle(th);
        rt_thread_local_free(k);
        if (!expect_counts("readonly", 0, 0, 0)) return 1;
    }
#endif

    /* Case 5: Handle/slot churn leaves zero live cells. */
    spl_scalar_tls_selfcheck_reset();
    {
        int64_t stale = 0;
        for (int i = 0; i < 256; i++) {
            int64_t fresh = rt_thread_local_new();
            if (fresh <= stale || rt_thread_local_get_i64(fresh) != 0) {
                printf("FAIL churn new %d\n", i);
                return 1;
            }
            rt_thread_local_set_i64(fresh, (int64_t)i + 1);
            if (rt_thread_local_get_i64(fresh) != (int64_t)i + 1 ||
                rt_thread_local_get_i64(stale) != 0) {
                printf("FAIL churn value %d\n", i);
                return 1;
            }
            rt_thread_local_free(fresh);
            stale = fresh;
        }
        int64_t exp = TEST_SCALAR_TLS_BOXED ? 256 : 0;
        if (!expect_counts("churn", exp, exp, 0)) return 1;
    }
#endif

    puts("PASS rt_thread_local_i64");
    return 0;
}
