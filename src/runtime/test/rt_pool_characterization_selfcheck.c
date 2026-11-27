/* Characterization of the native task pool (rt_pool_*), run against BOTH
 * C pool lanes so a refactor of either can be checked for behaviour drift:
 *
 *   lane A: runtime_pool.c   (Rust-seed simple-runtime lane)   -DRT_POOL_CHAR_LANE_A
 *   lane B: runtime_thread.c (core-C seed/simple lanes)
 *
 * Only exported rt_pool_* symbols are used. Each lane's exact return codes are
 * golden values; where the lanes legitimately differ the check is lane-guarded.
 * Build + run (all lanes, sanitizers): scripts/check/check-rt-pool-characterization.shs
 *
 * The pool is process-global (started once, parallelism grows only), so cases
 * run in a fixed order: clamp bounds before the pool starts, then one worker
 * (FIFO, exact state counters), then many workers (races, stress). */
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#if defined(_WIN32) || defined(_WIN64)
#include <windows.h>
typedef HANDLE char_thread_t;
static void char_yield(void) { Sleep(0); }
static void char_sleep_ms(int ms) { Sleep((DWORD)ms); }
static uint64_t char_now_ms(void) { return (uint64_t)GetTickCount64(); }
#else
#include <pthread.h>
#include <sched.h>
#include <time.h>
#include <unistd.h>
typedef pthread_t char_thread_t;
static void char_yield(void) { sched_yield(); }
static void char_sleep_ms(int ms) { usleep((useconds_t)ms * 1000u); }
static uint64_t char_now_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000u + (uint64_t)ts.tv_nsec / 1000000u;
}
#endif

extern int64_t rt_pool_set_parallelism(int64_t workers);
extern int64_t rt_pool_get_parallelism(void);
extern int64_t rt_pool_uses_global_fifo_queue(void);
extern int64_t rt_pool_uses_work_stealing(void);
extern int64_t rt_pool_safepoint(void);
extern int64_t rt_pool_submit(int64_t arg0, int64_t arg1);
extern int64_t rt_pool_is_done(int64_t handle);
extern int64_t rt_pool_join(int64_t handle);
extern int64_t rt_pool_state_create_v1(int64_t capacity);
extern int64_t rt_pool_state_try_submit_i64_kind_v1(int64_t state, int64_t kind, int64_t entry, int64_t input);
extern int64_t rt_pool_state_try_submit_i64_v1(int64_t state, int64_t entry, int64_t input);
extern int64_t rt_pool_task_status_i64_v1(int64_t task);
extern int64_t rt_pool_task_join_i64_v1(int64_t task);
extern int64_t rt_pool_task_release_i64_v1(int64_t task);
extern int64_t rt_pool_state_close_v1(int64_t state);
extern int64_t rt_pool_state_join_idle_v1(int64_t state);
extern int64_t rt_pool_state_outstanding_v1(int64_t state);
extern int64_t rt_pool_state_pending_v1(int64_t state);
extern int64_t rt_pool_state_running_v1(int64_t state);
extern int64_t rt_pool_state_completed_v1(int64_t state);
extern int64_t rt_pool_state_destroy_v1(int64_t state);
extern int64_t rt_pool_submitted_count(void);
extern int64_t rt_pool_completed_count(void);
extern int64_t rt_pool_pending_count(void);
extern int64_t rt_pool_busy_count(void);
extern int64_t rt_pool_blocked_count(void);
#ifdef RT_POOL_CHAR_LANE_A
extern void rt_pool_worker_block_begin(void);
extern void rt_pool_worker_block_end(void);
#endif

#define KIND_ADDRESS 1
#define KIND_VALUE 2
#define DIRECT_MARKER INT64_C(0x5344495245435446)
#define STATE_MAX_CAPACITY 65534

static unsigned g_checks;
static unsigned g_failures;
static const char* g_case = "?";
#define CHECK(x) do { ++g_checks; if (!(x)) { ++g_failures; \
    fprintf(stderr, "FAIL case=%s line=%d: %s\n", g_case, __LINE__, #x); } } while (0)
#define CHECK_EQ(a, b) do { int64_t va_ = (int64_t)(a), vb_ = (int64_t)(b); ++g_checks; \
    if (va_ != vb_) { ++g_failures; fprintf(stderr, "FAIL case=%s line=%d: %s == %s (%lld != %lld)\n", \
    g_case, __LINE__, #a, #b, (long long)va_, (long long)vb_); } } while (0)

/* ---- task entries (scalar ABI: (i64) -> i64) ---------------------------- */

static atomic_int g_gate_open;
static atomic_int g_gate_entered;
static atomic_long g_order_log[4096];
static atomic_int g_order_len;
static atomic_long g_sum;

static int64_t t_plus_one(int64_t x) { return x + 1; }
static int64_t t_square(int64_t x) { return x * x; }
static int64_t t_gate(int64_t x) {
    atomic_fetch_add(&g_gate_entered, 1);
    while (!atomic_load(&g_gate_open)) char_yield();
    return x;
}
static int64_t t_record(int64_t x) {
    int i = atomic_fetch_add(&g_order_len, 1);
    if (i < 4096) atomic_store(&g_order_log[i], (long)x);
    return x;
}
static int64_t t_add_sum(int64_t x) { atomic_fetch_add(&g_sum, (long)x); return x * 2; }

#ifdef RT_POOL_CHAR_LANE_A
static atomic_long g_blocked_seen_inside;
static atomic_long g_blocked_seen_after;
static int64_t t_block_probe(int64_t x) {
    rt_pool_worker_block_begin();
    rt_pool_worker_block_begin(); /* idempotent per worker */
    atomic_store(&g_blocked_seen_inside, (long)rt_pool_blocked_count());
    rt_pool_worker_block_end();
    rt_pool_worker_block_end();
    atomic_store(&g_blocked_seen_after, (long)rt_pool_blocked_count());
    return x;
}
#endif

/* Direct-function records: {entry, marker}, 16-byte aligned data. */
static int64_t rec_plus_one[2] __attribute__((aligned(16)));
static int64_t rec_square[2] __attribute__((aligned(16)));
static int64_t rec_gate[2] __attribute__((aligned(16)));
static int64_t rec_record[2] __attribute__((aligned(16)));
static int64_t rec_add_sum[2] __attribute__((aligned(16)));
static int64_t rec_null[2] __attribute__((aligned(16)));
#ifdef RT_POOL_CHAR_LANE_A
static int64_t rec_block_probe[2] __attribute__((aligned(16)));
#endif
static void init_records(void) {
#define SET_REC(r, f) do { (r)[0] = (int64_t)(intptr_t)(f); (r)[1] = DIRECT_MARKER; } while (0)
    SET_REC(rec_plus_one, t_plus_one);
    SET_REC(rec_square, t_square);
    SET_REC(rec_gate, t_gate);
    SET_REC(rec_record, t_record);
    SET_REC(rec_add_sum, t_add_sum);
#ifdef RT_POOL_CHAR_LANE_A
    SET_REC(rec_block_probe, t_block_probe);
#endif
    rec_null[0] = 0; rec_null[1] = DIRECT_MARKER;
#undef SET_REC
}
#define W(r) ((int64_t)(intptr_t)(r))

static int64_t submit(int64_t state, int64_t* rec, int64_t input) {
    return rt_pool_state_try_submit_i64_kind_v1(state, KIND_ADDRESS, W(rec), input);
}

static int64_t w_completed_count(int64_t u) { (void)u; return rt_pool_completed_count(); }
static int64_t w_busy_count(int64_t u) { (void)u; return rt_pool_busy_count(); }
static int64_t w_pending_count(int64_t u) { (void)u; return rt_pool_pending_count(); }

static int wait_until_eq(int64_t (*fn)(int64_t), int64_t arg, int64_t want) {
    uint64_t deadline = char_now_ms() + 20000;
    while (char_now_ms() < deadline) {
        if (fn(arg) == want) return 1;
        char_sleep_ms(1);
    }
    return 0;
}
static int wait_gate_entered(int want) {
    uint64_t deadline = char_now_ms() + 20000;
    while (char_now_ms() < deadline) {
        if (atomic_load(&g_gate_entered) >= want) return 1;
        char_sleep_ms(1);
    }
    return 0;
}
static void gate_reset(void) { atomic_store(&g_gate_open, 0); atomic_store(&g_gate_entered, 0); }
static void gate_open(void) { atomic_store(&g_gate_open, 1); }

/* Releases every task, closes and destroys the state. */
static void drain_state(int64_t state, int64_t* tasks, int n) {
    CHECK_EQ(rt_pool_state_join_idle_v1(state), 1);
    for (int i = 0; i < n; i++) {
        if (tasks[i] > 0) {
            rt_pool_task_join_i64_v1(tasks[i]);
            CHECK_EQ(rt_pool_task_release_i64_v1(tasks[i]), 1);
        }
    }
    CHECK_EQ(rt_pool_state_close_v1(state), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(state), 1);
}

/* ---- threads ------------------------------------------------------------ */

typedef struct { void (*fn)(void*); void* arg; } char_thunk;
#if defined(_WIN32) || defined(_WIN64)
static DWORD WINAPI char_thread_main(LPVOID p) { char_thunk* t = (char_thunk*)p; t->fn(t->arg); return 0; }
static int char_thread_start(char_thread_t* th, char_thunk* t) {
    *th = CreateThread(NULL, 0, char_thread_main, t, 0, NULL);
    if (*th == NULL) {
        fprintf(stderr, "ERROR case=%s: CreateThread failed (%lu)\n", g_case, (unsigned long)GetLastError());
        exit(2);
    }
    return 1;
}
static void char_thread_join(char_thread_t th) { WaitForSingleObject(th, INFINITE); CloseHandle(th); }
#else
static void* char_thread_main(void* p) { char_thunk* t = (char_thunk*)p; t->fn(t->arg); return NULL; }
static int char_thread_start(char_thread_t* th, char_thunk* t) {
    int rc = pthread_create(th, NULL, char_thread_main, t);
    if (rc != 0) {
        fprintf(stderr, "ERROR case=%s: pthread_create failed (%d)\n", g_case, rc);
        exit(2);
    }
    return 1;
}
static void char_thread_join(char_thread_t th) { pthread_join(th, NULL); }
#endif

/* ---- phase 0: before the pool starts ------------------------------------ */

static void case_clamp_bounds(void) {
    g_case = "clamp_bounds";
    CHECK_EQ(rt_pool_set_parallelism(INT64_MIN), 1);
    CHECK_EQ(rt_pool_get_parallelism(), 1);
    CHECK_EQ(rt_pool_set_parallelism(-5), 1);
    CHECK_EQ(rt_pool_set_parallelism(0), 1);
    CHECK_EQ(rt_pool_set_parallelism(1), 1);
    CHECK_EQ(rt_pool_set_parallelism(2), 2);
    CHECK_EQ(rt_pool_get_parallelism(), 2);
    CHECK_EQ(rt_pool_set_parallelism(63), 63);
    CHECK_EQ(rt_pool_set_parallelism(64), 64);
    CHECK_EQ(rt_pool_get_parallelism(), 64);
    CHECK_EQ(rt_pool_set_parallelism(65), 64);
    CHECK_EQ(rt_pool_set_parallelism(1000), 64);
    CHECK_EQ(rt_pool_set_parallelism(INT64_MAX), 64);
    CHECK_EQ(rt_pool_get_parallelism(), 64);
    /* not started: a smaller request still takes effect */
    CHECK_EQ(rt_pool_set_parallelism(1), 1);
    CHECK_EQ(rt_pool_get_parallelism(), 1);
}

static void case_initial_counters(void) {
    g_case = "initial_counters";
    CHECK_EQ(rt_pool_submitted_count(), 0);
    CHECK_EQ(rt_pool_completed_count(), 0);
    CHECK_EQ(rt_pool_pending_count(), 0);
    CHECK_EQ(rt_pool_busy_count(), 0);
    CHECK_EQ(rt_pool_blocked_count(), 0);
    int64_t fifo = rt_pool_uses_global_fifo_queue();
    int64_t steal = rt_pool_uses_work_stealing();
    CHECK(fifo == 0 || fifo == 1);
    CHECK(steal == 0 || steal == 1);
    CHECK_EQ(rt_pool_uses_global_fifo_queue(), fifo);
    CHECK_EQ(rt_pool_uses_work_stealing(), steal);
    printf("info: uses_global_fifo_queue=%lld uses_work_stealing=%lld\n", (long long)fifo, (long long)steal);
    int64_t sp = rt_pool_safepoint();
    printf("info: safepoint(main, not started)=%lld\n", (long long)sp);
    CHECK_EQ(rt_pool_safepoint(), sp);
#ifdef RT_POOL_CHAR_LANE_A
    /* not a worker: block markers are a no-op */
    rt_pool_worker_block_begin();
    CHECK_EQ(rt_pool_blocked_count(), 0);
    rt_pool_worker_block_end();
    rt_pool_worker_block_end();
    CHECK_EQ(rt_pool_blocked_count(), 0);
#endif
}

static void case_invalid_handles(void) {
    g_case = "invalid_handles";
    const int64_t bad[] = {0, -1, 1, 2, 12345, INT64_MAX, INT64_MIN, (int64_t)0x7fffffffffffLL};
    for (unsigned i = 0; i < sizeof bad / sizeof bad[0]; i++) {
        int64_t h = bad[i];
        CHECK_EQ(rt_pool_task_status_i64_v1(h), -1);
        CHECK_EQ(rt_pool_task_join_i64_v1(h), 0);
        CHECK_EQ(rt_pool_task_release_i64_v1(h), -1);
        CHECK_EQ(rt_pool_state_close_v1(h), 0);
        CHECK_EQ(rt_pool_state_join_idle_v1(h), 0);
        CHECK_EQ(rt_pool_state_outstanding_v1(h), -1);
        CHECK_EQ(rt_pool_state_pending_v1(h), -1);
        CHECK_EQ(rt_pool_state_running_v1(h), -1);
        CHECK_EQ(rt_pool_state_completed_v1(h), -1);
        CHECK_EQ(rt_pool_state_destroy_v1(h), 0);
        CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(h, KIND_ADDRESS, W(rec_plus_one), 1), -3);
        CHECK_EQ(rt_pool_state_try_submit_i64_v1(h, W(rec_plus_one), 1), -3);
    }
    /* legacy handles: NULL is done and joins to 0 */
    CHECK_EQ(rt_pool_is_done(0), 1);
    CHECK_EQ(rt_pool_join(0), 0);
    CHECK_EQ(rt_pool_submit(0, 0), 0);
}

static void case_create_capacity(void) {
    g_case = "create_capacity";
    CHECK_EQ(rt_pool_state_create_v1(0), 0);
    CHECK_EQ(rt_pool_state_create_v1(-1), 0);
    CHECK_EQ(rt_pool_state_create_v1(INT64_MIN), 0);
    CHECK_EQ(rt_pool_state_create_v1(STATE_MAX_CAPACITY + 1), 0);
    CHECK_EQ(rt_pool_state_create_v1(INT64_MAX), 0);
    int64_t caps[] = {1, 2, 64, STATE_MAX_CAPACITY};
    for (unsigned i = 0; i < 4; i++) {
        int64_t s = rt_pool_state_create_v1(caps[i]);
        CHECK(s > 0);
        CHECK_EQ(rt_pool_state_outstanding_v1(s), 0);
        CHECK_EQ(rt_pool_state_pending_v1(s), 0);
        CHECK_EQ(rt_pool_state_running_v1(s), 0);
        CHECK_EQ(rt_pool_state_completed_v1(s), 0);
        /* empty state: join_idle returns at once */
        CHECK_EQ(rt_pool_state_join_idle_v1(s), 1);
        /* destroy requires close */
        CHECK_EQ(rt_pool_state_destroy_v1(s), 0);
        CHECK_EQ(rt_pool_state_close_v1(s), 1);
        CHECK_EQ(rt_pool_state_close_v1(s), 1); /* close is idempotent */
        CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
        /* stale after destroy */
        CHECK_EQ(rt_pool_state_destroy_v1(s), 0);
        CHECK_EQ(rt_pool_state_close_v1(s), 0);
        CHECK_EQ(rt_pool_state_outstanding_v1(s), -1);
        CHECK_EQ(submit(s, rec_plus_one, 1), -3);
    }
}

static void case_bad_function_words(void) {
    g_case = "bad_function_words";
    int64_t s = rt_pool_state_create_v1(8);
    CHECK(s > 0);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, 0, W(rec_plus_one), 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, 3, W(rec_plus_one), 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, -1, W(rec_plus_one), 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_ADDRESS, 0, 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_ADDRESS, 4095, 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_ADDRESS, (int64_t)UINT64_C(0x00ff000000000000), 1), -3);
    /* a record that is neither direct nor a registered closure */
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_ADDRESS, W(rec_null), 1), -3);
    /* VALUE kind: bad tag, nil-ish words */
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_VALUE, W(rec_plus_one) | 2, 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_kind_v1(s, KIND_VALUE, 0, 1), -3);
    CHECK_EQ(rt_pool_state_try_submit_i64_v1(s, W(rec_plus_one) | 2, 1), -3);
    /* rejected submits leave no trace on the state */
    CHECK_EQ(rt_pool_state_outstanding_v1(s), 0);
    CHECK_EQ(rt_pool_state_pending_v1(s), 0);
    CHECK_EQ(rt_pool_submitted_count(), 0);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
}

/* ---- phase 1: exactly one worker --------------------------------------- */

static void case_submit_join_single(void) {
    g_case = "submit_join_single";
    int64_t s = rt_pool_state_create_v1(4);
    int64_t t = submit(s, rec_plus_one, 41);
    CHECK(t > 0);
    CHECK_EQ(rt_pool_task_join_i64_v1(t), 42);
    CHECK_EQ(rt_pool_task_join_i64_v1(t), 42); /* join twice, same answer */
    CHECK_EQ(rt_pool_task_status_i64_v1(t), 2);
    CHECK_EQ(rt_pool_state_completed_v1(s), 1);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), 1);
    CHECK_EQ(rt_pool_state_pending_v1(s), 0);
    CHECK_EQ(rt_pool_state_running_v1(s), 0);
    CHECK_EQ(rt_pool_task_release_i64_v1(t), 1);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), 0);
    /* double release / use after release: handle is gone */
    CHECK_EQ(rt_pool_task_release_i64_v1(t), -1);
    CHECK_EQ(rt_pool_task_status_i64_v1(t), -1);
    CHECK_EQ(rt_pool_task_join_i64_v1(t), 0);
    /* a task handle is not a state handle, and vice versa */
    int64_t t2 = submit(s, rec_square, 9);
    CHECK_EQ(rt_pool_task_join_i64_v1(t2), 81);
    CHECK_EQ(rt_pool_state_outstanding_v1(t2), -1);
    CHECK_EQ(rt_pool_state_close_v1(t2), 0);
    CHECK_EQ(rt_pool_state_destroy_v1(t2), 0);
    CHECK_EQ(rt_pool_task_status_i64_v1(s), -1);
    CHECK_EQ(rt_pool_task_release_i64_v1(s), -1);
    CHECK_EQ(rt_pool_task_join_i64_v1(s), 0);
    CHECK_EQ(rt_pool_task_release_i64_v1(t2), 1);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
    CHECK_EQ(rt_pool_get_parallelism(), 1);
    CHECK_EQ(rt_pool_submitted_count(), 2);
    CHECK(wait_until_eq(w_completed_count, 0, 2));
}

static void case_value_kind_entries(void) {
    g_case = "value_kind_entries";
    int64_t s = rt_pool_state_create_v1(16);
    /* VALUE kind: heap-tagged record (tag 1) and int-tagged record address (<<3) */
    int64_t t1 = rt_pool_state_try_submit_i64_v1(s, W(rec_plus_one) | 1, 10);
    int64_t t2 = rt_pool_state_try_submit_i64_kind_v1(s, KIND_VALUE, W(rec_square) << 3, 7);
    int64_t t3 = rt_pool_state_try_submit_i64_kind_v1(s, KIND_VALUE, W(rec_square) | 1, 5);
    CHECK(t1 > 0); CHECK(t2 > 0); CHECK(t3 > 0);
    CHECK_EQ(rt_pool_task_join_i64_v1(t1), 11);
    CHECK_EQ(rt_pool_task_join_i64_v1(t2), 49);
    CHECK_EQ(rt_pool_task_join_i64_v1(t3), 25);
    int64_t ts[3] = {t1, t2, t3};
    drain_state(s, ts, 3);
}

static void case_legacy_submit(void) {
    g_case = "legacy_submit";
    /* legacy raw record: first word is entry(record) */
    static int64_t raw[2] __attribute__((aligned(16)));
    raw[0] = (int64_t)(intptr_t)t_plus_one;
    raw[1] = 0;
    int64_t h = rt_pool_submit(W(raw), 0);
    CHECK(h != 0);
    if (h == 0) exit(1);
    CHECK_EQ(rt_pool_join(h), W(raw) + 1);
    int64_t h2 = rt_pool_submit(0, W(raw)); /* arg1 wins when non-zero */
    CHECK(h2 != 0);
    if (h2 == 0) exit(1);
    uint64_t deadline = char_now_ms() + 10000;
    while (!rt_pool_is_done(h2)) {
        if (char_now_ms() >= deadline) {
            fprintf(stderr, "FAIL case=%s: legacy task did not complete within 10 seconds\n", g_case);
            exit(1);
        }
        char_yield();
    }
    CHECK_EQ(rt_pool_is_done(h2), 1);
    CHECK_EQ(rt_pool_join(h2), W(raw) + 1);
    /* misaligned raw record is refused */
    CHECK_EQ(rt_pool_submit(W(raw) + 4, 0), 0);
}

static void case_fifo_order(int n) {
    g_case = "fifo_order";
    gate_reset();
    atomic_store(&g_order_len, 0);
    int64_t s = rt_pool_state_create_v1(n + 1);
    int64_t* ts = (int64_t*)calloc((size_t)n + 1, sizeof(int64_t));
    ts[0] = submit(s, rec_gate, -1);
    CHECK(ts[0] > 0);
    CHECK(wait_gate_entered(1));
    for (int i = 1; i <= n; i++) {
        ts[i] = submit(s, rec_record, i);
        CHECK(ts[i] > 0);
    }
    CHECK_EQ(rt_pool_state_pending_v1(s), n);
    CHECK_EQ(rt_pool_state_running_v1(s), 1);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), n + 1);
    CHECK_EQ(rt_pool_state_completed_v1(s), 0);
    CHECK_EQ(rt_pool_pending_count(), n);
    CHECK_EQ(rt_pool_busy_count(), 1);
    /* capacity is full: one more is refused with -1 and leaves no trace */
    CHECK_EQ(submit(s, rec_record, 999), -1);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), n + 1);
    CHECK_EQ(rt_pool_state_pending_v1(s), n);
    /* not done yet: release is refused (-3) and status is 0 */
    if (n > 0) {
        CHECK_EQ(rt_pool_task_status_i64_v1(ts[n]), 0);
        CHECK_EQ(rt_pool_task_release_i64_v1(ts[n]), -3);
    }
    gate_open();
    CHECK_EQ(rt_pool_state_join_idle_v1(s), 1);
    CHECK_EQ(rt_pool_state_pending_v1(s), 0);
    CHECK_EQ(rt_pool_state_running_v1(s), 0);
    CHECK_EQ(rt_pool_state_completed_v1(s), n + 1);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), n + 1);
    CHECK_EQ(atomic_load(&g_order_len), n);
    int in_order = 1;
    for (int i = 0; i < n; i++) if (atomic_load(&g_order_log[i]) != i + 1) in_order = 0;
    CHECK(in_order);
    if (n > 0) CHECK_EQ(rt_pool_task_status_i64_v1(ts[n]), 1); /* done, not joined */
    for (int i = 0; i <= n; i++) {
        CHECK_EQ(rt_pool_task_join_i64_v1(ts[i]), i == 0 ? -1 : i);
        CHECK_EQ(rt_pool_task_release_i64_v1(ts[i]), 1);
        CHECK_EQ(rt_pool_state_outstanding_v1(s), n - i);
    }
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
    CHECK(wait_until_eq(w_busy_count, 0, 0));
    CHECK_EQ(rt_pool_pending_count(), 0);
    free(ts);
}

static void case_shutdown_with_pending(void) {
    g_case = "shutdown_with_pending";
    gate_reset();
    int64_t s = rt_pool_state_create_v1(32);
    int64_t ts[17];
    ts[0] = submit(s, rec_gate, 100);
    CHECK(wait_gate_entered(1));
    for (int i = 1; i < 17; i++) ts[i] = submit(s, rec_plus_one, i);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    /* closed: new work refused, queued work still runs */
    CHECK_EQ(submit(s, rec_plus_one, 1), -2);
    CHECK_EQ(rt_pool_state_try_submit_i64_v1(s, W(rec_plus_one) | 1, 1), -2);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 0); /* pending/running */
    CHECK_EQ(rt_pool_state_pending_v1(s), 16);
    gate_open();
    CHECK_EQ(rt_pool_state_join_idle_v1(s), 1);
    CHECK_EQ(rt_pool_state_completed_v1(s), 17);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 0); /* still outstanding */
    for (int i = 0; i < 17; i++) {
        CHECK_EQ(rt_pool_task_join_i64_v1(ts[i]), i == 0 ? 100 : i + 1);
        CHECK_EQ(rt_pool_task_release_i64_v1(ts[i]), 1);
        if (i < 16) CHECK_EQ(rt_pool_state_destroy_v1(s), 0);
    }
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 0);
}

static void case_release_unjoined(void) {
    g_case = "release_unjoined";
    int64_t s = rt_pool_state_create_v1(2);
    int64_t t = submit(s, rec_plus_one, 1);
    CHECK(wait_until_eq(rt_pool_task_status_i64_v1, t, 1));
    CHECK_EQ(rt_pool_task_release_i64_v1(t), 1); /* done but never joined */
    CHECK_EQ(rt_pool_state_outstanding_v1(s), 0);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
}

static void case_handle_reuse(void) {
    g_case = "handle_reuse";
    /* more create/destroy cycles than the state slot table has slots: every
     * new handle differs from the stale one it may reuse a slot of */
    int64_t prev = 0;
    int stale_ok = 1, distinct_ok = 1;
    for (int i = 0; i < 3000; i++) {
        int64_t s = rt_pool_state_create_v1(1);
        if (s <= 0) { CHECK(s > 0); break; }
        if (s == prev) distinct_ok = 0;
        rt_pool_state_close_v1(s);
        if (rt_pool_state_destroy_v1(s) != 1) stale_ok = 0;
        if (rt_pool_state_outstanding_v1(s) != -1) stale_ok = 0;
        if (prev && rt_pool_state_close_v1(prev) != 0) stale_ok = 0;
        prev = s;
    }
    CHECK(distinct_ok);
    CHECK(stale_ok);
    /* task handles likewise */
    int64_t st = rt_pool_state_create_v1(1);
    int64_t prevt = 0;
    int t_ok = 1;
    for (int i = 0; i < 2000; i++) {
        int64_t t = submit(st, rec_plus_one, i);
        if (t <= 0 || t == prevt) { t_ok = 0; break; }
        if (rt_pool_task_join_i64_v1(t) != i + 1) t_ok = 0;
        if (rt_pool_task_release_i64_v1(t) != 1) t_ok = 0;
        if (prevt && rt_pool_task_status_i64_v1(prevt) != -1) t_ok = 0;
        prevt = t;
    }
    CHECK(t_ok);
    CHECK_EQ(rt_pool_state_close_v1(st), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(st), 1);
}

static void case_many_states(void) {
    g_case = "many_states";
    enum { NS = 200 };
    int64_t ss[NS];
    int ok = 1;
    for (int i = 0; i < NS; i++) { ss[i] = rt_pool_state_create_v1(2); if (ss[i] <= 0) ok = 0; }
    for (int i = 0; i < NS && ok; i++) for (int j = i + 1; j < NS; j++) if (ss[i] == ss[j]) ok = 0;
    CHECK(ok);
    int64_t ts[NS];
    for (int i = 0; i < NS; i++) ts[i] = submit(ss[i], rec_square, i);
    for (int i = 0; i < NS; i++) {
        CHECK_EQ(rt_pool_task_join_i64_v1(ts[i]), (int64_t)i * i);
        CHECK_EQ(rt_pool_state_outstanding_v1(ss[i]), 1);
        CHECK_EQ(rt_pool_task_release_i64_v1(ts[i]), 1);
        CHECK_EQ(rt_pool_state_close_v1(ss[i]), 1);
        CHECK_EQ(rt_pool_state_destroy_v1(ss[i]), 1);
    }
}

#ifdef RT_POOL_CHAR_LANE_A
static void case_worker_block_markers(void) {
    g_case = "worker_block_markers";
    int64_t s = rt_pool_state_create_v1(2);
    int64_t t = submit(s, rec_block_probe, 5);
    CHECK_EQ(rt_pool_task_join_i64_v1(t), 5);
    CHECK_EQ(atomic_load(&g_blocked_seen_inside), 1);
    CHECK_EQ(atomic_load(&g_blocked_seen_after), 0);
    CHECK_EQ(rt_pool_blocked_count(), 0);
    CHECK_EQ(rt_pool_task_release_i64_v1(t), 1);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
}
#endif

/* ---- phase 2: many workers --------------------------------------------- */

static void case_grow_parallelism(void) {
    g_case = "grow_parallelism";
    CHECK_EQ(rt_pool_get_parallelism(), 1);
    CHECK_EQ(rt_pool_set_parallelism(0), 1);  /* started: shrink refused */
    CHECK_EQ(rt_pool_set_parallelism(8), 8);
    CHECK_EQ(rt_pool_get_parallelism(), 8);
    CHECK_EQ(rt_pool_set_parallelism(4), 8);
    CHECK_EQ(rt_pool_set_parallelism(-1), 8);
    CHECK_EQ(rt_pool_get_parallelism(), 8);
}

static void case_parallel_gate(void) {
    g_case = "parallel_gate";
    gate_reset();
    int64_t s = rt_pool_state_create_v1(64);
    int64_t ts[8];
    for (int i = 0; i < 8; i++) ts[i] = submit(s, rec_gate, i);
    CHECK(wait_gate_entered(8)); /* all 8 workers run concurrently */
    CHECK_EQ(rt_pool_state_running_v1(s), 8);
    CHECK_EQ(rt_pool_state_pending_v1(s), 0);
    CHECK_EQ(rt_pool_busy_count(), 8);
    gate_open();
    drain_state(s, ts, 8);
}

typedef struct { int64_t task; atomic_int* go; int64_t result; int64_t rc; } join_arg;
static void th_join(void* p) {
    join_arg* a = (join_arg*)p;
    while (!atomic_load(a->go)) char_yield();
    a->result = rt_pool_task_join_i64_v1(a->task);
}
static void th_release_loop(void* p) {
    join_arg* a = (join_arg*)p;
    while (!atomic_load(a->go)) char_yield();
    int64_t rc;
    while ((rc = rt_pool_task_release_i64_v1(a->task)) == -3) char_yield();
    a->rc = rc;
}

static void case_concurrent_joiners(void) {
    g_case = "concurrent_joiners";
    for (int round = 0; round < 20; round++) {
        gate_reset();
        int64_t s = rt_pool_state_create_v1(4);
        int64_t t = submit(s, rec_gate, 77 + round);
        atomic_int go = 0;
        enum { NJ = 8 };
        join_arg args[NJ];
        char_thunk thunks[NJ];
        char_thread_t ths[NJ];
        for (int i = 0; i < NJ; i++) {
            args[i] = (join_arg){t, &go, -999, 0};
            thunks[i] = (char_thunk){th_join, &args[i]};
            char_thread_start(&ths[i], &thunks[i]);
        }
        atomic_store(&go, 1);
        CHECK(wait_gate_entered(1));
        gate_open();
        for (int i = 0; i < NJ; i++) char_thread_join(ths[i]);
        int all = 1;
        for (int i = 0; i < NJ; i++) if (args[i].result != 77 + round) all = 0;
        CHECK(all);
        CHECK_EQ(rt_pool_task_release_i64_v1(t), 1);
        CHECK_EQ(rt_pool_state_close_v1(s), 1);
        CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
    }
}

static void case_join_release_race(void) {
    g_case = "join_release_race";
    int ok = 1;
    for (int round = 0; round < 200; round++) {
        int64_t s = rt_pool_state_create_v1(2);
        int64_t t = submit(s, rec_plus_one, round);
        atomic_int go = 0;
        join_arg ja = {t, &go, -999, 0}, ra = {t, &go, 0, 0};
        char_thunk jt = {th_join, &ja}, rt_ = {th_release_loop, &ra};
        char_thread_t a, b;
        char_thread_start(&a, &jt);
        char_thread_start(&b, &rt_);
        atomic_store(&go, 1);
        char_thread_join(a);
        char_thread_join(b);
        /* the joiner sees the result, or 0 once the handle is gone */
        if (!(ja.result == round + 1 || ja.result == 0)) ok = 0;
        if (ra.rc != 1) ok = 0;
        if (rt_pool_task_status_i64_v1(t) != -1) ok = 0;
        if (rt_pool_state_outstanding_v1(s) != 0) ok = 0;
        rt_pool_state_close_v1(s);
        if (rt_pool_state_destroy_v1(s) != 1) ok = 0;
    }
    CHECK(ok);
}

typedef struct { int64_t state; atomic_int* stop; int bad; } reader_arg;
static void th_reader(void* p) {
    reader_arg* a = (reader_arg*)p;
    while (!atomic_load(a->stop)) {
        int64_t o = rt_pool_state_outstanding_v1(a->state);
        int64_t pe = rt_pool_state_pending_v1(a->state);
        int64_t ru = rt_pool_state_running_v1(a->state);
        int64_t co = rt_pool_state_completed_v1(a->state);
        if (o < -1 || pe < -1 || ru < -1 || co < -1) a->bad++;
        if (o > 64 || pe > 64 || ru > 8 || co > 64) a->bad++;
    }
}

static void case_readers_during_destroy(void) {
    g_case = "readers_during_destroy";
    for (int round = 0; round < 30; round++) {
        int64_t s = rt_pool_state_create_v1(64);
        atomic_int stop = 0;
        enum { NR = 8 };
        reader_arg ra[NR];
        char_thunk th[NR];
        char_thread_t ts[NR];
        for (int i = 0; i < NR; i++) {
            ra[i] = (reader_arg){s, &stop, 0};
            th[i] = (char_thunk){th_reader, &ra[i]};
            char_thread_start(&ts[i], &th[i]);
        }
        int64_t tasks[64];
        for (int i = 0; i < 64; i++) tasks[i] = submit(s, rec_square, i);
        for (int i = 0; i < 64; i++) {
            rt_pool_task_join_i64_v1(tasks[i]);
            rt_pool_task_release_i64_v1(tasks[i]);
        }
        rt_pool_state_close_v1(s);
        CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
        char_sleep_ms(1);
        atomic_store(&stop, 1);
        int bad = 0;
        for (int i = 0; i < NR; i++) { char_thread_join(ts[i]); bad += ra[i].bad; }
        CHECK_EQ(bad, 0);
        CHECK_EQ(rt_pool_state_outstanding_v1(s), -1);
    }
}

typedef struct { int64_t state; int tasks; int64_t local_sum; int fails; } stress_arg;
static void th_stress(void* p) {
    stress_arg* a = (stress_arg*)p;
    int64_t window[32];
    int wn = 0;
    for (int i = 1; i <= a->tasks; i++) {
        int64_t t;
        while ((t = submit(a->state, rec_add_sum, i)) == -1) {
            /* capacity: drain our own window first */
            for (int k = 0; k < wn; k++) {
                if (rt_pool_task_join_i64_v1(window[k]) <= 0) a->fails++;
                if (rt_pool_task_release_i64_v1(window[k]) != 1) a->fails++;
            }
            wn = 0;
            char_yield();
        }
        if (t <= 0) { a->fails++; continue; }
        a->local_sum += i;
        window[wn++] = t;
        if (wn == 32) {
            for (int k = 0; k < wn; k++) {
                if (rt_pool_task_join_i64_v1(window[k]) <= 0) a->fails++;
                if (rt_pool_task_release_i64_v1(window[k]) != 1) a->fails++;
            }
            wn = 0;
        }
    }
    for (int k = 0; k < wn; k++) {
        if (rt_pool_task_join_i64_v1(window[k]) <= 0) a->fails++;
        if (rt_pool_task_release_i64_v1(window[k]) != 1) a->fails++;
    }
}

static void case_stress(int nthreads, int ntasks, int64_t capacity) {
    g_case = "stress";
    atomic_store(&g_sum, 0);
    int64_t before_sub = rt_pool_submitted_count();
    int64_t s = rt_pool_state_create_v1(capacity);
    CHECK(s > 0);
    stress_arg* args = (stress_arg*)calloc((size_t)nthreads, sizeof(stress_arg));
    char_thunk* th = (char_thunk*)calloc((size_t)nthreads, sizeof(char_thunk));
    char_thread_t* ts = (char_thread_t*)calloc((size_t)nthreads, sizeof(char_thread_t));
    if (!args || !th || !ts) {
        fprintf(stderr, "ERROR case=%s: thread argument allocation failed\n", g_case);
        exit(2);
    }
    for (int i = 0; i < nthreads; i++) {
        args[i] = (stress_arg){s, ntasks, 0, 0};
        th[i] = (char_thunk){th_stress, &args[i]};
        CHECK(char_thread_start(&ts[i], &th[i]));
    }
    int64_t want = 0;
    int fails = 0;
    for (int i = 0; i < nthreads; i++) { char_thread_join(ts[i]); want += args[i].local_sum; fails += args[i].fails; }
    CHECK_EQ(fails, 0);
    CHECK_EQ(atomic_load(&g_sum), want);
    CHECK_EQ(want, (int64_t)nthreads * ntasks * (ntasks + 1) / 2);
    CHECK_EQ(rt_pool_state_outstanding_v1(s), 0);
    CHECK_EQ(rt_pool_state_pending_v1(s), 0);
    CHECK_EQ(rt_pool_state_running_v1(s), 0);
    CHECK_EQ(rt_pool_state_completed_v1(s), (int64_t)nthreads * ntasks);
    CHECK_EQ(rt_pool_submitted_count() - before_sub, (int64_t)nthreads * ntasks);
    CHECK_EQ(rt_pool_state_close_v1(s), 1);
    CHECK_EQ(rt_pool_state_destroy_v1(s), 1);
    CHECK(wait_until_eq(w_pending_count, 0, 0));
    CHECK(wait_until_eq(w_busy_count, 0, 0));
    free(args); free(th); free(ts);
}

static void case_global_balance(void) {
    g_case = "global_balance";
    CHECK(wait_until_eq(w_busy_count, 0, 0));
    CHECK_EQ(rt_pool_submitted_count(), rt_pool_completed_count());
    CHECK_EQ(rt_pool_pending_count(), 0);
    CHECK_EQ(rt_pool_blocked_count(), 0);
}

int main(int argc, char** argv) {
    int quick = argc > 1 && argv[1][0] == 'q'; /* sanitizer runs use smaller stress */
    init_records();
    case_clamp_bounds();
    case_initial_counters();
    case_invalid_handles();
    case_create_capacity();
    case_bad_function_words();
    /* the first accepted submit starts the pool with one worker */
    case_submit_join_single();
    case_value_kind_entries();
    case_legacy_submit();
    case_fifo_order(0);
    case_fifo_order(1);
    case_fifo_order(2);
    case_fifo_order(100);
    case_fifo_order(1000);
    case_shutdown_with_pending();
    case_release_unjoined();
    case_handle_reuse();
    case_many_states();
#ifdef RT_POOL_CHAR_LANE_A
    case_worker_block_markers();
#endif
    case_grow_parallelism();
    case_parallel_gate();
    case_concurrent_joiners();
    case_join_release_race();
    case_readers_during_destroy();
    int m = quick ? 200 : 2000;
    case_stress(1, m, 64);
    case_stress(4, m, 64);
    case_stress(16, m, 256);
    case_stress(64, quick ? 50 : 500, 1024);
    case_stress(8, m, 8); /* capacity pressure: -1 retries */
    case_global_balance();
    printf("%s: %u checks, %u failures\n", g_failures ? "FAIL" : "PASS", g_checks, g_failures);
    return g_failures ? 1 : 0;
}
