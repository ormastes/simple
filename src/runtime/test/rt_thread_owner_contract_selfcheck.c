/* The C rt_thread_* handle family must be a twin of the Rust owner
 * (src/compiler_rust/runtime/src/executor.rs), because --runtime-owner picks
 * one of them per link: spawn(closure, data) runs closure(data), join waits
 * once and keeps the handle until free, a repeat join returns nil.
 * Link against runtime_thread.c's object plus its runtime dependencies
 * (the core-C composition objects). */
#ifdef NDEBUG
#error "This contract requires enabled assertions"
#endif
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include "../runtime_value.h"
#ifdef _WIN32
#include <windows.h>
#define SLEEP_MS(ms) Sleep(ms)
#else
#include <unistd.h>
#define SLEEP_MS(ms) usleep((ms) * 1000)
#endif

extern int64_t rt_thread_spawn_isolated(int64_t closure, int64_t data);
extern int64_t rt_thread_spawn_isolated_kind(int64_t kind, int64_t closure, int64_t data);
extern int64_t rt_thread_spawn_isolated_with_args_kind(int64_t kind, int64_t closure, int64_t data1, int64_t data2);

/* runtime_thread.c RT_WORKER_CLOSURE_*: the spawner states the word kind. */
#define KIND_ADDRESS 1
#define KIND_VALUE 2
extern int64_t rt_thread_join(int64_t handle);
extern int64_t rt_thread_is_done(int64_t handle);
extern int64_t rt_thread_id(int64_t handle);
extern void rt_thread_free(int64_t handle);

#define NIL ((int64_t)3)
#define DIRECT_MARKER 0x5344495245435446LL

static int64_t g_seen_env = 0;
static int64_t g_seen_data = 0;

/* Closure record: [0] = entry(env, data), [1] = any non-direct word. */
static int64_t record_entry(int64_t env, int64_t data) {
    g_seen_env = env;
    g_seen_data = data;
    return 42;
}

static volatile int64_t g_slow_finished = 0;

/* Direct-function worker that outlives the handle freed before it ends. */
static int64_t slow_entry(int64_t data) {
    SLEEP_MS(50);
    g_slow_finished = data;
    return data;
}

/* Two-argument direct worker (record [0] = entry, [1] = DIRECT_MARKER). */
static int64_t direct2_entry(int64_t a, int64_t b) {
    return a + b;
}

/* Direct-function record: [0] = entry(data), [1] = DIRECT_MARKER. */
static int64_t direct_entry(int64_t data) {
    return data + 8;
}

int main(void) {
    static int64_t record[2];
    static int64_t direct[2];
    record[0] = (int64_t)(intptr_t)&record_entry;
    record[1] = 0;
    direct[0] = (int64_t)(intptr_t)&direct_entry;
    direct[1] = DIRECT_MARKER;
    static int64_t direct2[2];
    direct2[0] = (int64_t)(intptr_t)&direct2_entry;
    direct2[1] = DIRECT_MARKER;

    /* A real address of this process is never the int-tagged (addr << 3)
     * word, including above 2^47 on aarch64 PIE and with a top-byte tag. */
    assert(!rt_native_word_exceeds_user_va((uint64_t)(uintptr_t)record));
#if defined(__aarch64__)
    assert(!rt_native_word_exceeds_user_va((UINT64_C(0x5a) << 56) | (uint64_t)(uintptr_t)record));
    assert(rt_native_word_exceeds_user_va(UINT64_C(0x0000aaaaaaab0000) << 3));
#endif

    /* thread.spl shape: (closure, nil), the closure a heap-tagged value. nil
     * must not be taken as the closure. */
    int64_t h1 = rt_thread_spawn_isolated((int64_t)(intptr_t)record | 1, NIL);
    assert(h1 != 0);
    assert(rt_thread_join(h1) == 42);
    assert(g_seen_env == (int64_t)(intptr_t)record);
    assert(g_seen_data == NIL);
    assert(rt_thread_is_done(h1) == 1);
    /* Join keeps the handle: a repeat join is nil, not a stale slot. */
    assert(rt_thread_join(h1) == NIL);

    /* A second spawn must not reuse h1's slot while h1 is unfreed. */
    int64_t h2 = rt_thread_spawn_isolated_kind(KIND_ADDRESS, (int64_t)(intptr_t)direct, 7 << 3);
    assert(h2 != 0 && h2 != h1);
    rt_thread_free(h1);
    assert(rt_thread_join(h2) == (7 << 3) + 8);
    rt_thread_free(h2);

    /* Legacy (0, closure) argument order is still accepted. */
    int64_t h3 = rt_thread_spawn_isolated(0, (int64_t)(intptr_t)record | 1);
    assert(h3 != 0);
    assert(rt_thread_join(h3) == 42);
    assert(g_seen_data == NIL);
    rt_thread_free(h3);

    /* free without join detaches; let the worker finish first. */
    int64_t h4 = rt_thread_spawn_isolated_kind(KIND_ADDRESS, (int64_t)(intptr_t)direct, 0);
    assert(h4 != 0);
    while (rt_thread_is_done(h4) == 0) SLEEP_MS(1);
    assert(rt_thread_id(h4) != 0);
    rt_thread_free(h4);

    /* free before the worker finishes (thread.spl free(): "thread continues
     * running, result is discarded"): the worker owns the thread data until
     * it exits, so its result/done writes must not hit freed memory. */
    static int64_t slow[2];
    slow[0] = (int64_t)(intptr_t)&slow_entry;
    slow[1] = DIRECT_MARKER;
    int64_t h5 = rt_thread_spawn_isolated_kind(KIND_ADDRESS, (int64_t)(intptr_t)slow, 9 << 3);
    assert(h5 != 0);
    rt_thread_free(h5);
    assert(rt_thread_join(h5) == 0);
    for (int i = 0; i < 2000 && g_slow_finished == 0; i++) SLEEP_MS(1);
    assert(g_slow_finished == (9 << 3));
    SLEEP_MS(20);

    /* Explicit worker-closure kind (isolated_thread_raw_worker_argument_
     * heuristic_flake_2026-08-12): the spawner's kind decides, never the
     * word's value. VALUE + TAG_INT (addr << 3) is a raw native record with
     * raw i64 args, at ANY address -- no VA cutoff. */
    int64_t h6 = rt_thread_spawn_isolated_kind(KIND_VALUE, (int64_t)(intptr_t)record << 3, 5 << 3);
    assert(h6 != 0);
    assert(rt_thread_join(h6) == 42);
    assert(g_seen_env == (int64_t)(intptr_t)record);
    assert(g_seen_data == 5);
    rt_thread_free(h6);
    /* The same record under ADDRESS keeps RuntimeValue args. */
    int64_t h7 = rt_thread_spawn_isolated_kind(KIND_ADDRESS, (int64_t)(intptr_t)record, 5 << 3);
    assert(h7 != 0);
    assert(rt_thread_join(h7) == 42);
    assert(g_seen_data == (5 << 3));
    rt_thread_free(h7);
    /* Two-argument workers: raw args decoded under VALUE + TAG_INT. */
    int64_t h8 = rt_thread_spawn_isolated_with_args_kind(KIND_VALUE, (int64_t)(intptr_t)direct2 << 3, 10 << 3, 32 << 3);
    assert(h8 != 0);
    assert(rt_thread_join(h8) == 42);
    rt_thread_free(h8);
    int64_t h9 = rt_thread_spawn_isolated_with_args_kind(KIND_ADDRESS, (int64_t)(intptr_t)direct2, 10, 32);
    assert(h9 != 0);
    assert(rt_thread_join(h9) == 42);
    rt_thread_free(h9);
    /* Rejections: unknown kinds, non-callable value tags, null-page payloads,
     * and "addresses" above the user-VA ceiling. */
    assert(rt_thread_spawn_isolated_kind(0, (int64_t)(intptr_t)record, NIL) == 0);
    assert(rt_thread_spawn_isolated_kind(3, (int64_t)(intptr_t)record, NIL) == 0);
    assert(rt_thread_spawn_isolated_kind(KIND_VALUE, NIL, NIL) == 0);
    assert(rt_thread_spawn_isolated_kind(KIND_VALUE, (int64_t)(intptr_t)record | 2, NIL) == 0);
    assert(rt_thread_spawn_isolated_kind(KIND_VALUE, 4095 << 3, NIL) == 0);
    assert(rt_thread_spawn_isolated_kind(KIND_ADDRESS, (int64_t)(UINT64_C(0x00ff000000000000)), NIL) == 0);
    assert(rt_thread_spawn_isolated_with_args_kind(7, (int64_t)(intptr_t)direct2, 1, 2) == 0);

    puts("rt_thread_owner_contract_selfcheck: ok");
    return 0;
}
