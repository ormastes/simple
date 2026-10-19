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
#ifdef _WIN32
#include <windows.h>
#define SLEEP_MS(ms) Sleep(ms)
#else
#include <unistd.h>
#define SLEEP_MS(ms) usleep((ms) * 1000)
#endif

extern int64_t rt_thread_spawn_isolated(int64_t closure, int64_t data);
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

    /* thread.spl shape: (closure, nil). nil must not be taken as the closure. */
    int64_t h1 = rt_thread_spawn_isolated((int64_t)(intptr_t)record, NIL);
    assert(h1 != 0);
    assert(rt_thread_join(h1) == 42);
    assert(g_seen_env == (int64_t)(intptr_t)record);
    assert(g_seen_data == NIL);
    assert(rt_thread_is_done(h1) == 1);
    /* Join keeps the handle: a repeat join is nil, not a stale slot. */
    assert(rt_thread_join(h1) == NIL);

    /* A second spawn must not reuse h1's slot while h1 is unfreed. */
    int64_t h2 = rt_thread_spawn_isolated((int64_t)(intptr_t)direct, 7 << 3);
    assert(h2 != 0 && h2 != h1);
    rt_thread_free(h1);
    assert(rt_thread_join(h2) == (7 << 3) + 8);
    rt_thread_free(h2);

    /* Legacy (0, closure) argument order is still accepted. */
    int64_t h3 = rt_thread_spawn_isolated(0, (int64_t)(intptr_t)record);
    assert(h3 != 0);
    assert(rt_thread_join(h3) == 42);
    assert(g_seen_data == NIL);
    rt_thread_free(h3);

    /* free without join detaches; let the worker finish first. */
    int64_t h4 = rt_thread_spawn_isolated((int64_t)(intptr_t)direct, 0);
    assert(h4 != 0);
    while (rt_thread_is_done(h4) == 0) SLEEP_MS(1);
    assert(rt_thread_id(h4) != 0);
    rt_thread_free(h4);

    puts("rt_thread_owner_contract_selfcheck: ok");
    return 0;
}
