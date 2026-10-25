/* Self-check for the object-graph refcount (BSM P4): rt_rc_share/retain/
 * release/count and rt_heap_graph_bytes in runtime_native.c.
 *
 * Build + run:
 *   clang -std=gnu11 -O1 -o /tmp/rtrc src/runtime/test/rt_rc_selfcheck.c \
 *      src/runtime/runtime_native.c -lm -lpthread && /tmp/rtrc
 * Perf/RSS lane: `rtrc leak <n>` / `rtrc release <n>` builds <n> rounds of a
 * 100k-object graph and either leaks it or rc-releases it.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "../runtime.h"

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_heap_registry_count(void);
extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value);

static int failures = 0;

static void check(int cond, const char* what) {
    printf("  %s %s\n", cond ? "ok  " : "FAIL", what);
    if (!cond) failures++;
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

static int64_t arr(void) { return (int64_t)(uintptr_t)rt_array_new(0); }
static void push(int64_t a, int64_t v) { rt_array_push((SplArray*)(uintptr_t)a, v); }

static void set_cycle_check(int on) {
#if defined(_WIN32)
    _putenv(on ? "SIMPLE_RC_CYCLE_CHECK=1" : "SIMPLE_RC_CYCLE_CHECK=");
#else
    if (on) setenv("SIMPLE_RC_CYCLE_CHECK", "1", 1); else unsetenv("SIMPLE_RC_CYCLE_CHECK");
#endif
}

/* One array root holding n distinct strings: n + 1 registered objects. */
static int64_t build_graph(int n) {
    int64_t root = arr();
    char buf[32];
    for (int i = 0; i < n; i++) {
        snprintf(buf, sizeof(buf), "rc-node-%08d", i);
        push(root, mkstr(buf));
    }
    return root;
}

static int perf_lane(const char* mode, int rounds) {
    int release = strcmp(mode, "release") == 0;
    clock_t start = clock();
    for (int r = 0; r < rounds; r++) {
        int64_t g = build_graph(100000);
        if (release && (!rt_rc_share(g) || !rt_rc_release(g))) return 1;
    }
    double secs = (double)(clock() - start) / CLOCKS_PER_SEC;
    printf("rc perf lane mode=%s rounds=%d objects/round=100001 cpu=%.3fs registry=%lld\n",
           mode, rounds, secs, (long long)rt_heap_registry_count());
    return 0;
}

int main(int argc, char** argv) {
    if (argc == 3) return perf_lane(argv[1], atoi(argv[2]));

    printf("(a) share/retain/release lifecycle\n");
    int64_t child = arr();                 /* rc-root child */
    push(child, mkstr("child-text"));
    check(rt_rc_share(child) == 1 && rt_rc_count(child) == 1, "child shared rc=1");
    int64_t root = arr();
    push(root, mkstr("owned-text"));
    push(root, child);
    check(rt_rc_retain(child) == 1 && rt_rc_count(child) == 2, "root's edge retains child rc=2");
    check(rt_rc_share(root) == 1 && rt_rc_count(root) == 1, "share -> 1");
    check(rt_rc_share(root) == 1 && rt_rc_count(root) == 1, "share idempotent on rc root");
    check(rt_rc_retain(root) == 1 && rt_rc_count(root) == 2, "retain -> 2");
    check(rt_rc_release(root) == 1 && rt_rc_count(root) == 1, "release -> 1");
    int64_t before = rt_heap_registry_count();
    check(rt_rc_release(root) == 1, "release -> 0");
    check(rt_heap_registry_count() == before - 2, "root + owned string left the registry");
    check(rt_rc_count(root) == -1, "freed root is no longer an rc root");
    check(rt_rc_count(child) == 1, "rc-root child only decremented");
    before = rt_heap_registry_count();
    check(rt_rc_release(child) == 1 && rt_heap_registry_count() == before - 2,
          "child release frees child + its string");

    printf("(b) release on non-rc\n");
    int64_t plain = arr();
    push(plain, mkstr("plain-text"));
    before = rt_heap_registry_count();
    check(rt_rc_release(plain) == 0 && rt_rc_retain(plain) == 0, "release/retain refuse non-rc");
    check(rt_rc_release(rt_value_int(7)) == 0 && rt_rc_count(rt_value_int(7)) == -1,
          "immediate int is not an rc root");
    check(rt_heap_registry_count() == before, "nothing freed");

    printf("(c) graph bytes\n");
    int64_t g = arr();                     /* cap 4 */
    push(g, mkstr("abcd"));
    push(g, mkstr("efghij"));
    int64_t g_rc = arr();
    push(g_rc, mkstr("never-counted"));
    rt_rc_share(g_rc);
    push(g, g_rc);
    /* RtCoreArray 32 + 4 slots * 8 = 64; RtCoreString 16 + 4 = 20; 16 + 6 = 22;
     * rc-root child contributes 0. */
    check(rt_heap_graph_bytes(g) == 64 + 20 + 22, "graph bytes = 106 (hand-computed)");
    check(rt_heap_graph_bytes(rt_value_int(1)) == -1, "invalid root -> -1");

    printf("(d) share inside an active transient scope\n");
    check(rt_transient_array_scope_begin() == 1, "scope begin");
    int64_t scoped = arr();
    int64_t scoped_text = mkstr("scoped-text-value");
    push(scoped, scoped_text);
    int64_t scoped_leak = arr();           /* not shared: scope end frees it */
    (void)scoped_leak;
    check(rt_rc_share(scoped) == 1, "share in scope");
    before = rt_heap_registry_count();
    check(rt_transient_array_scope_end() == 1, "scope end");
    check(rt_heap_registry_count() == before - 1, "scope end freed only the unshared array");
    check(rt_string_len(scoped_text) == 17, "shared graph's string survives scope end");
    before = rt_heap_registry_count();
    check(rt_rc_release(scoped) == 1 && rt_heap_registry_count() == before - 2,
          "release frees moved graph");

    printf("(e) SIMPLE_RC_CYCLE_CHECK\n");
    int64_t d = rt_dict_new(0);
    rt_dict_set(d, mkstr("self-key"), d);
    set_cycle_check(1);
    check(rt_rc_share(d) == 0 && rt_rc_count(d) == -1, "self-containing dict refused");
    int64_t dag = arr();
    int64_t leaf = arr();
    push(dag, leaf);
    push(dag, leaf);                       /* diamond, not a cycle */
    check(rt_rc_share(dag) == 1, "DAG with shared edge accepted");
    set_cycle_check(0);
    rt_rc_release(dag);

    printf("(f) 100k-object graph share + release\n");
    before = rt_heap_registry_count();
    int64_t big = build_graph(100000);
    clock_t t0 = clock();
    int shared = rt_rc_share(big);
    clock_t t1 = clock();
    int released = rt_rc_release(big);
    clock_t t2 = clock();
    check(shared && released && rt_heap_registry_count() == before, "100k graph fully freed");
    printf("  info share=%.3fms release=%.3fms (100001 objects)\n",
           1000.0 * (t1 - t0) / CLOCKS_PER_SEC, 1000.0 * (t2 - t1) / CLOCKS_PER_SEC);

    if (failures) printf("SELFCHECK FAILED (%d failures)\n", failures);
    else printf("SELFCHECK PASSED (0 failures)\n");
    return failures ? 1 : 0;
}
