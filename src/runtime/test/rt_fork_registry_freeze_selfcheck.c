/* Self-check for the fork-child heap-registry freeze
 * (rt_core_immortal_registry_freeze_for_fork_child_v1, called by
 * rt_fork_shared_heap_v1 in the child). Membership must be unchanged across
 * the freeze: inherited objects stay live, erase exactly once, and may be
 * re-registered; child objects register and erase in the overlay. Checked
 * in a real fork child and in-process. Bug: doc/08_tracking/bug/mir_fork_child_heap_registry_cow_resize_2026-10-25.md
 *
 * Build + run:
 *   cc -std=gnu11 -O1 -o /tmp/rtfrz src/runtime/test/rt_fork_registry_freeze_selfcheck.c \
 *       src/runtime/runtime_native.c -lm -lpthread \
 *      -Wl,--unresolved-symbols=ignore-all && /tmp/rtfrz
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <sys/wait.h>
#include <unistd.h>

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_free(int64_t value);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_heap_registry_count(void);
extern void rt_core_immortal_registry_freeze_for_fork_child_v1(void);

static int failures = 0;
static void check(int cond, const char* what) {
    printf("  %s %s\n", cond ? "ok  " : "FAIL", what);
    if (!cond) failures++;
}

static int64_t mkstr(int i) {
    char buf[96];
    int n = snprintf(buf, sizeof buf, "fork registry freeze string number %06d padding", i);
    return rt_string_new((const uint8_t*)buf, (uint64_t)n);
}

#define N 4000
static int64_t inherited[N];

static int run_child_checks(void) {
    int64_t base = rt_heap_registry_count();
    int ok = 1;
    for (int i = 0; i < N; i++) ok &= rt_string_len(inherited[i]) > 0;
    check(ok, "inherited strings are still registered after the freeze");
    int64_t mine[N];
    for (int i = 0; i < N; i++) mine[i] = mkstr(N + i);
    check(rt_heap_registry_count() == base + N, "child strings register in the overlay");
    int freed = 0;
    for (int i = 0; i < N; i++) freed += rt_string_free(mine[i]) == 1;
    check(freed == N && rt_heap_registry_count() == base, "child strings erase from the overlay");
    check(rt_string_free(mine[0]) == 0, "overlay double free refused");
    check(rt_string_free(inherited[7]) == 1, "inherited string erases once");
    check(rt_string_free(inherited[7]) == 0, "inherited double free refused");
    check(rt_heap_registry_count() == base - 1, "count reflects the inherited erase");
    ok = 1;
    for (int i = 0; i < N; i++) if (i != 7) ok &= rt_string_len(inherited[i]) > 0;
    check(ok, "other inherited strings stay live after the erase");
    return failures;
}

int main(void) {
    for (int i = 0; i < N; i++) inherited[i] = mkstr(i);

    printf("fork child:\n");
    /* What rt_fork_shared_heap_v1 (runtime_fork.c) does in its child. */
    fflush(NULL);
    pid_t pid = fork();
    if (pid == 0) {
        rt_core_immortal_registry_freeze_for_fork_child_v1();
        _exit(run_child_checks() == 0 ? 0 : 1);
    }
    int status = 0;
    check(pid > 0 && waitpid(pid, &status, 0) == pid &&
          WIFEXITED(status) && WEXITSTATUS(status) == 0, "fork child checks pass");
    check(rt_heap_registry_count() >= N, "parent registry untouched by the child");

    printf("in-process freeze:\n");
    rt_core_immortal_registry_freeze_for_fork_child_v1();
    run_child_checks();
    rt_core_immortal_registry_freeze_for_fork_child_v1(); /* nested: no-op layer */
    check(rt_string_len(inherited[8]) > 0, "nested freeze keeps membership");

    printf("%s\n", failures == 0 ? "PASS" : "FAIL");
    return failures == 0 ? 0 : 1;
}
