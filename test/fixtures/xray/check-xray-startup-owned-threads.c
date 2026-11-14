/*
 * Source-only contract fixture for the real Linux XRay startup-owned-thread
 * ledger. Each scenario runs in a child process because the provider state is
 * intentionally process-lifetime and one-shot.
 *
 * This proves only the owned spawn wrapper/ledger contract. It does not prove
 * absence of foreign or constructor threads, scheduler quiescence, profile
 * admission, or compiler-rt sled patching.
 */
#define _GNU_SOURCE 1
#include <errno.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#include "xray/xray_startup_owned_threads_v1.h"

int64_t simple_xray_resident_control_enter_v1(void);
void simple_xray_resident_control_leave_v1(void);
void simple_xray_resident_runtime_ready_v1(void);
int64_t simple_xray_startup_no_owned_threads_begin_v1(void);
int64_t simple_xray_startup_no_owned_threads_end_v1(void);
void simple_xray_startup_window_seal_v1(void);

static _Atomic int g_entry_calls;
static int g_checks;

#define CHECK(condition, label) do { \
    ++g_checks; \
    if (!(condition)) { \
        fprintf(stderr, "FAIL %s\n", label); \
        return 1; \
    } \
} while (0)

static void *count_entry(void *unused) {
    (void)unused;
    atomic_fetch_add_explicit(&g_entry_calls, 1, memory_order_relaxed);
    return NULL;
}

/* Deliberately foreign test thread: it cannot borrow another thread's window.
 * This does not establish foreign-thread exclusion for an admitted profile. */
static void *probe_other_window_owner(void *argument) {
    int *valid = argument;
    *valid = 0;
    if (simple_xray_resident_control_enter_v1() != 1) return NULL;
    *valid = simple_xray_startup_current_owner_v1() == 0 &&
        simple_xray_startup_no_owned_threads_end_v1() == 0;
    simple_xray_resident_control_leave_v1();
    return NULL;
}

static int run_begin_and_spawn_case(void) {
    pthread_t thread;
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "begin is denied without control/readiness");
    simple_xray_resident_runtime_ready_v1();
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "begin is denied without control after readiness");
    CHECK(simple_xray_resident_control_enter_v1() == 1,
        "control owner acquired after readiness");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 1,
        "first begin acquires the one-shot window");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "second begin is denied while held");
    CHECK(simple_xray_startup_current_owner_v1() == 1,
        "begin binds the current native thread");
    simple_xray_resident_control_leave_v1();
    CHECK(simple_xray_startup_current_owner_v1() == 0,
        "query requires current control ownership");
    int other_refused = 0;
    CHECK(pthread_create(&thread, NULL, probe_other_window_owner, &other_refused) == 0,
        "foreign diagnostic thread starts outside owned creation contract");
    CHECK(pthread_join(thread, NULL) == 0, "foreign diagnostic thread joins");
    CHECK(other_refused == 1, "another control owner cannot borrow or end window");
    CHECK(simple_xray_resident_control_enter_v1() == 1,
        "startup owner reacquires control after consumer handoff");
    CHECK(simple_xray_startup_current_owner_v1() == 1,
        "control release preserves native startup-thread association");
    CHECK(SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1(&thread, NULL, count_entry, NULL) == EAGAIN,
        "owned spawn is refused while window is held");
    CHECK(atomic_load_explicit(&g_entry_calls, memory_order_relaxed) == 0,
        "refused spawn never invokes entry");
    CHECK(simple_xray_startup_no_owned_threads_end_v1() == 1,
        "end closes and spends the held window");
    CHECK(simple_xray_startup_no_owned_threads_end_v1() == 0,
        "second end is denied");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "spent bit denies reacquisition before any spawn");
    CHECK(SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1(&thread, NULL, count_entry, NULL) == 0,
        "spawn is admitted after the held window closes");
    CHECK(pthread_join(thread, NULL) == 0, "admitted owned thread joins");
    CHECK(atomic_load_explicit(&g_entry_calls, memory_order_relaxed) == 1,
        "admitted thread entry ran once");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "successful owned spawn permanently denies a later window");
    simple_xray_resident_control_leave_v1();
    return 0;
}

static int run_seal_idle_case(void) {
    pthread_t thread;
    simple_xray_resident_runtime_ready_v1();
    simple_xray_startup_window_seal_v1();
    CHECK(simple_xray_resident_control_enter_v1() == 1,
        "control owner acquired after idle seal");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "idle seal prevents later begin");
    CHECK(SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1(&thread, NULL, count_entry, NULL) == 0,
        "idle seal does not block ordinary owned spawn");
    CHECK(pthread_join(thread, NULL) == 0,
        "post-seal owned thread joins");
    simple_xray_resident_control_leave_v1();
    return 0;
}

static int run_seal_held_case(void) {
    simple_xray_resident_runtime_ready_v1();
    CHECK(simple_xray_resident_control_enter_v1() == 1,
        "control owner acquired before held seal");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 1,
        "held-seal case begins window");
    simple_xray_startup_window_seal_v1();
    CHECK(simple_xray_startup_current_owner_v1() == 0,
        "seal invalidates local startup ownership");
    CHECK(simple_xray_startup_no_owned_threads_end_v1() == 0,
        "seal clears held state so end fails closed");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "held seal permanently prevents reacquisition");
    simple_xray_resident_control_leave_v1();
    return 0;
}

static int run_prior_spawn_case(void) {
    pthread_t thread;
    simple_xray_resident_runtime_ready_v1();
    CHECK(SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1(&thread, NULL, count_entry, NULL) == 0,
        "prior owned spawn succeeds");
    CHECK(pthread_join(thread, NULL) == 0, "prior owned spawn joins");
    CHECK(simple_xray_resident_control_enter_v1() == 1,
        "control owner acquired after prior spawn");
    CHECK(simple_xray_startup_no_owned_threads_begin_v1() == 0,
        "prior successful spawn permanently denies begin");
    simple_xray_resident_control_leave_v1();
    return 0;
}

typedef int (*scenario_fn)(void);

static int run_scenario(const char *name, scenario_fn scenario) {
    pid_t child = fork();
    if (child < 0) {
        perror("fork");
        return 0;
    }
    if (child == 0) _exit(scenario() == 0 ? 0 : 1);
    int status = 0;
    if (waitpid(child, &status, 0) != child || !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        fprintf(stderr, "FAIL scenario %s\n", name);
        return 0;
    }
    printf("PASS scenario %s\n", name);
    return 1;
}

int main(void) {
    int passed = 0;
    passed += run_scenario("one-shot-begin-and-held-spawn-refusal", run_begin_and_spawn_case);
    passed += run_scenario("idle-seal-before-main", run_seal_idle_case);
    passed += run_scenario("seal-held-window-fails-closed", run_seal_held_case);
    passed += run_scenario("prior-owned-spawn-denies-window", run_prior_spawn_case);
    if (passed != 4) return 1;
    puts("PASS — startup owned-thread ledger source contract (owned spawn boundary only)");
    return 0;
}
