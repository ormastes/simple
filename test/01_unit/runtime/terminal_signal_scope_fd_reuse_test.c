#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

static atomic_int install_calls;
static atomic_int fail_install_call;
static atomic_int failure_reached;
static atomic_int allow_failure;
static atomic_int park_handler;
static atomic_int handler_loaded;
static atomic_int handler_target;
static atomic_int release_handler;
static atomic_int after_retire;
static atomic_int quiesce_observed;
static atomic_int close_while_inflight;

static int test_sigaction(int signum, const struct sigaction* action,
                          struct sigaction* previous) {
    if (previous != NULL) {
        int call = atomic_fetch_add_explicit(&install_calls, 1, memory_order_acq_rel) + 1;
        if (call == atomic_load_explicit(&fail_install_call, memory_order_acquire)) {
            atomic_store_explicit(&failure_reached, 1, memory_order_release);
            while (!atomic_load_explicit(&allow_failure, memory_order_acquire)) {
            }
            errno = EIO;
            return -1;
        }
    }
    return sigaction(signum, action, previous);
}

static void test_handler_target_loaded(int target) {
    if (target < 0 || !atomic_load_explicit(&park_handler, memory_order_acquire)) return;
    atomic_store_explicit(&handler_target, target, memory_order_release);
    atomic_store_explicit(&handler_loaded, 1, memory_order_release);
    while (!atomic_load_explicit(&release_handler, memory_order_acquire)) {
    }
}

static void test_after_retire(void) {
    atomic_store_explicit(&after_retire, 1, memory_order_release);
}

static void test_quiesce_wait(void) {
    atomic_store_explicit(&quiesce_observed, 1, memory_order_release);
}

static void test_before_close(int target) {
    (void)target;
    if (atomic_load_explicit(&park_handler, memory_order_acquire) &&
        !atomic_load_explicit(&release_handler, memory_order_acquire)) {
        atomic_store_explicit(&close_while_inflight, 1, memory_order_release);
    }
}

#define SPL_TERMINAL_SCOPE_BEGIN test_terminal_scope_begin
#define SPL_TERMINAL_SCOPE_READ test_terminal_scope_read
#define SPL_TERMINAL_SCOPE_END test_terminal_scope_end
#define SPL_TERMINAL_SCOPE_EMERGENCY_RESTORE test_terminal_scope_emergency_restore
#define SPL_TERMINAL_SCOPE_SIGACTION test_sigaction
#define SPL_TERMINAL_SCOPE_TEST_HANDLER_TARGET_LOADED test_handler_target_loaded
#define SPL_TERMINAL_SCOPE_TEST_AFTER_RETIRE test_after_retire
#define SPL_TERMINAL_SCOPE_TEST_QUIESCE_WAIT test_quiesce_wait
#define SPL_TERMINAL_SCOPE_TEST_BEFORE_CLOSE test_before_close
#include "runtime_terminal_signal_scope_impl.h"

static int64_t begin_result;
static bool end_result;

static void reset_test_state(void) {
    atomic_store(&install_calls, 0);
    atomic_store(&fail_install_call, 0);
    atomic_store(&failure_reached, 0);
    atomic_store(&allow_failure, 0);
    atomic_store(&park_handler, 1);
    atomic_store(&handler_loaded, 0);
    atomic_store(&handler_target, -1);
    atomic_store(&release_handler, 0);
    atomic_store(&after_retire, 0);
    atomic_store(&quiesce_observed, 0);
    atomic_store(&close_while_inflight, 0);
    begin_result = -1;
    end_result = false;
}

static void* begin_scope(void* unused) {
    (void)unused;
    begin_result = test_terminal_scope_begin();
    return NULL;
}

static void* raise_hup(void* unused) {
    (void)unused;
    assert(raise(SIGHUP) == 0);
    return NULL;
}

static void* raise_winch(void* unused) {
    (void)unused;
    assert(raise(SIGWINCH) == 0);
    return NULL;
}

static void* end_scope(void* raw_scope) {
    int64_t scope = *(int64_t*)raw_scope;
    end_result = test_terminal_scope_end(scope);
    return NULL;
}

static void wait_until(atomic_int* state) {
    while (!atomic_load_explicit(state, memory_order_acquire)) {
    }
}

static void assert_exact_reuse_is_empty(int retired_write) {
    int probe[2];
    assert(pipe(probe) == 0);
    assert(probe[1] == retired_write);
    int flags = fcntl(probe[0], F_GETFL, 0);
    assert(flags >= 0);
    assert(fcntl(probe[0], F_SETFL, flags | O_NONBLOCK) == 0);
    char byte = 0;
    errno = 0;
    assert(read(probe[0], &byte, 1) == -1);
    assert(errno == EAGAIN || errno == EWOULDBLOCK);
    close(probe[0]);
    close(probe[1]);
}

static void prior_hup(int signum) {
    (void)signum;
}

static void test_partial_begin_rollback_waits_before_exact_fd_reuse(void) {
    struct sigaction prior = {0};
    struct sigaction original = {0};
    prior.sa_handler = prior_hup;
    sigemptyset(&prior.sa_mask);
    assert(sigaction(SIGHUP, &prior, &original) == 0);

    reset_test_state();
    atomic_store(&fail_install_call, 2);
    pthread_t beginner;
    pthread_t sender;
    assert(pthread_create(&beginner, NULL, begin_scope, NULL) == 0);
    wait_until(&failure_reached);
    assert(pthread_create(&sender, NULL, raise_hup, NULL) == 0);
    wait_until(&handler_loaded);
    int retired_write = atomic_load_explicit(&handler_target, memory_order_acquire);
    atomic_store_explicit(&allow_failure, 1, memory_order_release);
    wait_until(&after_retire);
    wait_until(&quiesce_observed);
    assert(atomic_load(&close_while_inflight) == 0);
    atomic_store_explicit(&release_handler, 1, memory_order_release);
    assert(pthread_join(sender, NULL) == 0);
    assert(pthread_join(beginner, NULL) == 0);
    assert(begin_result == 0);
    assert(atomic_load(&close_while_inflight) == 0);

    struct sigaction restored = {0};
    assert(sigaction(SIGHUP, NULL, &restored) == 0);
    assert(restored.sa_handler == prior_hup);
    assert_exact_reuse_is_empty(retired_write);
    assert(sigaction(SIGHUP, &original, NULL) == 0);
}

static void test_end_waits_before_exact_fd_reuse(void) {
    reset_test_state();
    int64_t scope = test_terminal_scope_begin();
    assert(scope > 0);
    pthread_t sender;
    pthread_t closer;
    assert(pthread_create(&sender, NULL, raise_winch, NULL) == 0);
    wait_until(&handler_loaded);
    int retired_write = atomic_load_explicit(&handler_target, memory_order_acquire);
    assert(pthread_create(&closer, NULL, end_scope, &scope) == 0);
    wait_until(&after_retire);
    wait_until(&quiesce_observed);
    assert(atomic_load(&close_while_inflight) == 0);
    atomic_store_explicit(&release_handler, 1, memory_order_release);
    assert(pthread_join(sender, NULL) == 0);
    assert(pthread_join(closer, NULL) == 0);
    assert(end_result);
    assert(atomic_load(&close_while_inflight) == 0);
    assert_exact_reuse_is_empty(retired_write);
}

int main(void) {
    test_partial_begin_rollback_waits_before_exact_fd_reuse();
    test_end_waits_before_exact_fd_reuse();
    return 0;
}
