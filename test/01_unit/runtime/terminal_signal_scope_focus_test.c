/* Focused POSIX ABI contract for the core-C terminal signal lease. */
#include "runtime.h"

#include <assert.h>
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <pthread.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

/* runtime_terminal.c contains tuple helpers although this focus test does not
 * call them; supply the value-runtime boundary so the TU links in isolation. */
int64_t rt_tuple_new(int64_t size) { (void)size; return 0; }
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    (void)tuple; (void)index; (void)value; return 0;
}
int64_t rt_value_int(int64_t value) { return value; }

static volatile sig_atomic_t prior_winch_seen = 0;
static void prior_winch(int signal_number) { (void)signal_number; prior_winch_seen = 1; }

typedef struct ScopeReadThread {
    int64_t scope;
    int64_t result;
} ScopeReadThread;

static void* scope_read_thread(void* raw) {
    ScopeReadThread* state = (ScopeReadThread*)raw;
    state->result = rt_terminal_read_byte_interruptible(state->scope);
    return NULL;
}

static void* scope_end_thread(void* raw) {
    ScopeReadThread* state = (ScopeReadThread*)raw;
    state->result = rt_terminal_signal_scope_end(state->scope) ? 1 : 0;
    return NULL;
}

int main(void) {
    int input[2];
    assert(pipe(input) == 0);
    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        close(input[1]);
        assert(dup2(input[0], STDIN_FILENO) == STDIN_FILENO);
        close(input[0]);
        struct sigaction prior = {0};
        prior.sa_handler = prior_winch;
        assert(sigaction(SIGWINCH, &prior, NULL) == 0);
        int64_t scope = rt_terminal_signal_scope_begin();
        assert(scope > 0);
        assert(rt_terminal_signal_scope_begin() == 0);
        errno = 0;
        assert(rt_terminal_read_byte_interruptible(scope + 1) == -4);
        assert(errno == EINVAL);
        assert(raise(SIGWINCH) == 0);
        assert(rt_terminal_read_byte_interruptible(scope) == -3);
        assert(raise(SIGTERM) == 0);
        assert(rt_terminal_read_byte_interruptible(scope) == -2);
        assert(rt_terminal_signal_scope_end(scope));
        errno = 0;
        assert(!rt_terminal_signal_scope_end(scope));
        assert(errno == EINVAL);
        assert(raise(SIGWINCH) == 0);
        assert(prior_winch_seen == 1);
        _exit(0);
    }
    close(input[0]);
    close(input[1]);
    int status = 0;
    assert(waitpid(child, &status, 0) == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);

    /* Exact panic reproducer: production panic must restore the PTY instead
       of leaving the invoking shell in raw mode. */
    int panic_master = -1;
    int panic_slave = -1;
    assert(openpty(&panic_master, &panic_slave, NULL, NULL, NULL) == 0);
    struct termios panic_before;
    assert(tcgetattr(panic_slave, &panic_before) == 0);
    pid_t panic_child = fork();
    assert(panic_child >= 0);
    if (panic_child == 0) {
        close(panic_master);
        assert(dup2(panic_slave, STDIN_FILENO) == STDIN_FILENO);
        close(panic_slave);
        assert(rt_terminal_signal_scope_begin() > 0);
        assert(rt_terminal_enable_raw_mode());
        rt_panic("intentional terminal restoration contract");
        _exit(99);
    }
    close(panic_slave);
    assert(waitpid(panic_child, &status, 0) == panic_child);
    assert((WIFSIGNALED(status)) ||
           (WIFEXITED(status) && WEXITSTATUS(status) != 0));
    struct termios panic_after;
    assert(tcgetattr(panic_master, &panic_after) == 0);
    assert((panic_before.c_lflag & (ICANON | ECHO)) ==
           (panic_after.c_lflag & (ICANON | ECHO)));
    close(panic_master);

    /* Adjacent panic owners: Simple assert/precondition failures lower through
       the contract helpers, not rt_panic, and must restore the same PTY state. */
    for (int contract_case = 0; contract_case < 2; contract_case++) {
        int contract_master = -1;
        int contract_slave = -1;
        assert(openpty(&contract_master, &contract_slave, NULL, NULL, NULL) == 0);
        struct termios contract_before;
        assert(tcgetattr(contract_slave, &contract_before) == 0);
        pid_t contract_child = fork();
        assert(contract_child >= 0);
        if (contract_child == 0) {
            close(contract_master);
            assert(dup2(contract_slave, STDIN_FILENO) == STDIN_FILENO);
            close(contract_slave);
            assert(rt_terminal_signal_scope_begin() > 0);
            assert(rt_terminal_enable_raw_mode());
            const uint8_t owner[] = "terminal_contract";
            if (contract_case == 0) {
                simple_contract_check(0, 5, owner, sizeof(owner) - 1);
            } else {
                const uint8_t message[] = "intentional contract restoration";
                simple_contract_check_msg(0, 5, owner, sizeof(owner) - 1,
                                          message, sizeof(message) - 1);
            }
            _exit(98);
        }
        close(contract_slave);
        assert(waitpid(contract_child, &status, 0) == contract_child);
        assert(WIFSIGNALED(status) ||
               (WIFEXITED(status) && WEXITSTATUS(status) != 0));
        struct termios contract_after;
        assert(tcgetattr(contract_master, &contract_after) == 0);
        assert((contract_before.c_lflag & (ICANON | ECHO)) ==
               (contract_after.c_lflag & (ICANON | ECHO)));
        close(contract_master);
    }

    /* Adjacent prevention: signal delivery from another thread may overlap
       teardown, but must never write through a descriptor after it is reused. */
    atomic_store(&race_phase, 0);
    pthread_t sender;
    assert(pthread_create(&sender, NULL, signal_during_teardown, NULL) == 0);
    int expected_read = open("/dev/null", O_RDONLY);
    int expected_write = open("/dev/null", O_RDONLY);
    assert(expected_read >= 0 && expected_write >= 0);
    close(expected_read);
    close(expected_write);
    int64_t race_scope = rt_terminal_signal_scope_begin();
    assert(race_scope > 0);
    atomic_store_explicit(&race_phase, 1, memory_order_release);
    while (atomic_load_explicit(&race_phase, memory_order_acquire) != 3) {
    }
    assert(rt_terminal_read_byte_interruptible(race_scope) == -3);
    assert(rt_terminal_signal_scope_end(race_scope));
    int reused_pipe[2];
    assert(pipe(reused_pipe) == 0);
    assert(reused_pipe[0] == expected_read);
    assert(reused_pipe[1] == expected_write);
    int reused_flags = fcntl(reused_pipe[0], F_GETFL, 0);
    assert(reused_flags >= 0);
    assert(fcntl(reused_pipe[0], F_SETFL, reused_flags | O_NONBLOCK) == 0);
    atomic_store_explicit(&race_phase, 2, memory_order_release);
    assert(pthread_join(sender, NULL) == 0);
    unsigned char stale_wake = 0;
    errno = 0;
    assert(read(reused_pipe[0], &stale_wake, 1) == -1);
    assert(errno == EAGAIN || errno == EWOULDBLOCK);
    close(reused_pipe[0]);
    close(reused_pipe[1]);

    int eof_input[2];
    int eof_ready[2];
    assert(pipe(eof_input) == 0);
    assert(pipe(eof_ready) == 0);
    pid_t eof_child = fork();
    assert(eof_child >= 0);
    if (eof_child == 0) {
        close(eof_input[1]);
        close(eof_ready[0]);
        assert(dup2(eof_input[0], STDIN_FILENO) == STDIN_FILENO);
        close(eof_input[0]);
        int64_t scope = rt_terminal_signal_scope_begin();
        assert(scope > 0);
        ScopeReadThread first = {.scope = scope, .result = -99};
        ScopeReadThread second = {.scope = scope, .result = -99};
        ScopeReadThread closer = {.scope = scope, .result = -99};
        pthread_t first_id, second_id, closer_id;
        assert(pthread_create(&first_id, NULL, scope_read_thread, &first) == 0);
        struct timespec reader_admission_delay = {.tv_sec = 0, .tv_nsec = 10000000};
        assert(nanosleep(&reader_admission_delay, NULL) == 0);
        assert(pthread_create(&second_id, NULL, scope_read_thread, &second) == 0);
        assert(pthread_create(&closer_id, NULL, scope_end_thread, &closer) == 0);
        assert(pthread_join(first_id, NULL) == 0);
        assert(pthread_join(second_id, NULL) == 0);
        assert(pthread_join(closer_id, NULL) == 0);
        assert(closer.result == 1);
        assert((first.result == -4 && second.result == -2) ||
               (first.result == -2 && second.result == -4));
        _exit(0);
    }
    close(concurrent_input[0]);
    assert(waitpid(concurrent_child, &status, 0) == concurrent_child);
    close(concurrent_input[1]);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    return 0;
}
