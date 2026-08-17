#include "runtime.h"

#include <assert.h>
#include <pty.h>
#include <signal.h>
#include <stdint.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>
#include <pthread.h>
#include <stdatomic.h>

static volatile sig_atomic_t prior_winch_seen;
static atomic_int race_phase;

static void* signal_during_teardown(void* unused) {
    (void)unused;
    bool acknowledged = false;
    for (;;) {
        int phase = atomic_load_explicit(&race_phase, memory_order_acquire);
        if (phase == 2) break;
        if (phase == 1 || phase == 3) {
            assert(raise(SIGWINCH) == 0);
            if (!acknowledged) {
                acknowledged = true;
                atomic_store_explicit(&race_phase, 3, memory_order_release);
            }
        }
    }
    return NULL;
}

static void prior_winch(int signum) {
    (void)signum;
    prior_winch_seen = 1;
}

static void assert_managed_mask_equal(const sigset_t* left, const sigset_t* right) {
    const int signals[] = {SIGHUP, SIGINT, SIGTERM, SIGWINCH};
    for (size_t i = 0; i < sizeof(signals) / sizeof(signals[0]); i++) {
        assert(sigismember(left, signals[i]) == sigismember(right, signals[i]));
    }
}

int main(void) {
    int master = -1;
    int slave = -1;
    assert(openpty(&master, &slave, NULL, NULL, NULL) == 0);
    int ready[2];
    int ack[2];
    assert(pipe(ready) == 0);
    assert(pipe(ack) == 0);

    pid_t child = fork();
    assert(child >= 0);
    if (child == 0) {
        close(master);
        close(ready[0]);
        close(ack[1]);
        assert(dup2(slave, STDIN_FILENO) == STDIN_FILENO);
        close(slave);

        struct termios before;
        assert(tcgetattr(STDIN_FILENO, &before) == 0);
        assert(rt_terminal_enable_raw_mode());
        struct termios active_raw;
        assert(tcgetattr(STDIN_FILENO, &active_raw) == 0);
        assert((active_raw.c_lflag & (ICANON | ECHO)) == 0);
        struct sigaction prior = {0};
        prior.sa_handler = prior_winch;
        assert(sigaction(SIGWINCH, &prior, NULL) == 0);

        sigset_t original_mask;
        assert(sigprocmask(SIG_SETMASK, NULL, &original_mask) == 0);

        int64_t scope = rt_terminal_signal_scope_begin();
        assert(scope != 0);
        assert(rt_terminal_signal_scope_begin() == 0);
        errno = 0;
        assert(rt_terminal_read_byte_interruptible(scope + 1) == -4);
        assert(errno == EINVAL);
        assert(write(ready[1], "B", 1) == 1);
        assert(rt_terminal_read_byte_interruptible(scope) == 'Z');
        assert(write(ready[1], "R", 1) == 1);
        assert(rt_terminal_read_byte_interruptible(scope) == -3);
        assert(write(ready[1], "W", 1) == 1);
        char proceed = 0;
        assert(read(ack[0], &proceed, 1) == 1 && proceed == 'T');
        assert(rt_terminal_read_byte_interruptible(scope) == -2);
        assert(rt_terminal_disable_raw_mode());
        assert(rt_terminal_signal_scope_end(scope));
        int ownership_probe = open("/dev/null", O_RDONLY);
        assert(ownership_probe >= 0);
        errno = 0;
        assert(!rt_terminal_signal_scope_end(scope));
        assert(errno == EINVAL);
        assert(fcntl(ownership_probe, F_GETFD) >= 0);
        close(ownership_probe);
        assert(rt_terminal_read_byte_interruptible(scope) == -4);

        sigset_t final_mask;
        assert(sigprocmask(SIG_SETMASK, NULL, &final_mask) == 0);
        assert_managed_mask_equal(&original_mask, &final_mask);

        raise(SIGWINCH);
        assert(prior_winch_seen == 1);
        struct termios after;
        assert(tcgetattr(STDIN_FILENO, &after) == 0);
        assert((before.c_lflag & (ICANON | ECHO)) ==
               (after.c_lflag & (ICANON | ECHO)));
        close(ready[1]);
        close(ack[0]);
        _exit(0);
    }

    close(slave);
    close(ready[1]);
    close(ack[0]);
    char state = 0;
    assert(read(ready[0], &state, 1) == 1 && state == 'B');
    assert(write(master, "Z", 1) == 1);
    assert(read(ready[0], &state, 1) == 1 && state == 'R');
    assert(kill(child, SIGWINCH) == 0);
    assert(read(ready[0], &state, 1) == 1 && state == 'W');
    assert(write(ack[1], "T", 1) == 1);
    assert(kill(child, SIGTERM) == 0);
    int status = 0;
    assert(waitpid(child, &status, 0) == child);
    close(master);
    close(ready[0]);
    close(ack[1]);
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
        assert(scope != 0);
        assert(write(eof_ready[1], "E", 1) == 1);
        assert(rt_terminal_read_byte_interruptible(scope) == -1);
        assert(rt_terminal_signal_scope_end(scope));
        close(eof_ready[1]);
        _exit(0);
    }
    close(eof_input[0]);
    close(eof_ready[1]);
    assert(read(eof_ready[0], &state, 1) == 1 && state == 'E');
    close(eof_input[1]);
    assert(waitpid(eof_child, &status, 0) == eof_child);
    close(eof_ready[0]);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    return 0;
}
