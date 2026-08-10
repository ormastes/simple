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

static volatile sig_atomic_t prior_winch_seen;

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
        struct termios raw = before;
        cfmakeraw(&raw);
        assert(tcsetattr(STDIN_FILENO, TCSANOW, &raw) == 0);
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
        assert(tcsetattr(STDIN_FILENO, TCSANOW, &before) == 0);
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
