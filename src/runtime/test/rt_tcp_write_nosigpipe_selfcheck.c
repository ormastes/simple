/* Compile the actual native owner, as in rt_allocation_registry_churn_selfcheck.
 * The fallback variant removes socket capabilities only in this test TU. */
#if defined(SIMPLE_TCP_CHECK_THREAD_FALLBACK)
#include <sys/socket.h>
#undef MSG_NOSIGNAL
#undef SO_NOSIGPIPE
#endif
#include "../runtime_native.c"
#include <assert.h>
#include <sys/wait.h>

static int64_t payload(int text, const uint8_t *bytes, size_t len) {
    if (text) return rt_string_new(bytes, len);
    SplArray *a = rt_byte_array_new_len(len);
    assert(a);
    if (len) memcpy((void *)(uintptr_t)rt_array_data_ptr(a), bytes, len);
    return (int64_t)(uintptr_t)a;
}
static int64_t send_value(int which, int fd, int64_t value) {
    if (which == 0) return rt_io_tcp_write(fd, value);
    if (which == 1) return rt_io_tcp_write_text(fd, value);
    return rt_io_tcp_write_bytes(fd, value);
}
static void drop_value(int which, int64_t value) {
    if (which == 1) rt_string_free(value);
    else rt_array_free((SplArray *)(uintptr_t)value);
}
static void default_sigpipe(void) {
    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = SIG_DFL;
    sigemptyset(&action.sa_mask);
    assert(sigaction(SIGPIPE, &action, NULL) == 0);
    sigset_t set;
    sigemptyset(&set); sigaddset(&set, SIGPIPE);
    assert(pthread_sigmask(SIG_UNBLOCK, &set, NULL) == 0);
}
static void closed_peer(int which, int pending_control) {
    default_sigpipe();
    sigset_t set, old, pending;
    sigemptyset(&set); sigaddset(&set, SIGPIPE);
    if (pending_control) {
        assert(pthread_sigmask(SIG_BLOCK, &set, &old) == 0);
        assert(pthread_kill(pthread_self(), SIGPIPE) == 0);
    }
    int pair[2]; assert(socketpair(AF_UNIX, SOCK_STREAM, 0, pair) == 0);
    assert(close(pair[1]) == 0);
    const uint8_t bytes[] = {65, 0, 255};
    int64_t value = payload(which == 1, bytes, sizeof(bytes));
    errno = 0;
    assert(send_value(which, pair[0], value) == -1);
    assert(errno == EPIPE);
    assert(fcntl(pair[0], F_GETFD) >= 0); /* write never closes the caller fd */
    struct sigaction after; assert(sigaction(SIGPIPE, NULL, &after) == 0);
    assert(after.sa_handler == SIG_DFL);
    sigset_t mask; assert(pthread_sigmask(SIG_SETMASK, NULL, &mask) == 0);
    assert(sigismember(&mask, SIGPIPE) == pending_control);
    assert(sigpending(&pending) == 0);
    assert(sigismember(&pending, SIGPIPE) == pending_control);
    if (pending_control) {
        int signal_number = 0;
        assert(sigwait(&set, &signal_number) == 0 && signal_number == SIGPIPE);
        assert(pthread_sigmask(SIG_SETMASK, &old, NULL) == 0);
    }
    drop_value(which, value); assert(rt_io_tcp_close(pair[0]));
}
static void controls(int which) {
    int pair[2]; assert(socketpair(AF_UNIX, SOCK_STREAM, 0, pair) == 0);
    const uint8_t bytes[] = {65, 0, 128, 255}; uint8_t received[4];
    int64_t value = payload(which == 1, bytes, sizeof(bytes));
    assert(send_value(which, pair[0], value) == 4);
    assert(read(pair[1], received, 4) == 4 && memcmp(bytes, received, 4) == 0);
    errno = 0; assert(send_value(which, -1, value) == -1 && errno == EBADF);
    drop_value(which, value);
    value = payload(which == 1, bytes, 0);
    assert(send_value(which, -1, value) == 0); /* unchanged empty fast path */
    drop_value(which, value);
    int size = 4096; assert(setsockopt(pair[0], SOL_SOCKET, SO_SNDBUF, &size, sizeof(size)) == 0);
    assert(fcntl(pair[0], F_SETFL, O_NONBLOCK) == 0);
    size_t len = 1024 * 1024; uint8_t *large = malloc(len); assert(large);
    for (size_t i = 0; i < len; ++i) large[i] = (uint8_t)(i % 251);
    value = payload(which == 1, large, len);
    int64_t sent = send_value(which, pair[0], value);
    assert(sent > 0 && (uint64_t)sent < len); /* one syscall, no hidden write_all */
    uint8_t *prefix = malloc((size_t)sent); assert(prefix);
    size_t got = 0;
    while (got < (size_t)sent) {
        ssize_t n = read(pair[1], prefix + got, (size_t)sent - got);
        assert(n > 0); got += (size_t)n;
    }
    assert(memcmp(prefix, large, (size_t)sent) == 0);
    /* Fill the nonblocking socket: EAGAIN must remain an error, not zero. */
    for (int i = 0; ; ++i) {
        assert(i < 512);
        errno = 0; int64_t n = send_value(which, pair[0], value);
        if (n < 0) { assert(errno == EAGAIN || errno == EWOULDBLOCK); break; }
        assert(n > 0 && (uint64_t)n <= len);
    }
    free(prefix); free(large); drop_value(which, value);
    assert(rt_io_tcp_close(pair[0])); assert(close(pair[1]) == 0);
}
int main(void) {
    int failed = 0;
    for (int which = 0; which < 3; ++which) {
        for (int pending_control = 0; pending_control < 2; ++pending_control) {
            pid_t child = fork(); assert(child >= 0);
            if (child == 0) { alarm(10); closed_peer(which, pending_control); _exit(0); }
            int status = 0; assert(waitpid(child, &status, 0) == child);
            if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                fprintf(stderr, "peerclosed variant=%d pending=%d signal=%d exit=%d\n", which, pending_control,
                    WIFSIGNALED(status) ? WTERMSIG(status) : 0, WIFEXITED(status) ? WEXITSTATUS(status) : -1);
                failed = 1;
            }
        }
        controls(which);
    }
    if (failed) return 1;
    puts("PASS tcp write/write_text/write_bytes: default-SIGPIPE child survives EPIPE; pending signal preserved; exact/partial bytes, EAGAIN, EBADF, empty and close controls");
    return 0;
}
