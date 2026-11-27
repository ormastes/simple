/* Deterministic Linux signal test for the production bounded stdin read. */
#define _POSIX_C_SOURCE 200809L
#include "runtime.h"

#include <errno.h>
#include <pthread.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

int64_t rt_stdin_read_timeout_v1(int64_t size, int64_t timeout_ms);

static SplArray g_empty_array;
static volatile sig_atomic_t g_signals_seen;
static int g_nonempty_array_requests;
static int g_push_calls;
static int g_clock_mode;
static int g_poll_calls;
static int g_failures;
static pthread_t g_reader_thread;

int __real_clock_gettime(clockid_t clock_id, struct timespec* value);
int __real_poll(struct pollfd* fds, nfds_t count, int timeout_ms);

#define CHECK(condition, message) do { \
    if (condition) printf("PASS %s\n", message); \
    else { printf("FAIL %s\n", message); ++g_failures; } \
} while (0)

int __wrap_clock_gettime(clockid_t clock_id, struct timespec* value) {
    if (g_clock_mode == 1) {
        errno = EIO;
        return -1;
    }
    if (g_clock_mode == 2 && clock_id == CLOCK_MONOTONIC) {
        value->tv_sec = sizeof(time_t) >= sizeof(int64_t)
            ? (time_t)INT64_MAX : (time_t)INT32_MAX;
        value->tv_nsec = 999999000L;
        return 0;
    }
    return __real_clock_gettime(clock_id, value);
}

int __wrap_poll(struct pollfd* fds, nfds_t count, int timeout_ms) {
    ++g_poll_calls;
    return __real_poll(fds, count, timeout_ms);
}

/* Narrow array-ABI shims: this fixture asserts timeout-empty behavior and
 * deliberately fails if the production function attempts a nonempty result. */
SplArray* rt_array_new(int64_t cap) {
    if (cap > 0) {
        ++g_nonempty_array_requests;
        return NULL;
    }
    return &g_empty_array;
}

int8_t rt_array_push(SplArray* array, int64_t value) {
    (void)array;
    (void)value;
    ++g_push_calls;
    return 0;
}

static void handle_signal(int signal_number) {
    (void)signal_number;
    ++g_signals_seen;
}

static void sleep_ms(long milliseconds) {
    struct timespec remaining = { milliseconds / 1000,
        (milliseconds % 1000) * 1000000L };
    while (nanosleep(&remaining, &remaining) != 0 && errno == EINTR) {}
}

static int64_t monotonic_ns(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * INT64_C(1000000000) + now.tv_nsec;
}

static void* interrupt_reader(void* unused) {
    (void)unused;
    sleep_ms(40);
    for (int i = 0; i < 8; ++i) {
        sleep_ms(20);
        (void)pthread_kill(g_reader_thread, SIGUSR1);
    }
    return NULL;
}

static void check_clock_fail_closed(void) {
    int polls_before = g_poll_calls;
    g_clock_mode = 1;
    int64_t failed_clock_result = rt_stdin_read_timeout_v1(16, 300);
    g_clock_mode = 0;
    CHECK(failed_clock_result == (int64_t)(uintptr_t)&g_empty_array,
        "monotonic clock failure returns the empty byte array");
    CHECK(g_poll_calls == polls_before,
        "monotonic clock failure returns before polling");

    polls_before = g_poll_calls;
    g_clock_mode = 2;
    int64_t overflow_result = rt_stdin_read_timeout_v1(16, 1);
    g_clock_mode = 0;
    CHECK(overflow_result == (int64_t)(uintptr_t)&g_empty_array,
        "unrepresentable absolute deadline returns the empty byte array");
    CHECK(g_poll_calls == polls_before,
        "deadline overflow returns before polling");
}

int main(void) {
    int saved_stdin = dup(STDIN_FILENO);
    int pipe_fds[2];
    if (saved_stdin < 0 || pipe(pipe_fds) != 0 ||
            dup2(pipe_fds[0], STDIN_FILENO) < 0) {
        perror("prepare unread stdin pipe");
        return 2;
    }
    close(pipe_fds[0]);
    /* Keep the writer open so poll observes an unread pipe, not EOF/HUP. */

    struct sigaction action;
    memset(&action, 0, sizeof(action));
    action.sa_handler = handle_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGUSR1, &action, NULL) != 0) {
        perror("sigaction");
        return 2;
    }

    check_clock_fail_closed();

    g_reader_thread = pthread_self();
    pthread_t interrupter;
    if (pthread_create(&interrupter, NULL, interrupt_reader, NULL) != 0) {
        perror("pthread_create");
        return 2;
    }
    const int64_t timeout_ms = 300;
    int64_t start = monotonic_ns();
    if (start < 0) return 2;
    int64_t result = rt_stdin_read_timeout_v1(16, timeout_ms);
    int64_t end = monotonic_ns();
    if (end < 0 || pthread_join(interrupter, NULL) != 0) return 2;

    int64_t elapsed_ms = (end - start + 999999) / 1000000;
    CHECK(g_signals_seen >= 7, "signals repeatedly interrupted the poll before its deadline");
    CHECK(result == (int64_t)(uintptr_t)&g_empty_array,
        "unread pipe returns the empty byte array on timeout");
    CHECK(g_nonempty_array_requests == 0 && g_push_calls == 0,
        "timeout path does not construct a nonempty byte array");
    CHECK(elapsed_ms >= 250, "timeout does not return substantially early");
    CHECK(elapsed_ms < 400,
        "repeated EINTR does not restart the full timeout interval");
    printf("elapsed_ms=%lld signals=%d timeout_ms=%lld\n",
        (long long)elapsed_ms, (int)g_signals_seen, (long long)timeout_ms);

    close(pipe_fds[1]);
    if (dup2(saved_stdin, STDIN_FILENO) < 0) return 2;
    close(saved_stdin);
    if (g_failures != 0) return 1;
    puts("PASS — production stdin timeout EINTR deadline selfcheck");
    return 0;
}
