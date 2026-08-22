#define _POSIX_C_SOURCE 200809L
#include "hal_provider_sealed_session_v1.h"

#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static int64_t now_ms(void) {
    struct timespec t;
    if (clock_gettime(CLOCK_MONOTONIC, &t) != 0) return -1;
    return (int64_t)t.tv_sec * 1000 + t.tv_nsec / 1000000;
}

static int write_full(int fd, const unsigned char *p, size_t n) {
    size_t at = 0;
    while (at < n) {
        ssize_t k = write(fd, p + at, n - at);
        if (k > 0) at += (size_t)k;
        else if (k < 0 && errno == EINTR) continue;
        else return 0;
    }
    return 1;
}

static int read_line_deadline(int fd, unsigned char *p, size_t cap,
                              int64_t deadline, size_t *n_out) {
    size_t n = 0;
    while (n + 1 < cap) {
        struct pollfd f = { .fd = fd, .events = POLLIN | POLLHUP, .revents = 0 };
        int64_t current = now_ms();
        int remaining;
        int ready;
        if (current < 0 || current >= deadline) return 0;
        remaining = (int)(deadline - current);
        ready = poll(&f, 1, remaining);
        if (ready < 0 && errno == EINTR) continue;
        if (ready <= 0) return 0;
        {
            ssize_t k = read(fd, p + n, cap - n - 1);
            if (k > 0) {
                unsigned char *newline = memchr(p + n, '\n', (size_t)k);
                n += (size_t)k;
                if (newline) {
                    if ((size_t)(newline - p) + 1 != n) return 0;
                    p[n] = 0; *n_out = n; return 1;
                }
            } else if (k < 0 && errno == EINTR) continue;
            else return 0;
        }
    }
    return 0;
}

static void lane_kill(HalSealedLaneV1 *lane) {
    int status;
    if (lane->fd_in >= 0) close(lane->fd_in);
    if (lane->fd_out >= 0) close(lane->fd_out);
    lane->fd_in = lane->fd_out = -1;
    if (lane->pid > 1) {
        if (kill(lane->pid, SIGKILL) != 0 && errno != ESRCH) { }
        while (waitpid(lane->pid, &status, 0) < 0 && errno == EINTR) { }
        lane->reaped = 1;
    }
    lane->pid = -1;
    lane->healthy = 0;
}

static int spawn_lane(HalSealedLaneV1 *lane, const char *launcher,
                      const char *worker, int64_t deadline_ms) {
    int to_child[2] = {-1, -1}, from_child[2] = {-1, -1};
    char deadline_text[32];
    pid_t pid;
    size_t n = 0;
    int64_t ready_deadline;
    if (!launcher || launcher[0] != '/' || !worker || worker[0] != '/' ||
        deadline_ms <= 0 || pipe(to_child) != 0) return 0;
    if (pipe(from_child) != 0) {
        close(to_child[0]); close(to_child[1]); return 0;
    }
    (void)snprintf(deadline_text, sizeof(deadline_text), "%lld", (long long)deadline_ms);
    pid = fork();
    if (pid < 0) {
        close(to_child[0]); close(to_child[1]);
        close(from_child[0]); close(from_child[1]); return 0;
    }
    if (pid == 0) {
        dup2(to_child[0], STDIN_FILENO);
        dup2(from_child[1], STDOUT_FILENO);
        close(to_child[0]); close(to_child[1]); close(from_child[0]); close(from_child[1]);
        execl(launcher, launcher, "--session", deadline_text, "512", worker, (char *)0);
        _exit(127);
    }
    close(to_child[0]); close(from_child[1]);
    memset(lane, 0, sizeof(*lane));
    lane->fd_in = to_child[1]; lane->fd_out = from_child[0]; lane->pid = (int)pid;
    lane->generation = 1; lane->next_sequence = 1;
    ready_deadline = now_ms() + deadline_ms;
    {
        int sandbox_pid = 0, writable = -1, environment = -1, shared = -1;
        int initialized = 0, sealed = 0, consumed = 0;
        if (!read_line_deadline(lane->fd_out, lane->output,
                                sizeof(lane->output), ready_deadline, &n) ||
            sscanf((char *)lane->output,
                   "HALSESSION1|%d|%d|%d|%d|%d|%d%n",
                   &sandbox_pid, &writable, &environment, &shared,
                   &initialized, &sealed, &consumed) != 6 ||
            consumed <= 0 || (size_t)consumed + 1 != n ||
            lane->output[consumed] != '\n' || sandbox_pid <= 1 ||
            writable != 0 || environment != 0 || shared != 0 ||
            initialized != 1 || sealed != 1) {
            lane_kill(lane); return 0;
        }
        lane->sandbox_pid = sandbox_pid;
        lane->isolation_valid = 1;
    }
    lane->healthy = 1;
    return 1;
}

int hal_sealed_session_prepare_v1(HalSealedSessionV1 *s,
                                  const HalSealedSessionConfigV1 *c) {
    int i;
    if (!s || !c || c->deadline_ms <= 0) return 0;
    memset(s, 0, sizeof(*s));
    for (i = 0; i < HAL_SEALED_LANES_V1; ++i) {
        s->lane[i].fd_in = s->lane[i].fd_out = s->lane[i].pid = -1;
        if (!spawn_lane(&s->lane[i], c->launcher, c->worker[i], c->deadline_ms)) {
            while (--i >= 0) lane_kill(&s->lane[i]);
            return 0;
        }
        s->prepare_spawn_count++;
    }
    s->deadline_ms = c->deadline_ms;
    s->prepared = 1;
    return 1;
}

int hal_sealed_session_seal_v1(HalSealedSessionV1 *s) {
    int i;
    if (!s || !s->prepared || s->sealed) return 0;
    for (i = 0; i < HAL_SEALED_LANES_V1; ++i)
        if (!s->lane[i].healthy || s->lane[i].pid <= 1 ||
            (kill(s->lane[i].pid, 0) != 0 && errno != EPERM)) return 0;
    s->sealed = 1;
    return 1;
}

int hal_sealed_session_enter_critical_v1(HalSealedSessionV1 *s) {
    if (!s || !s->sealed || s->critical_entered) return 0;
    s->critical_entered = 1;
    return 1;
}

int hal_sealed_session_leave_critical_v1(HalSealedSessionV1 *s) {
    if (!s || !s->critical_entered) return 0;
    s->critical_entered = 0;
    s->sealed = 0;
    return 1;
}

int hal_sealed_session_invoke_mask_v1(
        HalSealedSessionV1 *s, uint64_t invocation, unsigned lane_mask,
        const unsigned char *request, size_t request_size,
        unsigned char result[3][HAL_SEALED_FRAME_CAP_V1],
        size_t result_size[3]) {
    char reset[96], expected[96];
    int i, reset_size, expected_size;
    int64_t deadline;
    if (!s || !s->sealed || !s->critical_entered || invocation == 0 ||
        lane_mask == 0 || (lane_mask & ~7u) != 0 || !request ||
        request_size < 2 || request_size >= HAL_SEALED_FRAME_CAP_V1 ||
        request[request_size - 1] != '\n' || !result || !result_size) return 0;
    deadline = now_ms() + s->deadline_ms;
    for (i = 0; i < 3; ++i) result_size[i] = 0;
    for (i = 0; i < 3; ++i) {
        HalSealedLaneV1 *l = &s->lane[i];
        if ((lane_mask & (1u << i)) == 0) continue;
        if (!l->healthy) return 0;
        reset_size = snprintf(reset, sizeof(reset), "HALRESET1|%llu|%llu|%llu\n",
            (unsigned long long)l->generation,
            (unsigned long long)l->next_sequence,
            (unsigned long long)invocation);
        if (reset_size <= 0 || (size_t)reset_size >= sizeof(reset) ||
            !write_full(l->fd_in, (unsigned char *)reset, (size_t)reset_size)) {
            l->healthy = 0; return 0;
        }
    }
    for (i = 0; i < 3; ++i) {
        HalSealedLaneV1 *l = &s->lane[i];
        size_t n = 0;
        if ((lane_mask & (1u << i)) == 0) continue;
        expected_size = snprintf(expected, sizeof(expected), "HALRESETOK1|%llu|%llu|%llu\n",
            (unsigned long long)l->generation,
            (unsigned long long)l->next_sequence,
            (unsigned long long)invocation);
        if (!read_line_deadline(l->fd_out, l->output, sizeof(l->output), deadline, &n) ||
            n != (size_t)expected_size || memcmp(l->output, expected, n) != 0) {
            l->healthy = 0; return 0;
        }
    }
    for (i = 0; i < 3; ++i) {
        if ((lane_mask & (1u << i)) != 0) {
            if (!write_full(s->lane[i].fd_in, request, request_size)) {
                s->lane[i].healthy = 0; return 0;
            }
        }
    }
    for (i = 0; i < 3; ++i) {
        if ((lane_mask & (1u << i)) == 0) continue;
        if (!read_line_deadline(s->lane[i].fd_out, result[i], HAL_SEALED_FRAME_CAP_V1,
                                deadline, &result_size[i]) ||
            result_size[i] < 8 ||
            (memcmp(result[i], "HALRES1|", 8) != 0 &&
             memcmp(result[i], "HALRES2|", 8) != 0 &&
             (result_size[i] < 9 ||
              memcmp(result[i], "HALRES2B|", 9) != 0))) {
            s->lane[i].healthy = 0; return 0;
        }
    }
    for (i = 0; i < 3; ++i)
        if ((lane_mask & (1u << i)) != 0) s->lane[i].next_sequence++;
    s->completed_invocations++;
    return 1;
}

int hal_sealed_session_invoke_v1(HalSealedSessionV1 *s, uint64_t invocation,
                                 const unsigned char *request, size_t request_size,
                                 unsigned char result[3][HAL_SEALED_FRAME_CAP_V1],
                                 size_t result_size[3]) {
    return hal_sealed_session_invoke_mask_v1(
        s, invocation, 7u, request, request_size, result, result_size);
}

int hal_sealed_session_restart_lane_v1(HalSealedSessionV1 *s, int lane,
                                       const HalSealedSessionConfigV1 *c) {
    if (!s || !c || lane < 0 || lane >= 3 || s->sealed || s->critical_entered) return 0;
    lane_kill(&s->lane[lane]);
    if (!spawn_lane(&s->lane[lane], c->launcher, c->worker[lane], c->deadline_ms)) return 0;
    s->maintenance_restart_count++;
    return 1;
}

int hal_sealed_session_shutdown_v1(HalSealedSessionV1 *s) {
    int i;
    if (!s || s->critical_entered) return 0;
    for (i = 0; i < 3; ++i) lane_kill(&s->lane[i]);
    s->prepared = s->sealed = 0;
    return 1;
}
