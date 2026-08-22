/* Trusted rt(hal) provider launcher, ABI v1.
 *
 * This executable is the isolation authority between the Simple coordinator
 * and a Pure/C/Rust provider.  It deliberately has no dynamic allocation and
 * accepts only an absolute worker image.  Linux is the only admitted platform
 * in v1; every other platform fails closed at compile time.
 */
#define _GNU_SOURCE

#if !defined(__linux__)
#error "hal-provider-launcher-v1 requires Linux isolation primitives"
#endif

#include <errno.h>
#include <fcntl.h>
#include <linux/fsverity.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

enum {
    HAL_LAUNCHER_REQUEST_CAP = 4096,
    HAL_LAUNCHER_RESPONSE_CAP = 512,
    HAL_LAUNCHER_ARG_CAP = 128
};

static const char *const HAL_BWRAP_PATH = "/usr/bin/bwrap";
static const char *const HAL_PROVIDER_POLICY_PATH =
    "/usr/libexec/simple/hal-provider-policy-v1";

static int64_t monotonic_ms(void) {
    struct timespec value;
    if (clock_gettime(CLOCK_MONOTONIC, &value) != 0) return -1;
    return (int64_t)value.tv_sec * 1000 + value.tv_nsec / 1000000;
}

static int parse_positive(const char *text, int64_t upper, int64_t *out) {
    char *end = NULL;
    long long value;
    if (!text || !*text) return 0;
    errno = 0;
    value = strtoll(text, &end, 10);
    if (errno || !end || *end || value <= 0 || value > upper) return 0;
    *out = (int64_t)value;
    return 1;
}

static int write_all(int fd, const char *data, size_t size) {
    size_t offset = 0;
    while (offset < size) {
        ssize_t count = write(fd, data + offset, size - offset);
        if (count > 0) {
            offset += (size_t)count;
        } else if (count < 0 && errno == EINTR) {
            continue;
        } else {
            return 0;
        }
    }
    return 1;
}

static int read_request(char *buffer, size_t cap, size_t *size_out,
                        int64_t *invocation_out) {
    size_t size = 0;
    int separators = 0;
    int64_t invocation = 0;
    int invocation_digits = 0;
    while (size + 1 < cap) {
        ssize_t count = read(STDIN_FILENO, buffer + size, 1);
        char ch;
        if (count < 0 && errno == EINTR) continue;
        if (count != 1) return 0;
        ch = buffer[size++];
        if (ch == '\n') break;
        if (ch == '|') {
            separators++;
            continue;
        }
        if (separators == 3) {
            if (ch < '0' || ch > '9') return 0;
            invocation_digits = 1;
            if (invocation > (INT64_MAX - (ch - '0')) / 10) return 0;
            invocation = invocation * 10 + (ch - '0');
        }
    }
    if (size < 2 || buffer[size - 1] != '\n' || !invocation_digits ||
        memcmp(buffer, "HALREQ1|", 8) != 0) return 0;
    buffer[size] = '\0';
    *size_out = size;
    *invocation_out = invocation;
    return 1;
}

static int close_ambient_descriptors(void) {
    /* An incomplete numeric scan would not prove closure when RLIMIT_NOFILE
     * is raised. Linux close_range is one constant-cost, exhaustive kernel
     * transition; an older kernel is therefore unsupported, not best-effort.
     */
    return close_range(3, ~0U, 0) == 0;
}

static int trusted_bwrap_image(void) {
    struct stat value;
    if (lstat(HAL_BWRAP_PATH, &value) != 0) return 0;
    return S_ISREG(value.st_mode) && value.st_uid == 0 &&
        (value.st_mode & (S_IWGRP | S_IWOTH)) == 0;
}

static int parse_u64_text(const char *text, uint64_t *out) {
    char *end = NULL;
    unsigned long long value;
    if (!text || !*text) return 0;
    errno = 0;
    value = strtoull(text, &end, 10);
    if (errno || !end || *end) return 0;
    *out = (uint64_t)value;
    return 1;
}

static int hex_nibble(char value) {
    if (value >= '0' && value <= '9') return value - '0';
    if (value >= 'a' && value <= 'f') return value - 'a' + 10;
    if (value >= 'A' && value <= 'F') return value - 'A' + 10;
    return -1;
}

static int policy_admits_worker(int worker_fd, const char *path,
                                const struct stat *worker_stat) {
    char buffer[4097];
    char *save_line = NULL, *line;
    int policy_fd;
    ssize_t size;
    struct stat policy_stat;
    struct {
        uint16_t digest_algorithm;
        uint16_t digest_size;
        unsigned char digest[64];
    } measured;
    policy_fd = open(HAL_PROVIDER_POLICY_PATH, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (policy_fd < 0 || fstat(policy_fd, &policy_stat) != 0 ||
        !S_ISREG(policy_stat.st_mode) || policy_stat.st_uid != 0 ||
        (policy_stat.st_mode & (S_IWGRP | S_IWOTH)) != 0) {
        if (policy_fd >= 0) close(policy_fd);
        return 0;
    }
    size = read(policy_fd, buffer, sizeof(buffer) - 1);
    close(policy_fd);
    if (size <= 0 || size >= (ssize_t)sizeof(buffer) - 1) return 0;
    buffer[size] = '\0';
    memset(&measured, 0, sizeof(measured));
    measured.digest_size = sizeof(measured.digest);
    if (ioctl(worker_fd, FS_IOC_MEASURE_VERITY, &measured) != 0 ||
        measured.digest_algorithm != FS_VERITY_HASH_ALG_SHA256 ||
        measured.digest_size != 32) return 0;
    line = strtok_r(buffer, "\n", &save_line);
    while (line) {
        char *fields[6];
        char *save_field = NULL;
        int count = 0, index;
        uint64_t device, inode, file_size;
        char *field = strtok_r(line, "|", &save_field);
        while (field && count < 6) {
            fields[count++] = field;
            field = strtok_r(NULL, "|", &save_field);
        }
        if (count == 6 && field == NULL && strcmp(fields[0], "HALPROV1") == 0 &&
            strcmp(fields[1], path) == 0 &&
            parse_u64_text(fields[2], &device) &&
            parse_u64_text(fields[3], &inode) &&
            parse_u64_text(fields[4], &file_size) &&
            device == (uint64_t)worker_stat->st_dev &&
            inode == (uint64_t)worker_stat->st_ino &&
            file_size == (uint64_t)worker_stat->st_size &&
            strlen(fields[5]) == 64) {
            for (index = 0; index < 32; ++index) {
                int hi = hex_nibble(fields[5][index * 2]);
                int lo = hex_nibble(fields[5][index * 2 + 1]);
                if (hi < 0 || lo < 0 ||
                    measured.digest[index] != (unsigned char)((hi << 4) | lo))
                    break;
            }
            if (index == 32) return 1;
        }
        line = strtok_r(NULL, "\n", &save_line);
    }
    return 0;
}

static int trusted_worker_fd(const char *path) {
    struct stat value;
    int fd = open(path, O_PATH | O_NOFOLLOW);
    if (fd < 0) return -1;
    if (fstat(fd, &value) != 0 || !S_ISREG(value.st_mode) ||
        value.st_uid != 0 || (value.st_mode & (S_IWGRP | S_IWOTH)) != 0 ||
        (value.st_mode & (S_IXUSR | S_IXGRP | S_IXOTH)) == 0 ||
        !policy_admits_worker(fd, path, &value)) {
        close(fd);
        return -1;
    }
    return fd;
}

static int read_small_file(const char *path, char *buffer, size_t capacity) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    ssize_t size;
    if (fd < 0) return 0;
    size = read(fd, buffer, capacity - 1);
    close(fd);
    if (size <= 0 || size >= (ssize_t)capacity - 1) return 0;
    buffer[size] = '\0';
    while (size > 0 && (buffer[size - 1] == '\n' || buffer[size - 1] == '\r'))
        buffer[--size] = '\0';
    return 1;
}

static int bounded_cgroup_v2(void) {
    char membership[1024], base[1536], path[1664], value[128];
    char *line, *newline;
    uint64_t limit, quota, period;
    if (!read_small_file("/proc/self/cgroup", membership, sizeof(membership)))
        return 0;
    line = strstr(membership, "0::/");
    if (!line) return 0;
    newline = strchr(line, '\n');
    if (newline) *newline = '\0';
    if (snprintf(base, sizeof(base), "/sys/fs/cgroup%s", line + 3) <= 0)
        return 0;
#define HAL_READ_CONTROL(name) do { \
    if (snprintf(path, sizeof(path), "%s/%s", base, (name)) <= 0 || \
        !read_small_file(path, value, sizeof(value))) return 0; \
} while (0)
    HAL_READ_CONTROL("memory.max");
    if (!parse_u64_text(value, &limit) || limit > 256ULL * 1024ULL * 1024ULL)
        return 0;
    HAL_READ_CONTROL("memory.swap.max");
    if (!parse_u64_text(value, &limit) || limit != 0) return 0;
    HAL_READ_CONTROL("pids.max");
    if (!parse_u64_text(value, &limit) || limit > 32) return 0;
    HAL_READ_CONTROL("cpu.max");
    {
        char *space = strchr(value, ' ');
        if (!space) return 0;
        *space = '\0';
        if (!parse_u64_text(value, &quota) ||
            !parse_u64_text(space + 1, &period) || period == 0 || quota > period)
            return 0;
    }
#undef HAL_READ_CONTROL
    return 1;
}

static int apply_resource_limits(int64_t deadline_ms) {
    struct rlimit limit;
    rlim_t cpu_seconds = (rlim_t)((deadline_ms + 999) / 1000 + 1);
#define HAL_SET_LIMIT(resource, amount) do { \
    limit.rlim_cur = (rlim_t)(amount); \
    limit.rlim_max = (rlim_t)(amount); \
    if (setrlimit((resource), &limit) != 0) return 0; \
} while (0)
    HAL_SET_LIMIT(RLIMIT_AS, 256ULL * 1024ULL * 1024ULL);
    HAL_SET_LIMIT(RLIMIT_NPROC, 32);
    HAL_SET_LIMIT(RLIMIT_CPU, cpu_seconds);
    HAL_SET_LIMIT(RLIMIT_FSIZE, 1024ULL * 1024ULL);
    HAL_SET_LIMIT(RLIMIT_NOFILE, 64);
    HAL_SET_LIMIT(RLIMIT_CORE, 0);
#undef HAL_SET_LIMIT
    return 1;
}

static void worker_exec(int input_fd, int output_fd,
                        char **worker_argv, int worker_argc,
                        int64_t deadline_ms) {
    int null_fd;
    int worker_fd;
    int index = 0, worker_index = 0;
    char *sandbox_argv[HAL_LAUNCHER_ARG_CAP + 32];
    extern char **environ;
    if (dup2(input_fd, STDIN_FILENO) < 0 ||
        dup2(output_fd, STDOUT_FILENO) < 0) _exit(120);
    null_fd = open("/dev/null", O_WRONLY | O_CLOEXEC);
    if (null_fd < 0 || dup2(null_fd, STDERR_FILENO) < 0) _exit(121);
    if (!close_ambient_descriptors()) _exit(122);
    worker_fd = trusted_worker_fd(worker_argv[0]);
    if (worker_fd < 0) _exit(127);
    if (worker_fd != 3) {
        if (dup2(worker_fd, 3) < 0) _exit(127);
        close(worker_fd);
        worker_fd = 3;
    }
    if (clearenv() != 0 || (environ && environ[0] != NULL)) _exit(123);
    if (prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0) _exit(124);
    if (prctl(PR_SET_PDEATHSIG, SIGKILL) != 0 || getppid() == 1) _exit(125);
    if (!apply_resource_limits(deadline_ms)) _exit(128);
    if (!trusted_bwrap_image()) _exit(126);
    sandbox_argv[index++] = (char *)HAL_BWRAP_PATH;
    sandbox_argv[index++] = "--unshare-all";
    sandbox_argv[index++] = "--die-with-parent";
    sandbox_argv[index++] = "--new-session";
    sandbox_argv[index++] = "--clearenv";
    sandbox_argv[index++] = "--preserve-fds";
    sandbox_argv[index++] = "1";
    sandbox_argv[index++] = "--tmpfs";
    sandbox_argv[index++] = "/";
    sandbox_argv[index++] = "--ro-bind";
    sandbox_argv[index++] = "/usr";
    sandbox_argv[index++] = "/usr";
    sandbox_argv[index++] = "--ro-bind-try";
    sandbox_argv[index++] = "/lib";
    sandbox_argv[index++] = "/lib";
    sandbox_argv[index++] = "--ro-bind-try";
    sandbox_argv[index++] = "/lib64";
    sandbox_argv[index++] = "/lib64";
    sandbox_argv[index++] = "--proc";
    sandbox_argv[index++] = "/proc";
    sandbox_argv[index++] = "--tmpfs";
    sandbox_argv[index++] = "/tmp";
    sandbox_argv[index++] = "--chdir";
    sandbox_argv[index++] = "/";
    sandbox_argv[index++] = "--";
    sandbox_argv[index++] = "/proc/self/fd/3";
    worker_index = 1;
    while (worker_index < worker_argc) {
        sandbox_argv[index++] = worker_argv[worker_index++];
    }
    sandbox_argv[index] = NULL;
    execve(HAL_BWRAP_PATH, sandbox_argv, environ);
    _exit(126);
}

static int terminate_and_reap(pid_t child) {
    int status;
    pid_t waited;
    /* The outer worker is a dedicated process-group leader. Bubblewrap also
     * uses --die-with-parent, so killing the supervisor cannot orphan a
     * namespaced descendant. The direct kill is a race-safe fallback. */
    if (kill(-child, SIGKILL) != 0 && errno != ESRCH) return 0;
    if (kill(child, SIGKILL) != 0 && errno != ESRCH) return 0;
    do {
        waited = waitpid(child, &status, 0);
    } while (waited < 0 && errno == EINTR);
    return waited == child;
}

static int read_line_timed(int fd, char *buffer, size_t cap,
                           int64_t deadline_ms, size_t *size_out) {
    size_t size = 0;
    int64_t start = monotonic_ms();
    if (start < 0) return 0;
    while (size + 1 < cap) {
        struct pollfd descriptor = {.fd = fd, .events = POLLIN | POLLHUP,
                                    .revents = 0};
        int64_t now = monotonic_ms();
        int ready;
        if (now < 0 || now - start >= deadline_ms) return 0;
        ready = poll(&descriptor, 1, (int)(deadline_ms - (now - start)));
        if (ready < 0 && errno == EINTR) continue;
        if (ready <= 0) return 0;
        {
            ssize_t count = read(fd, buffer + size, 1);
            if (count == 1) {
                if (buffer[size++] == '\n') {
                    buffer[size] = '\0';
                    *size_out = size;
                    return 1;
                }
            } else if (count < 0 && errno == EINTR) {
                continue;
            } else {
                return 0;
            }
        }
    }
    return 0;
}

static int session_main(int argc, char **argv) {
    char parent_line[HAL_LAUNCHER_REQUEST_CAP];
    char worker_line[HAL_LAUNCHER_REQUEST_CAP];
    char isolation[192];
    int to_child[2] = {-1, -1}, from_child[2] = {-1, -1};
    int64_t deadline_ms = 0, response_cap = 0;
    pid_t child;
    size_t parent_size = 0, worker_size = 0;
    int status = 0;
    if (argc < 5 || argc > HAL_LAUNCHER_ARG_CAP || argv[4][0] != '/' ||
        !trusted_bwrap_image() || !bounded_cgroup_v2() ||
        !parse_positive(argv[2], 3600000, &deadline_ms) ||
        !parse_positive(argv[3], HAL_LAUNCHER_RESPONSE_CAP, &response_cap) ||
        pipe2(to_child, O_CLOEXEC) != 0 || pipe2(from_child, O_CLOEXEC) != 0)
        return 74;
    child = fork();
    if (child < 0) return 75;
    if (child == 0) {
        if (setpgid(0, 0) != 0) _exit(119);
        worker_exec(to_child[0], from_child[1], &argv[4], argc - 4,
                    deadline_ms);
    }
    if (setpgid(child, child) != 0 && errno != EACCES) {
        terminate_and_reap(child); return 75;
    }
    close(to_child[0]); close(from_child[1]);
    if (!read_line_timed(from_child[0], worker_line, sizeof(worker_line),
                         deadline_ms, &worker_size) ||
        worker_size != 11 || memcmp(worker_line, "HALWORKER1\n", 11) != 0) {
        terminate_and_reap(child); return 76;
    }
    {
        int count = snprintf(isolation, sizeof(isolation),
            "HALSESSION1|%ld|0|0|0|1|1\n", (long)child);
        if (count <= 0 || (size_t)count >= sizeof(isolation) ||
            !write_all(STDOUT_FILENO, isolation, (size_t)count)) {
            terminate_and_reap(child); return 77;
        }
    }
    for (;;) {
        if (!read_line_timed(STDIN_FILENO, parent_line, sizeof(parent_line),
                             deadline_ms, &parent_size)) break;
        if (parent_size < 12 || memcmp(parent_line, "HALRESET1|", 10) != 0 ||
            !write_all(to_child[1], parent_line, parent_size) ||
            !read_line_timed(from_child[0], worker_line, sizeof(worker_line),
                             deadline_ms, &worker_size) ||
            worker_size < 14 || memcmp(worker_line, "HALRESETOK1|", 12) != 0 ||
            !write_all(STDOUT_FILENO, worker_line, worker_size)) break;
        if (!read_line_timed(STDIN_FILENO, parent_line, sizeof(parent_line),
                             deadline_ms, &parent_size) ||
            parent_size < 9 || memcmp(parent_line, "HALREQ1|", 8) != 0 ||
            !write_all(to_child[1], parent_line, parent_size) ||
            !read_line_timed(from_child[0], worker_line,
                             (size_t)response_cap + 1, deadline_ms,
                             &worker_size) ||
            worker_size < 9 || memcmp(worker_line, "HALRES1|", 8) != 0 ||
            !write_all(STDOUT_FILENO, worker_line, worker_size)) break;
    }
    terminate_and_reap(child);
    while (waitpid(child, &status, WNOHANG) < 0 && errno == EINTR) { }
    return 78;
}

int main(int argc, char **argv) {
    char request[HAL_LAUNCHER_REQUEST_CAP];
    char response[HAL_LAUNCHER_RESPONSE_CAP + 1];
    char isolation[192];
    int to_child[2] = {-1, -1};
    int from_child[2] = {-1, -1};
    size_t request_size = 0, response_size = 0;
    int64_t invocation = 0, deadline_ms = 0, response_cap = 0, start_ms;
    pid_t child;
    int status = 0, reaped = 0;

    if (argc >= 2 && strcmp(argv[1], "--session") == 0)
        return session_main(argc, argv);
    if (argc < 4 || argc > HAL_LAUNCHER_ARG_CAP || argv[3][0] != '/' ||
        !trusted_bwrap_image() ||
        !parse_positive(argv[1], 3600000, &deadline_ms) ||
        !parse_positive(argv[2], HAL_LAUNCHER_RESPONSE_CAP, &response_cap) ||
        !read_request(request, sizeof(request), &request_size, &invocation)) return 64;
    if (pipe2(to_child, O_CLOEXEC) != 0 || pipe2(from_child, O_CLOEXEC) != 0)
        return 65;
    child = fork();
    if (child < 0) return 66;
    if (child == 0) {
        if (setpgid(0, 0) != 0) _exit(119);
        worker_exec(to_child[0], from_child[1], &argv[3], argc - 3,
                    deadline_ms);
    }
    if (setpgid(child, child) != 0 && errno != EACCES) {
        terminate_and_reap(child);
        return 66;
    }
    close(to_child[0]);
    close(from_child[1]);
    if (!write_all(to_child[1], request, request_size) || close(to_child[1])) {
        terminate_and_reap(child);
        return 67;
    }
    to_child[1] = -1;
    start_ms = monotonic_ms();
    if (start_ms < 0) {
        terminate_and_reap(child);
        return 68;
    }
    for (;;) {
        struct pollfd descriptor;
        int64_t now = monotonic_ms();
        int remaining;
        int poll_status;
        ssize_t count;
        pid_t waited;
        if (now < 0 || now - start_ms >= deadline_ms) {
            terminate_and_reap(child);
            return 69;
        }
        remaining = (int)(deadline_ms - (now - start_ms));
        descriptor.fd = from_child[0];
        descriptor.events = POLLIN | POLLHUP;
        descriptor.revents = 0;
        poll_status = poll(&descriptor, 1, remaining);
        if (poll_status < 0 && errno == EINTR) continue;
        if (poll_status <= 0) {
            terminate_and_reap(child);
            return 69;
        }
        count = read(from_child[0], response + response_size,
                     (size_t)response_cap + 1 - response_size);
        if (count > 0) {
            response_size += (size_t)count;
            if (response_size > (size_t)response_cap) {
                terminate_and_reap(child);
                return 70;
            }
            continue;
        }
        if (count < 0 && errno == EINTR) continue;
        if (count < 0) {
            terminate_and_reap(child);
            return 71;
        }
        close(from_child[0]);
        from_child[0] = -1;
        /* EOF is not terminal proof: a hostile worker can close stdout and
         * remain alive. Keep the same absolute deadline while waiting and
         * never enter an unbounded blocking wait here. */
        for (;;) {
            const struct timespec pause = {.tv_sec = 0, .tv_nsec = 1000000};
            do {
                waited = waitpid(child, &status, WNOHANG);
            } while (waited < 0 && errno == EINTR);
            if (waited == child) {
                reaped = 1;
                break;
            }
            now = monotonic_ms();
            if (waited < 0 || now < 0 || now - start_ms >= deadline_ms) {
                terminate_and_reap(child);
                return 69;
            }
            nanosleep(&pause, NULL);
        }
        break;
    }
    if (!reaped || !WIFEXITED(status) || WEXITSTATUS(status) != 0 ||
        response_size < 2 || response[response_size - 1] != '\n' ||
        memchr(response, '\n', response_size - 1) != NULL) return 72;
    response[response_size] = '\0';
    {
        int count = snprintf(isolation, sizeof(isolation),
            "HALISO1|%lld|%ld|0|0|0|1|1\n",
            (long long)invocation, (long)child);
        if (count <= 0 || (size_t)count >= sizeof(isolation) ||
            !write_all(STDOUT_FILENO, isolation, (size_t)count) ||
            !write_all(STDOUT_FILENO, response, response_size)) return 73;
    }
    return 0;
}
