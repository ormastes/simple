/* Included by runtime_process_owned.c on Linux only. One broker owns one
 * grouped compiler attempt. The worker enters a fresh memory-capped cgroup
 * atomically in clone3, before its first instruction or execveat. */
#include <linux/magic.h>
#include <linux/memfd.h>
#include <linux/sched.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/statvfs.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#ifndef CGROUP2_SUPER_MAGIC
#define CGROUP2_SUPER_MAGIC 0x63677270
#endif
#ifndef AT_EMPTY_PATH
#define AT_EMPTY_PATH 0x1000
#endif
#ifndef F_ADD_SEALS
#define F_ADD_SEALS 1033
#define F_SEAL_SEAL 0x0001
#define F_SEAL_SHRINK 0x0002
#define F_SEAL_GROW 0x0004
#define F_SEAL_WRITE 0x0008
#endif
extern char **environ;

typedef struct {
    int active, collected, parent_fd, group_fd, pidfd;
    pid_t pid;
    char name[80];
    int64_t started_ms, timeout_ms, peak;
    int leader_reaped, tree_empty, timed_out, cancelled, exit_code;
} RtLinuxGroup;

static RtLinuxGroup rt_linux_group = {0};

static int rt_lg_copy_text(const char *data, uint64_t len, char *out, size_t cap) {
    if (!data || !out || len == 0 || len >= cap || memchr(data, 0, (size_t)len))
        return 0;
    memcpy(out, data, (size_t)len); out[len] = 0; return 1;
}

static int rt_lg_read_fd(int fd, char *out, size_t cap) {
    if (fd < 0 || !out || cap < 2) return 0;
    ssize_t n = read(fd, out, cap - 1);
    if (n <= 0 || (size_t)n >= cap) return 0;
    out[n] = 0; return 1;
}

static int rt_lg_read_at(int dir, const char *name, char *out, size_t cap) {
    int fd = openat(dir, name, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    int ok = rt_lg_read_fd(fd, out, cap);
    close(fd); return ok;
}

static int rt_lg_write_at(int dir, const char *name, const char *data) {
    int fd = openat(dir, name, O_WRONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    size_t size = strlen(data);
    ssize_t written = write(fd, data, size);
    int saved = errno;
    int closed = close(fd);
    if (written != (ssize_t)size || closed != 0) { errno = saved ? saved : EIO; return 0; }
    return 1;
}

static int rt_lg_number(const char *text, int64_t *value) {
    if (!text || !value || !(*text >= '0' && *text <= '9')) return 0;
    uint64_t result = 0;
    const char *p = text;
    for (; *p >= '0' && *p <= '9'; p++) {
        if (result > (uint64_t)INT64_MAX / 10) return 0;
        result = result * 10 + (uint64_t)(*p - '0');
        if (result > INT64_MAX) return 0;
    }
    if (*p != 0 && !(*p == '\n' && p[1] == 0)) return 0;
    *value = (int64_t)result; return 1;
}

static int rt_lg_parent(void) {
    FILE *file = fopen("/proc/self/cgroup", "re");
    if (!file) return -1;
    char line[4096], path[4096]; int found = 0;
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "0::/", 4) == 0) {
            size_t n = strcspn(line + 3, "\r\n");
            if (n == 0 || n > sizeof(path) - 15) break;
            memcpy(path, "/sys/fs/cgroup", 14);
            memcpy(path + 14, line + 3, n); path[14 + n] = 0;
            found = 1; break;
        }
    }
    fclose(file);
    if (!found || strstr(path, "/../") || strstr(path, "/./")) return -1;
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    struct statfs fs;
    if (fd < 0) return -1;
    if (fstatfs(fd, &fs) != 0 || (unsigned long)fs.f_type != CGROUP2_SUPER_MAGIC) {
        close(fd); errno = ENOTSUP; return -1;
    }
    return fd;
}

static int rt_lg_hex_digest(const char *data, uint64_t len, char out[65]) {
    if (!rt_lg_copy_text(data, len, out, 65) || len != 64) return 0;
    for (size_t i = 0; i < 64; i++)
        if (!((out[i] >= '0' && out[i] <= '9') ||
              (out[i] >= 'a' && out[i] <= 'f'))) return 0;
    return 1;
}

static int rt_lg_digest_fd(int fd, const char expected[65]) {
    struct stat before, after;
    if (fd < 0 || fstat(fd, &before) || !S_ISREG(before.st_mode) ||
        before.st_size < 0 || before.st_size > (off_t)1073741824) return 0;
    size_t size = (size_t)before.st_size;
    void *data = size ? mmap(NULL, size, PROT_READ, MAP_PRIVATE, fd, 0) : NULL;
    if (size && data == MAP_FAILED) return 0;
    uint8_t digest[32]; owned_sha256(size ? (const uint8_t*)data : (const uint8_t*)"", size, digest);
    if (size) munmap(data, size);
    if (fstat(fd, &after) || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || before.st_size != after.st_size ||
        before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
        before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
        before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
        before.st_ctim.tv_nsec != after.st_ctim.tv_nsec) return 0;
    static const char digits[] = "0123456789abcdef";
    for (size_t i = 0; i < 32; i++)
        if (expected[i * 2] != digits[digest[i] >> 4] ||
            expected[i * 2 + 1] != digits[digest[i] & 15]) return 0;
    return 1;
}

/* Copy once to a sealed anonymous executable, then hash and execute those
 * exact bytes. A writer changing the original inode after admission cannot
 * change either the broker or compiler worker image. */
static int rt_lg_pin_image(const char *path, const char expected[65]) {
#if !defined(SYS_memfd_create)
    (void)path; (void)expected; errno = ENOTSUP; return -1;
#else
    int source = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (source < 0) return -1;
    struct stat before, after;
    if (fstat(source, &before) != 0 || !S_ISREG(before.st_mode) ||
        before.st_size <= 0 || before.st_size > (off_t)536870912) {
        close(source); errno = EFBIG; return -1;
    }
    int sealed = (int)syscall(SYS_memfd_create, "simple-native-image",
        MFD_CLOEXEC | MFD_ALLOW_SEALING);
    if (sealed < 0) { close(source); return -1; }
    uint8_t buffer[65536]; off_t copied = 0;
    while (copied < before.st_size) {
        size_t want = (size_t)(before.st_size - copied);
        if (want > sizeof(buffer)) want = sizeof(buffer);
        ssize_t got = pread(source, buffer, want, copied);
        if (got < 0 && errno == EINTR) continue;
        if (got <= 0) goto fail;
        ssize_t offset = 0;
        while (offset < got) {
            ssize_t written = write(sealed, buffer + offset, (size_t)(got - offset));
            if (written < 0 && errno == EINTR) continue;
            if (written <= 0) goto fail;
            offset += written;
        }
        copied += got;
    }
    if (fstat(source, &after) != 0 || before.st_dev != after.st_dev ||
        before.st_ino != after.st_ino || before.st_size != after.st_size ||
        before.st_mtim.tv_sec != after.st_mtim.tv_sec ||
        before.st_mtim.tv_nsec != after.st_mtim.tv_nsec ||
        before.st_ctim.tv_sec != after.st_ctim.tv_sec ||
        before.st_ctim.tv_nsec != after.st_ctim.tv_nsec ||
        fchmod(sealed, 0500) != 0 ||
        fcntl(sealed, F_ADD_SEALS,
            F_SEAL_WRITE | F_SEAL_GROW | F_SEAL_SHRINK | F_SEAL_SEAL) != 0 ||
        lseek(sealed, 0, SEEK_SET) < 0 || !rt_lg_digest_fd(sealed, expected))
        goto fail;
    close(source); return sealed;
fail:
    close(source); close(sealed); errno = ESTALE; return -1;
#endif
}

static char **rt_lg_copy_environment(SplArray *values) {
    int64_t count = values ? rt_array_len(values) : -1;
    if (count < 0 || count > 4096) return NULL;
    char **result = calloc((size_t)count + 1, sizeof(char*));
    if (!result) return NULL;
    for (int64_t i = 0; i < count; i++) {
        int64_t item = rt_array_get(values, i);
        int64_t len = rt_string_len(item);
        const uint8_t *data = rt_string_data(item);
        if (!data || len < 3 || len > 65535 || memchr(data, 0, (size_t)len) ||
            !memchr(data, '=', (size_t)len)) goto fail;
        result[i] = malloc((size_t)len + 1);
        if (!result[i]) goto fail;
        memcpy(result[i], data, (size_t)len); result[i][len] = 0;
    }
    return result;
fail:
    for (int64_t i = 0; i < count; i++) free(result[i]);
    free(result); return NULL;
}

static void rt_lg_free_strings(char **items) {
    if (!items) return;
    for (size_t i = 0; items[i]; i++) free(items[i]);
    free(items);
}

static int rt_lg_populated(int fd, int *populated) {
    char events[256];
    if (!rt_lg_read_at(fd, "cgroup.events", events, sizeof(events))) return 0;
    char *line = strstr(events, "populated ");
    if (!line || (line != events && line[-1] != '\n') ||
        (line[10] != '0' && line[10] != '1')) return 0;
    *populated = line[10] == '1'; return 1;
}

static int rt_lg_peak(int fd, int64_t *peak) {
    char data[128];
    return rt_lg_read_at(fd, "memory.peak", data, sizeof(data)) &&
        rt_lg_number(data, peak);
}

static int64_t rt_lg_now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now)) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static int rt_lg_kill(RtLinuxGroup *owner) {
    return rt_lg_write_at(owner->group_fd, "cgroup.kill", "1");
}

static int rt_lg_capacity_capability(int parent) {
#if !defined(SYS_pidfd_open) || !defined(SYS_clone3) || !defined(SYS_execveat)
    (void)parent; errno = ENOTSUP; return 0;
#else
    int pidfd = (int)syscall(SYS_pidfd_open, getpid(), 0);
    if (pidfd < 0) return 0;
    close(pidfd);
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return 0;
    char name[80], value[128];
    snprintf(name, sizeof(name), "simple-native-cap-%ld-%ld-%ld",
        (long)getpid(), (long)now.tv_sec, (long)now.tv_nsec);
    if (mkdirat(parent, name, 0700) != 0) return 0;
    int group = openat(parent, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    int kill_fd = group >= 0 ? openat(group, "cgroup.kill", O_WRONLY | O_CLOEXEC | O_NOFOLLOW) : -1;
    int valid = group >= 0 && kill_fd >= 0 &&
        rt_lg_read_at(group, "memory.max", value, sizeof(value)) &&
        rt_lg_read_at(group, "memory.peak", value, sizeof(value)) &&
        rt_lg_read_at(group, "cgroup.events", value, sizeof(value));
    int saved = errno;
    if (kill_fd >= 0) close(kill_fd);
    if (group >= 0) close(group);
    if (unlinkat(parent, name, AT_REMOVEDIR) != 0) valid = 0;
    if (!valid) errno = saved ? saved : ENOTSUP;
    return valid;
#endif
}

static int rt_lg_poll(RtLinuxGroup *owner) {
    if (!owner->active || owner->collected) return EINVAL;
    int64_t now = rt_lg_now_ms();
    if (now < 0) return EIO;
    if (!owner->timed_out && !owner->leader_reaped &&
        now - owner->started_ms >= owner->timeout_ms) {
        owner->timed_out = 1;
        if (!rt_lg_kill(owner)) return errno ? errno : EIO;
    }
    if (!owner->leader_reaped) {
        int status = 0;
        pid_t observed = waitpid(owner->pid, &status, WNOHANG);
        if (observed < 0) return errno ? errno : ECHILD;
        if (observed == owner->pid) {
            owner->leader_reaped = 1;
            owner->exit_code = WIFEXITED(status) ? WEXITSTATUS(status) :
                (WIFSIGNALED(status) ? 128 + WTERMSIG(status) : 255);
        }
    }
    int populated = 1;
    if (!rt_lg_populated(owner->group_fd, &populated) ||
        !rt_lg_peak(owner->group_fd, &owner->peak)) return EIO;
    if (owner->leader_reaped && populated) {
        if (!rt_lg_kill(owner)) return errno ? errno : EIO;
    }
    owner->tree_empty = owner->leader_reaped && !populated;
    return 0;
}

static SplArray *rt_lg_observation(int error) {
    RtLinuxGroup *o = &rt_linux_group;
    const int64_t values[] = {error, o->leader_reaped && o->tree_empty,
        o->leader_reaped, o->tree_empty, o->tree_empty ? 0 : 1,
        o->exit_code, o->timed_out, o->cancelled, o->peak};
    return owned_adapter_values(values, 9);
}

/* Double-fork leaves the broker independent of manager death. The exact
 * executable inode is opened, hashed, and execveat'd through the same fd. */
SplArray *rt_linux_group_launch_broker_v1(const char *program_data, uint64_t program_len, const char *digest_data, uint64_t digest_len, SplArray *args) {
    int64_t answer[2] = {0, EINVAL};
    char program[4096], expected[65];
    int64_t argc = 0; int copy_error = 0;
    char **argv = NULL;
    int image = -1, pipefd[2] = {-1, -1};
    if (!rt_lg_copy_text(program_data, program_len, program, sizeof(program)) ||
        !rt_lg_hex_digest(digest_data, digest_len, expected) ||
        program[0] != '/') goto done;
    argv = owned_adapter_copy_argv(program_data, program_len, args, &argc, &copy_error);
    if (!argv) { answer[1] = copy_error ? copy_error : EINVAL; goto done; }
    image = rt_lg_pin_image(program, expected);
    if (image < 0) {
        answer[1] = errno ? errno : ESTALE; goto done;
    }
#if defined(SYS_execveat) && defined(SYS_close_range)
    if (pipe(pipefd) != 0 || fcntl(pipefd[0], F_SETFD, FD_CLOEXEC) < 0 ||
        fcntl(pipefd[1], F_SETFD, FD_CLOEXEC) < 0) {
        answer[1] = errno ? errno : EIO; goto done;
    }
    pid_t intermediate = fork();
    if (intermediate == 0) {
        close(pipefd[0]);
        pid_t broker = fork();
        if (broker == 0) {
            close(pipefd[1]);
            if (setsid() < 0) _exit(126);
            int null_fd = open("/dev/null", O_RDWR | O_CLOEXEC);
            if (null_fd < 0 || dup2(null_fd, 0) < 0 || dup2(null_fd, 1) < 0 ||
                dup2(null_fd, 2) < 0 || image < 3) _exit(126);
            if (image != 3 && dup2(image, 3) < 0) _exit(126);
            if (fcntl(3, F_SETFD, FD_CLOEXEC) < 0 ||
                syscall(SYS_close_range, 4U, ~0U, 0U) != 0) _exit(126);
            syscall(SYS_execveat, 3, "", argv, environ, AT_EMPTY_PATH);
            _exit(127);
        }
        if (broker <= 0 || write(pipefd[1], &broker, sizeof(broker)) != sizeof(broker))
            _exit(125);
        _exit(0);
    }
    if (intermediate < 0) { answer[1] = errno; goto done; }
    close(pipefd[1]); pipefd[1] = -1;
    pid_t broker = 0;
    ssize_t bytes = read(pipefd[0], &broker, sizeof(broker));
    int status = 0;
    pid_t reaped = waitpid(intermediate, &status, 0);
    if (bytes != sizeof(broker) || broker <= 0 || reaped != intermediate ||
        !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        answer[1] = ECHILD; goto done;
    }
    answer[0] = broker; answer[1] = 0;
#else
    answer[1] = ENOTSUP;
#endif
done:
    if (pipefd[0] >= 0) close(pipefd[0]);
    if (pipefd[1] >= 0) close(pipefd[1]);
    if (image >= 0) close(image);
    owned_adapter_free_argv(argv, argc);
    return owned_adapter_values(answer, 2);
}

SplArray *rt_linux_group_start_v1(const char *program_data, uint64_t program_len, const char *digest_data, uint64_t digest_len, SplArray *args, SplArray *environment, const char *directory_data, uint64_t directory_len, const char *root_data, uint64_t root_len, const char *identity_data, uint64_t identity_len, int64_t memory_limit, int64_t timeout_ms, const char *stdout_data, uint64_t stdout_len, const char *stderr_data, uint64_t stderr_len) {
    int64_t answer[2] = {0, EINVAL};
    char program[4096], directory[4096], root[4096], stdout_path[4096], stderr_path[4096];
    char expected[65], identity[65], memory_text[64], verify[128];
    int64_t readback = 0;
    char **argv = NULL, **envp = NULL;
    int64_t argc = 0; int copy_error = 0;
    int parent_fd = -1, group_fd = -1, exec_fd = -1, cwd_fd = -1, out_fd = -1, err_fd = -1;
    int created = 0, child_started = 0, pidfd = -1;
    pid_t pid = -1;
    if (rt_linux_group.active || memory_limit < 1 || memory_limit > 1125899906842624LL ||
        timeout_ms < 1 || timeout_ms > 86400000 ||
        !rt_lg_copy_text(program_data, program_len, program, sizeof(program)) ||
        !rt_lg_copy_text(directory_data, directory_len, directory, sizeof(directory)) ||
        !rt_lg_copy_text(root_data, root_len, root, sizeof(root)) ||
        !rt_lg_copy_text(stdout_data, stdout_len, stdout_path, sizeof(stdout_path)) ||
        !rt_lg_copy_text(stderr_data, stderr_len, stderr_path, sizeof(stderr_path)) ||
        !rt_lg_hex_digest(digest_data, digest_len, expected) ||
        !rt_lg_hex_digest(identity_data, identity_len, identity) ||
        program[0] != '/' || directory[0] != '/' || root[0] != '/' ||
        stdout_path[0] != '/' || stderr_path[0] != '/') goto done;
    argv = owned_adapter_copy_argv(program_data, program_len, args, &argc, &copy_error);
    envp = rt_lg_copy_environment(environment);
    if (!argv || !envp) { answer[1] = copy_error ? copy_error : ENOMEM; goto done; }
    exec_fd = rt_lg_pin_image(program, expected);
    cwd_fd = open(directory, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (exec_fd < 0 || cwd_fd < 0) {
        answer[1] = errno ? errno : ESTALE; goto done;
    }
    parent_fd = rt_lg_parent();
    if (parent_fd < 0) { answer[1] = errno ? errno : ENOTSUP; goto done; }
    char name[80]; snprintf(name, sizeof(name), "simple-native-%s", identity);
    if (mkdirat(parent_fd, name, 0700) != 0) { answer[1] = errno; goto done; }
    created = 1;
    group_fd = openat(parent_fd, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (group_fd < 0) { answer[1] = errno; goto done; }
    snprintf(memory_text, sizeof(memory_text), "%lld", (long long)memory_limit);
    if (!rt_lg_write_at(group_fd, "memory.max", memory_text) ||
        !rt_lg_read_at(group_fd, "memory.max", verify, sizeof(verify)) ||
        !rt_lg_number(verify, &readback) || readback != memory_limit ||
        !rt_lg_write_at(group_fd, "memory.swap.max", "0") ||
        !rt_lg_read_at(group_fd, "memory.swap.max", verify, sizeof(verify)) ||
        verify[0] != '0' ||
        !rt_lg_write_at(group_fd, "memory.oom.group", "1") ||
        !rt_lg_read_at(group_fd, "memory.oom.group", verify, sizeof(verify)) ||
        verify[0] != '1' || !rt_lg_read_at(group_fd, "memory.peak", verify, sizeof(verify))) {
        answer[1] = errno ? errno : ENOTSUP; goto done;
    }
    out_fd = open(stdout_path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    err_fd = open(stderr_path, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (out_fd < 0 || err_fd < 0) { answer[1] = errno; goto done; }
#if defined(SYS_clone3) && defined(SYS_execveat) && defined(SYS_close_range)
    struct clone_args clone = {0};
    clone.flags = CLONE_PIDFD | CLONE_INTO_CGROUP;
    clone.pidfd = (uint64_t)(uintptr_t)&pidfd;
    clone.cgroup = (uint64_t)group_fd;
    clone.exit_signal = SIGCHLD;
    pid = (pid_t)syscall(SYS_clone3, &clone, sizeof(clone));
    if (pid == 0) {
        int input_fd = open("/dev/null", O_RDONLY | O_CLOEXEC);
        if (input_fd < 0 || dup2(input_fd, STDIN_FILENO) < 0) _exit(126);
        if (fchdir(cwd_fd) || dup2(out_fd, STDOUT_FILENO) < 0 ||
            dup2(err_fd, STDERR_FILENO) < 0 || exec_fd < 3) _exit(126);
        if (exec_fd != 3 && dup2(exec_fd, 3) < 0) _exit(126);
        if (fcntl(3, F_SETFD, FD_CLOEXEC) < 0) _exit(126);
        if (syscall(SYS_close_range, 4U, ~0U, 0U) != 0) _exit(126);
        syscall(SYS_execveat, 3, "", argv, envp, AT_EMPTY_PATH);
        _exit(127);
    }
#else
    answer[1] = ENOTSUP; goto done;
#endif
    if (pid < 0) { answer[1] = errno ? errno : ENOTSUP; goto done; }
    child_started = 1;
    if (pidfd < 0) { answer[1] = ENOTSUP; goto done; }
    rt_linux_group = (RtLinuxGroup){.active=1, .parent_fd=parent_fd,
        .group_fd=group_fd, .pidfd=pidfd, .pid=pid,
        .started_ms=rt_lg_now_ms(), .timeout_ms=timeout_ms};
    memcpy(rt_linux_group.name, name, strlen(name) + 1);
    if (rt_linux_group.started_ms < 0) {
        answer[1] = EIO; rt_lg_kill(&rt_linux_group); rt_linux_group.active = 0;
        goto done;
    }
    answer[0] = 1; answer[1] = 0;
    parent_fd = group_fd = pidfd = -1; created = 0;
done:
    if (answer[0] == 0 && child_started) {
        if (group_fd >= 0) (void)rt_lg_write_at(group_fd, "cgroup.kill", "1");
        if (pidfd >= 0) close(pidfd);
        if (pid > 0) (void)waitpid(pid, NULL, 0);
    }
    if (out_fd >= 0) close(out_fd);
    if (err_fd >= 0) close(err_fd);
    if (exec_fd >= 0) close(exec_fd);
    if (cwd_fd >= 0) close(cwd_fd);
    if (group_fd >= 0) close(group_fd);
    if (created && parent_fd >= 0) (void)unlinkat(parent_fd, name, AT_REMOVEDIR);
    if (parent_fd >= 0) close(parent_fd);
    owned_adapter_free_argv(argv, argc);
    rt_lg_free_strings(envp);
    return owned_adapter_values(answer, 2);
}

SplArray *rt_linux_group_poll_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active) return rt_lg_observation(EINVAL);
    return rt_lg_observation(rt_lg_poll(&rt_linux_group));
}

int64_t rt_linux_group_cancel_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active || rt_linux_group.collected) return EINVAL;
    rt_linux_group.cancelled = 1;
    return rt_lg_kill(&rt_linux_group) ? 0 : (errno ? errno : EIO);
}

SplArray *rt_linux_group_collect_v1(int64_t token) {
    if (token != 1 || !rt_linux_group.active || rt_linux_group.collected)
        return rt_lg_observation(EINVAL);
    int error = rt_lg_poll(&rt_linux_group);
    if (error) return rt_lg_observation(error);
    if (!rt_linux_group.leader_reaped || !rt_linux_group.tree_empty)
        return rt_lg_observation(EBUSY);
    if (unlinkat(rt_linux_group.parent_fd, rt_linux_group.name, AT_REMOVEDIR) != 0)
        return rt_lg_observation(errno ? errno : EIO);
    close(rt_linux_group.pidfd);
    close(rt_linux_group.group_fd);
    close(rt_linux_group.parent_fd);
    rt_linux_group.collected = 1;
    return rt_lg_observation(0);
}

SplArray *rt_linux_group_available_capacity_v1(const char *path_data, uint64_t path_len) {
    int64_t result[3] = {EINVAL, 0, 0};
    char path[4096], line[256];
    if (!rt_lg_copy_text(path_data, path_len, path, sizeof(path)) || path[0] != '/')
        return owned_adapter_values(result, 3);
    FILE *file = fopen("/proc/meminfo", "re");
    if (!file) { result[0] = errno; return owned_adapter_values(result, 3); }
    int64_t available = 0;
    while (fgets(line, sizeof(line), file)) {
        if (strncmp(line, "MemAvailable:", 13) == 0) {
            long long kb = 0;
            if (sscanf(line, "MemAvailable: %lld kB", &kb) == 1 &&
                kb > 0 && kb <= INT64_MAX / 1024) available = (int64_t)kb * 1024;
            break;
        }
    }
    fclose(file);
    int parent = rt_lg_parent();
    if (parent < 0 || available <= 0) {
        if (parent >= 0) close(parent);
        result[0] = ENOTSUP; return owned_adapter_values(result, 3);
    }
    if (!rt_lg_capacity_capability(parent)) {
        result[0] = errno ? errno : ENOTSUP;
        close(parent); return owned_adapter_values(result, 3);
    }
    char maximum[128], current[128]; int64_t max_bytes = 0, used = 0;
    if (!rt_lg_read_at(parent, "memory.max", maximum, sizeof(maximum)) ||
        !rt_lg_read_at(parent, "memory.current", current, sizeof(current)) ||
        !rt_lg_number(current, &used)) {
        close(parent); result[0] = ENOTSUP; return owned_adapter_values(result, 3);
    }
    close(parent);
    if (strcmp(maximum, "max\n") != 0 && strcmp(maximum, "max") != 0) {
        if (!rt_lg_number(maximum, &max_bytes)) {
            result[0] = EPROTO; return owned_adapter_values(result, 3);
        }
        int64_t headroom = max_bytes > used ? max_bytes - used : 0;
        if (headroom < available) available = headroom;
    }
    struct statvfs volume;
    if (available <= 0 || statvfs(path, &volume) != 0 ||
        volume.f_frsize == 0 || volume.f_bavail > INT64_MAX / volume.f_frsize) {
        result[0] = errno ? errno : ENOSPC; return owned_adapter_values(result, 3);
    }
    result[0] = 0; result[1] = available;
    result[2] = (int64_t)(volume.f_bavail * volume.f_frsize);
    return owned_adapter_values(result, 3);
}
