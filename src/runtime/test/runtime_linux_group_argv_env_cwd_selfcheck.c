/* Real-runtime Linux cgroup V2 process-owner ABI probe.
 * The parent uses the production runtime arrays, strings, sealed image path,
 * cgroup owner, and process lifecycle. The same ELF is its checked child. */
#define _GNU_SOURCE
#include "runtime.h"
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <time.h>
#include <unistd.h>
#include <openssl/sha.h>

extern char **environ;

extern SplArray *rt_linux_group_parent_acquire_at_v2(const char *, uint64_t,
    const char *, uint64_t, const char *, uint64_t);
extern int64_t rt_linux_group_parent_release_v1(int64_t);
extern SplArray *rt_linux_group_start_v1(const char *, uint64_t, const char *, uint64_t,
    SplArray *, SplArray *, const char *, uint64_t, const char *, uint64_t,
    const char *, uint64_t, int64_t, int64_t, const char *, uint64_t,
    const char *, uint64_t);
extern SplArray *rt_linux_group_poll_v1(int64_t);
extern int64_t rt_linux_group_cancel_v1(int64_t);
extern SplArray *rt_linux_group_collect_v1(int64_t);

static int64_t field(SplArray *array, int64_t index) {
    if (!array || index < 0 || index >= rt_array_len(array)) return INT64_MIN;
    return rt_value_unbox_int(rt_array_get(array, index));
}

static int push_text(SplArray *array, const char *text) {
    int64_t value = rt_string_new((const uint8_t *)text, strlen(text));
    return value != 0 && rt_array_push(array, value);
}

static int add_env(SplArray *array, const char *key, const char *value) {
    char item[PATH_MAX * 2];
    int n = snprintf(item, sizeof(item), "%s=%s", key, value);
    return n > 0 && (size_t)n < sizeof(item) && push_text(array, item);
}

static int read_file(const char *path, char *out, size_t cap) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    size_t used = 0;
    while (used + 1 < cap) {
        ssize_t n = read(fd, out + used, cap - used - 1);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { close(fd); return 0; }
        if (n == 0) break;
        used += (size_t)n;
    }
    close(fd);
    if (used + 1 >= cap) return 0;
    out[used] = 0;
    return 1;
}

static int write_all(int fd, const char *data, size_t len) {
    size_t off = 0;
    while (off < len) {
        ssize_t n = write(fd, data + off, len - off);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) return 0;
        off += (size_t)n;
    }
    return 1;
}

static int contains_word(const char *list, const char *word) {
    size_t wanted = strlen(word);
    const char *at = list;
    while (*at) {
        at += strspn(at, " \t\r\n");
        size_t n = strcspn(at, " \t\r\n");
        if (n == wanted && memcmp(at, word, n) == 0) return 1;
        at += n;
    }
    return 0;
}

static int only_expected_controllers(const char *text) {
    int memory = 0, pids = 0;
    const char *at = text;
    while (*at) {
        at += strspn(at, " \t\r\n");
        size_t n = strcspn(at, " \t\r\n");
        if (!n) break;
        if (n == 6 && memcmp(at, "memory", 6) == 0) memory++;
        else if (n == 4 && memcmp(at, "pids", 4) == 0) pids++;
        else return 0;
        at += n;
    }
    return memory == 1 && pids == 1;
}

static int current_service_parent(char *delegated, size_t cap,
        const char *expected_unit) {
    char proc[PATH_MAX];
    if (!read_file("/proc/self/cgroup", proc, sizeof(proc))) return 0;
    char *line = proc, *next;
    char member[PATH_MAX] = {0};
    int unified = 0;
    while (line && *line) {
        next = strchr(line, '\n');
        if (next) *next++ = 0;
        if (strncmp(line, "0::", 3) == 0) {
            if (unified++ || line[3] != '/') return 0;
            if (strlen(line + 3) >= sizeof(member)) return 0;
            strcpy(member, line + 3);
        }
        line = next;
    }
    static const char suffix[] = "/supervisor";
    size_t len = strlen(member), suffix_len = sizeof(suffix) - 1;
    if (unified != 1 || len <= suffix_len ||
        strcmp(member + len - suffix_len, suffix) != 0) return 0;
    member[len - suffix_len] = 0;
    const char *base = strrchr(member, '/'); base = base ? base + 1 : member;
    size_t base_len = strlen(base);
    if (!expected_unit || strcmp(base, expected_unit) != 0 ||
        strncmp(base, "simple-linux-parent-v2-", 23) != 0 || base_len < 8 ||
        strcmp(base + base_len - 8, ".service") != 0) return 0;
    if (snprintf(delegated, cap, "/sys/fs/cgroup%s", member) >= (int)cap) return 0;
    struct statfs fs;
    return statfs(delegated, &fs) == 0 && (unsigned long)fs.f_type == 0x63677270UL;
}

static int setup_service_parent(const char *path, const char *expected_unit,
        int *parent_fd_out, char controls_after[PATH_MAX]) {
    const char *base = strrchr(path, '/'); base = base ? base + 1 : path;
    if (strcmp(base, expected_unit) != 0) return 0;
    int parent = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (parent < 0) return 0;
    char procs[PATH_MAX], available[PATH_MAX], before[PATH_MAX];
    int pfd = openat(parent, "cgroup.procs", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (pfd < 0) { close(parent); return 0; }
    ssize_t pn = read(pfd, procs, sizeof(procs) - 1); close(pfd);
    if (pn < 0 || (size_t)pn >= sizeof(procs) - 1) { close(parent); return 0; }
    procs[pn] = 0;
    if (strspn(procs, " \t\r\n") != strlen(procs)) { close(parent); return 0; }
    pfd = openat(parent, "cgroup.controllers", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (pfd < 0) { close(parent); return 0; }
    ssize_t an = read(pfd, available, sizeof(available) - 1); close(pfd);
    if (an < 0 || (size_t)an >= sizeof(available) - 1) { close(parent); return 0; }
    available[an] = 0;
    if (!contains_word(available, "memory") || !contains_word(available, "pids")) {
        close(parent); return 0;
    }
    pfd = openat(parent, "cgroup.subtree_control", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (pfd < 0) { close(parent); return 0; }
    ssize_t bn = read(pfd, before, sizeof(before) - 1); close(pfd);
    if (bn < 0 || (size_t)bn >= sizeof(before) - 1) { close(parent); return 0; }
    before[bn] = 0;
    if (strspn(before, " \t\r\n") != strlen(before)) { close(parent); return 0; }
    pfd = openat(parent, "cgroup.subtree_control", O_WRONLY | O_CLOEXEC | O_NOFOLLOW);
    if (pfd < 0) { close(parent); return 0; }
    int wrote = write_all(pfd, "+memory +pids", 13); close(pfd);
    if (!wrote) { close(parent); return 0; }
    pfd = openat(parent, "cgroup.subtree_control", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (pfd < 0) { close(parent); return 0; }
    ssize_t cn = read(pfd, controls_after, PATH_MAX - 1); close(pfd);
    if (cn < 0 || cn >= PATH_MAX - 1) { close(parent); return 0; }
    controls_after[cn] = 0;
    if (!only_expected_controllers(controls_after)) { close(parent); return 0; }
    *parent_fd_out = parent;
    printf("SERVICE_SETUP_PASS: unit=%s parent_procs_empty=true controllers=%s\n",
        expected_unit, controls_after); fflush(stdout);
    return 1;
}

static int digest_file(const char *path, char out[65]) {
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    SHA256_CTX ctx;
    if (SHA256_Init(&ctx) != 1) { close(fd); return 0; }
    uint8_t buf[16384], digest[SHA256_DIGEST_LENGTH];
    for (;;) {
        ssize_t n = read(fd, buf, sizeof(buf));
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) { close(fd); return 0; }
        if (!n) break;
        if (SHA256_Update(&ctx, buf, (size_t)n) != 1) { close(fd); return 0; }
    }
    close(fd);
    if (SHA256_Final(digest, &ctx) != 1) return 0;
    for (size_t i = 0; i < sizeof(digest); i++) sprintf(out + i * 2, "%02x", digest[i]);
    out[64] = 0;
    return 1;
}

static int absent_at(int dir, const char *name) {
    struct stat st;
    errno = 0;
    return fstatat(dir, name, &st, AT_SYMLINK_NOFOLLOW) < 0 && errno == ENOENT;
}

static int child_mode(int argc, char **argv) {
    static const char *expected_args[] = {
        "argument with spaces", "", "-leading", "utf8-\xE4\xB8\xad"
    };
    char executable[PATH_MAX], actual[PATH_MAX], cwd[PATH_MAX];
    ssize_t exe_len = readlink("/proc/self/exe", executable, sizeof(executable) - 1);
    if (exe_len < 0 || (size_t)exe_len >= sizeof(executable) - 1) return 21;
    executable[exe_len] = 0;
    const char *expected_argv0 = getenv("PROBE_ARGV0");
    if (argc != 5 || !expected_argv0 || strcmp(argv[0], expected_argv0) != 0) return 22;
    for (int i = 0; i < 4; i++) if (strcmp(argv[i + 1], expected_args[i]) != 0) return 23 + i;
    const char *want_cwd = getenv("PROBE_CWD");
    const char *marker = getenv("PROBE_MARKER");
    if (!want_cwd || !marker || !getenv("PROBE_EXPECT") ||
        strcmp(getenv("PROBE_EXPECT"), "owner-v2") != 0 ||
        strcmp(getenv("PROBE_MODE") ? getenv("PROBE_MODE") : "", "child") != 0 ||
        getenv("SIMPLE_OWNER_INHERIT_SENTINEL")) return 30;
    int env_count = 0;
    for (char **item = environ; item && *item; item++) {
        env_count++;
        if (strncmp(*item, "PROBE_CWD=", 10) != 0 &&
            strncmp(*item, "PROBE_MARKER=", 13) != 0 &&
        strncmp(*item, "PROBE_ARGV0=", 12) != 0 &&
            strcmp(*item, "PROBE_EXPECT=owner-v2") != 0 &&
            strcmp(*item, "PROBE_MODE=child") != 0) return 31;
    }
    if (env_count != 5 || !getcwd(cwd, sizeof(cwd)) || strcmp(cwd, want_cwd) != 0) return 32;
    if (snprintf(actual, sizeof(actual), "%s/marker", cwd) >= (int)sizeof(actual) ||
        strcmp(actual, marker) != 0) return 33;
    static const char receipt[] = "argv-env-cwd-pass\n";
    int fd = open(marker, O_WRONLY | O_CREAT | O_EXCL | O_CLOEXEC | O_NOFOLLOW, 0600);
    if (fd < 0) return 34;
    int ok = write_all(fd, receipt, sizeof(receipt) - 1) && fsync(fd) == 0;
    if (close(fd) != 0) ok = 0;
    return ok ? 0 : 35;
}

static int fresh_evidence(const char *path) {
    char canonical[PATH_MAX];
    struct stat st;
    if (!realpath(path, canonical) || strcmp(path, canonical) != 0 ||
        strcmp(path, "/") == 0 || stat(path, &st) != 0 || !S_ISDIR(st.st_mode) ||
        st.st_uid != geteuid() || (st.st_mode & 0077) != 0 || (st.st_mode & 0700) != 0700)
        return 0;
    int dir = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (dir < 0) return 0;
    const char *files[] = {"argv.stdout", "argv.stderr", "child-cwd"};
    for (size_t i = 0; i < sizeof(files) / sizeof(files[0]); i++) {
        struct stat child;
        if (fstatat(dir, files[i], &child, AT_SYMLINK_NOFOLLOW) == 0 || errno != ENOENT) {
            close(dir); return 0;
        }
    }
    close(dir);
    return 1;
}

static int64_t monotonic_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

static int marker_matches(const char *path) {
    char actual[128];
    int fd = open(path, O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    ssize_t n = read(fd, actual, sizeof(actual));
    int extra = 0;
    if (n == (ssize_t)(sizeof("argv-env-cwd-pass\n") - 1)) {
        char byte;
        extra = read(fd, &byte, 1) != 0;
    }
    close(fd);
    return n == (ssize_t)(sizeof("argv-env-cwd-pass\n") - 1) && !extra &&
        memcmp(actual, "argv-env-cwd-pass\n", sizeof("argv-env-cwd-pass\n") - 1) == 0;
}

static int release_parent(int service_parent, int64_t token, const char *identity,
        const char *controls_after_setup) {
    char name[80], controls_after[PATH_MAX];
    if (snprintf(name, sizeof(name), "simple-parent-%s", identity) >= (int)sizeof(name)) return 79;
    if (rt_linux_group_parent_release_v1(token) != 0 || !absent_at(service_parent, name)) return 79;
    int fd = openat(service_parent, "cgroup.subtree_control", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 79;
    ssize_t n = read(fd, controls_after, sizeof(controls_after) - 1); close(fd);
    if (n < 0 || n >= (ssize_t)sizeof(controls_after) - 1) return 79;
    controls_after[n] = 0;
    return strcmp(controls_after, controls_after_setup) == 0 ? 0 : 79;
}

static int open_admitted_parent(int service_parent, const char *identity,
        int64_t expected_device, int64_t expected_inode) {
    char name[80];
    if (snprintf(name, sizeof(name), "simple-parent-%s", identity) >= (int)sizeof(name)) return -1;
    int fd = openat(service_parent, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return -1;
    struct stat st;
    if (fstat(fd, &st) != 0 || (int64_t)st.st_dev != expected_device ||
        (int64_t)st.st_ino != expected_inode) { close(fd); return -1; }
    return fd;
}

static int open_absent_in_evidence(const char *path, const char *name) {
    int fd = open(path, O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0) return 0;
    int absent = absent_at(fd, name);
    close(fd);
    return absent;
}

static int v2_argv_env_cwd_probe(const char *unit, const char *evidence, const char *argv0) {
    if (!fresh_evidence(evidence)) {
        fprintf(stderr, "PROCESS_SETUP_FAIL: evidence directory is not canonical, private, and fresh\n");
        return 1;
    }
    char delegated[PATH_MAX], cwd[PATH_MAX], marker[PATH_MAX], executable[PATH_MAX];
    char controls_after_setup[PATH_MAX];
    int service_parent = -1;
    if (!current_service_parent(delegated, sizeof(delegated), unit) ||
        !setup_service_parent(delegated, unit, &service_parent, controls_after_setup)) {
        fprintf(stderr, "PROCESS_SETUP_FAIL: service parent membership/controllers not verified errno=%d\n", errno);
        return 1;
    }
    printf("V2_DELEGATED_PATH=%s\n", delegated); fflush(stdout);
    if (snprintf(cwd, sizeof(cwd), "%s/child-cwd", evidence) >= (int)sizeof(cwd) ||
        snprintf(marker, sizeof(marker), "%s/marker", cwd) >= (int)sizeof(marker) ||
        mkdir(cwd, 0700) != 0 || !realpath(argv0, executable)) {
        close(service_parent);
        fprintf(stderr, "PROCESS_SETUP_FAIL: child paths or executable unavailable errno=%d\n", errno);
        return 1;
    }
    if (setenv("SIMPLE_OWNER_INHERIT_SENTINEL", "parent-only-secret", 1) != 0) {
        close(service_parent); return 1;
    }
    char identity[65], digest[65];
    uint8_t identity_bytes[SHA256_DIGEST_LENGTH];
    if (!SHA256((const uint8_t *)unit, strlen(unit), identity_bytes)) {
        close(service_parent); return 1;
    }
    for (int i = 0; i < SHA256_DIGEST_LENGTH; i++) sprintf(identity + i * 2, "%02x", (uint8_t)identity_bytes[i]);
    identity[64] = 0;
    if (!digest_file(executable, digest)) { close(service_parent); return 1; }
    const char *attempt = "/tmp/simple-linux-parent-v2-argv-env-cwd";
    SplArray *admission = rt_linux_group_parent_acquire_at_v2(delegated, strlen(delegated),
        attempt, strlen(attempt), identity, 64);
    if (!admission || rt_array_len(admission) != 4) {
        close(service_parent); return 79;
    }
    int64_t admission_status = field(admission, 0), parent_token = field(admission, 1);
    int64_t parent_device = field(admission, 2), parent_inode = field(admission, 3);
    if (parent_token < 0) { close(service_parent); return 79; }
    if (admission_status != 0 || parent_token == 0 || parent_device < 0 || parent_inode <= 0) {
        int cleanup = 0;
        if (parent_token > 0)
            cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
        else if (parent_token == 0 && admission_status != 0 && parent_device == 0 && parent_inode == 0)
            cleanup = 0;
        else cleanup = 79;
        fprintf(stderr, "PARENT_ADMISSION_FAIL: status=%lld token=%lld\n",
            (long long)admission_status, (long long)parent_token);
        close(service_parent);
        if (cleanup) { puts("PARENT_ADMISSION_CLEANUP_PENDING"); return 79; }
        return 1;
    }
    printf("PARENT_ADMISSION_PASS: token=%lld path=%s\n", (long long)parent_token, delegated);
    fflush(stdout);
    int child_parent = open_admitted_parent(service_parent, identity,
        field(admission, 2), field(admission, 3));
    if (child_parent < 0) {
        int cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
        close(service_parent);
        return cleanup ? 79 : 1;
    }

    SplArray *args = rt_array_new(4), *environment = rt_array_new(5);
    if (!args || !environment || !push_text(args, "argument with spaces") ||
        !push_text(args, "") || !push_text(args, "-leading") ||
        !push_text(args, "utf8-\xE4\xB8\xAD") ||
        !add_env(environment, "PROBE_MODE", "child") ||
        !add_env(environment, "PROBE_EXPECT", "owner-v2") ||
        !add_env(environment, "PROBE_CWD", cwd) ||
        !add_env(environment, "PROBE_MARKER", marker) ||
        !add_env(environment, "PROBE_ARGV0", executable)) {
        close(child_parent);
        int cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
        close(service_parent); return cleanup ? 79 : 1;
    }
    char stdout_path[PATH_MAX], stderr_path[PATH_MAX];
    if (snprintf(stdout_path, sizeof(stdout_path), "%s/argv.stdout", evidence) >= (int)sizeof(stdout_path) ||
        snprintf(stderr_path, sizeof(stderr_path), "%s/argv.stderr", evidence) >= (int)sizeof(stderr_path) ||
        !open_absent_in_evidence(evidence, "argv.stdout") ||
        !open_absent_in_evidence(evidence, "argv.stderr")) {
        close(child_parent);
        int cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
        close(service_parent); return cleanup ? 79 : 1;
    }
    SplArray *started = rt_linux_group_start_v1(executable, strlen(executable), digest, 64,
        args, environment, cwd, strlen(cwd), attempt, strlen(attempt), identity, 64,
        33554432, 5000, stdout_path, strlen(stdout_path), stderr_path, strlen(stderr_path));
    rt_array_free(args); rt_array_free(environment);
    int64_t start_token = field(started, 0), start_status = field(started, 1);
    char child_group[80]; snprintf(child_group, sizeof(child_group), "simple-native-%s", identity);
    if (!started || rt_array_len(started) != 2 || start_token != 1 || start_status != 0) {
        if (!started || start_token != 0 || start_status == 0 ||
            !absent_at(child_parent, child_group)) {
            close(child_parent);
            close(service_parent); return 79;
        }
        close(child_parent);
        int cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
        close(service_parent);
        if (cleanup) return 79;
        if (start_status == ENOSYS) { puts("PROCESS_UNSUPPORTED: clone3 ENOSYS"); return 77; }
        if (start_status == EPERM) { puts("PROCESS_POLICY_BLOCKED: clone3 EPERM"); return 78; }
        fprintf(stderr, "PROCESS_START_FAIL: status=%lld\n", (long long)start_status);
        return 1;
    }
    int64_t start = monotonic_ms();
    int terminal = 0, timed_out = 0, clock_failure = start < 0, poll_error = 0;
    SplArray *observed = NULL;
    for (int i = 0; i < 1000 && !terminal && !clock_failure; i++) {
        int64_t now = monotonic_ms();
        if (now < 0) { clock_failure = 1; break; }
        if (now - start >= 10000) { timed_out = 1; break; }
        observed = rt_linux_group_poll_v1(start_token);
        if (!observed || rt_array_len(observed) != 10) { poll_error = EPROTO; break; }
        if (field(observed, 0) != 0) { poll_error = (int)field(observed, 0); break; }
        terminal = field(observed, 1) == 1;
        if (!terminal) usleep(10000);
    }
    if (!terminal) {
        int64_t cancel = rt_linux_group_cancel_v1(start_token);
        fprintf(stderr, "PROCESS_DRAIN: deadline=%d clock_failure=%d cancel=%lld\n",
            timed_out, clock_failure, (long long)cancel);
        int64_t drain = monotonic_ms();
        for (int i = 0; i < 1000; i++) {
            if (drain >= 0 && !clock_failure) {
                int64_t now = monotonic_ms();
                if (now < 0) clock_failure = 1;
                else if (now - drain >= 10000) break;
            }
            observed = rt_linux_group_poll_v1(start_token);
            if (observed && rt_array_len(observed) == 10 && field(observed, 0) == 0 &&
                field(observed, 1) == 1) { terminal = 1; break; }
            usleep(10000);
        }
    }
    if (!terminal) { close(child_parent); close(service_parent); puts("PROCESS_CLEANUP_PENDING: terminal state unknown"); return 79; }
    int process_ok = !timed_out && !clock_failure && !poll_error && field(observed, 2) == 1 &&
        field(observed, 3) == 1 && field(observed, 4) == 0 && field(observed, 5) == 0 &&
        field(observed, 6) == 0 && field(observed, 7) == 0;
    SplArray *collected = rt_linux_group_collect_v1(start_token);
    if (!collected || rt_array_len(collected) != 10 || field(collected, 0) != 0 ||
        field(collected, 1) != 1 || field(collected, 2) != 1 || field(collected, 3) != 1 ||
        field(collected, 4) != 0 || !absent_at(child_parent, child_group)) {
        close(child_parent); close(service_parent); puts("PROCESS_CLEANUP_PENDING: collect/reap/tree removal unknown"); return 79;
    }
    int marker_ok = marker_matches(marker);
    close(child_parent);
    int cleanup = release_parent(service_parent, parent_token, identity, controls_after_setup);
    close(service_parent);
    if (cleanup) { puts("PROCESS_CLEANUP_PENDING: parent release/controller readback unknown"); return 79; }
    if (!process_ok || !marker_ok) {
        printf("PROCESS_FAIL: timeout=%d clock_failure=%d poll_error=%d marker_exact=%d exit=%lld\n",
            timed_out, clock_failure, poll_error, marker_ok, (long long)field(observed, 5));
        return 1;
    }
    printf("PROCESS_PASS: sealed_sha256=%s argv_exact=true env_allowlist=true inherited_sentinel_absent=true cwd_exact=true marker_exact=true exit=0 reaped=true tree_empty=true parent_released=true\n", digest);
    return 0;
}

int main(int argc, char **argv) {
    __simple_runtime_init();
    if (argc == 5 && strcmp(argv[1], "argument with spaces") == 0)
        return child_mode(argc, argv);
    if (argc == 4 && strcmp(argv[1], "v2-argv-env-cwd") == 0)
        return v2_argv_env_cwd_probe(argv[2], argv[3], argv[0]);
    fprintf(stderr, "usage: %s v2-argv-env-cwd <exact-unit.service> <private-evidence-dir>\n", argv[0]);
    return 2;
}

