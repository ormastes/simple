/* Reuse the existing adapter fixture and the production cgroup implementation.
 * This is live C host evidence, not Simple ABI or BuildRunner admission. */
#define main linux_capacity_baseline_main
#include "linux_capacity_owner.c"
#undef main
#include <poll.h>
#include <signal.h>
#include <sys/prctl.h>

static int64_t oom_kills(void) {
    char events[2048];
    assert(rt_lg_read_at(rt_linux_group.group_fd, "memory.events", events, sizeof(events)));
    char *line = events;
    while (*line) {
        if (!strncmp(line, "oom_kill ", 9)) {
            long long count = -1;
            assert(sscanf(line + 9, "%lld", &count) == 1 && count >= 0);
            return count;
        }
        char *next = strchr(line, '\n');
        if (!next) break;
        line = next + 1;
    }
    assert(!"missing kernel oom_kill counter");
    return -1;
}

int main(int argc, char **argv) {
    assert(argc == 4 && argv[1][0] == '/' && argv[2][0] == '/');
    int orphan = !strcmp(argv[3], "orphan");
    assert(orphan || !strcmp(argv[3], "memory"));
    /* Adopt the fixture's orphan so the test itself also reaps its zombie. */
    assert(prctl(PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) == 0);
    const char *root = argv[1], *program = argv[2];
    char identity[65]; uint8_t identity_bytes[32];
    SHA256((const unsigned char *)root, strlen(root), identity_bytes);
    for (int i = 0; i < 32; i++) sprintf(identity + 2*i, "%02x", identity_bytes[i]);
    char mode[4096], marker[4096], output[4096], error[4096], digest[65];
    snprintf(mode, sizeof(mode), "%s/mode", root);
    FILE *file = fopen(mode, "wx"); assert(file);
    fprintf(file, "%s\n", argv[3]); assert(fclose(file) == 0);
    snprintf(marker, sizeof(marker), "%s/%s", root, orphan ? "descendant" : "allocation-started");
    snprintf(output, sizeof(output), "%s/stdout", root);
    snprintf(error, sizeof(error), "%s/stderr", root);
    digest_path(program, digest);
    SplArray *parent = rt_linux_group_parent_acquire_v1(root, strlen(root), identity, 64);
    assert(field(parent, 0) == 0);
    SplArray empty = {0};
    SplArray *started = rt_linux_group_start_v1(program, strlen(program), digest, 64,
        &empty, &empty, root, strlen(root), root, strlen(root), identity, 64,
        33554432, 10000, output, strlen(output), error, strlen(error));
    assert(field(started, 0) == 1 && field(started, 1) == 0);
    int descendant_fd = -1; long descendant = 0, session = 0;
    if (orphan) {
        for (int i = 0; i < 1000 && access(marker, F_OK); i++) usleep(1000);
        file = fopen(marker, "r"); assert(file);
        assert(fscanf(file, "%ld %ld", &descendant, &session) == 2); fclose(file);
        assert(descendant > 0 && descendant == session && descendant != rt_linux_group.pid);
        descendant_fd = (int)syscall(SYS_pidfd_open, (pid_t)descendant, 0);
        assert(descendant_fd >= 0);
        struct pollfd living = {.fd = descendant_fd, .events = POLLIN};
        assert(poll(&living, 1, 0) == 0);
        int populated = 0;
        assert(rt_lg_populated(rt_linux_group.group_fd, &populated) && populated);
        assert(field(rt_linux_group_collect_v1(1), 0) == EBUSY);
    }
    SplArray *observed = NULL;
    for (int i = 0; i < 1500; i++) {
        observed = rt_linux_group_poll_v1(1);
        assert(field(observed, 0) == 0);
        if (field(observed, 1)) break;
        usleep(10000);
    }
    assert(field(observed, 1) && field(observed, 2) && field(observed, 3));
    assert(field(observed, 6) == 0 && field(observed, 7) == 0);
    assert(field(observed, 8) > 0);
    assert(access(marker, F_OK) == 0);
    if (orphan) {
        assert(field(observed, 5) == 0);
        struct pollfd dead = {.fd = descendant_fd, .events = POLLIN};
        assert(poll(&dead, 1, 1000) == 1 && (dead.revents & POLLIN));
        int status = 0;
        assert(waitpid((pid_t)descendant, &status, 0) == descendant);
        assert(WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL);
        close(descendant_fd);
    } else {
        assert(field(observed, 5) == 128 + SIGKILL);
        assert(oom_kills() > 0);
    }
    assert(field(rt_linux_group_collect_v1(1), 0) == 0);
    assert(rt_linux_group_parent_release_v1(field(parent, 1)) == 0);
    puts(orphan ? "PASS: setsid descendant retired after leader exit; pidfd exit and reap; cleanup" :
        "PASS: real child memory limit caused kernel oom_kill; exit137; tree empty; cleanup");
    return 0;
}
