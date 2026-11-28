/* Real cgroup v2 evidence for the leader-residue move (rt_lg_move_residue_v3)
 * and its thirteenth profile word. It runs the actual poll and collect owner
 * code against real kernel groups, so it must be started inside a delegated,
 * writable cgroup:
 *
 *   systemd-run --user --scope -q -p Delegate=yes ./selfcheck
 *
 * Without such a cgroup it exits 77, which is not a PASS. It qualifies the
 * move, the unchanged kill of everything else and the failure paths. It does
 * not launch an engine and proves nothing about a live guest. */
#if !defined(__linux__)
#include <stdio.h>
int main(void) { puts("SKIP: runtime_linux_group_residue_move_selfcheck is Linux-only"); return 77; }
#else
#define _GNU_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static void owned_sha256(const uint8_t *data, size_t len, uint8_t out[32]) {
    (void)data; (void)len; memset(out, 0, 32);
}
static char **owned_adapter_copy_argv(const char *command, uint64_t length,
        SplArray *args, int64_t *argc, int *error) {
    (void)command; (void)length; (void)args; *argc = 0; *error = ENOTSUP; return NULL;
}
static void owned_adapter_free_argv(char **value, int64_t argc) { (void)value; (void)argc; }
static SplArray *owned_adapter_values(const int64_t *values, int64_t count) {
    SplArray *result = calloc(1, sizeof(*result));
    assert(result);
    result->items = calloc((size_t)count, sizeof(*result->items));
    assert(result->items);
    result->cap = result->len = count;
    for (int64_t i = 0; i < count; i++) result->items[i].as_int = values[i];
    return result;
}
static int owned_adapter_fill_reserved_values(SplArray *array, const int64_t *values, int64_t count) {
    (void)array; (void)values; (void)count; return 0;
}
SplArray *rt_array_new(int64_t capacity) { (void)capacity; return NULL; }
void rt_array_free(SplArray *array) { if (array) { free(array->items); free(array); } }
int64_t rt_array_len(SplArray *array) { return array ? array->len : -1; }
int64_t rt_array_get(SplArray *array, int64_t index) {
    return array && index >= 0 && index < array->len ? array->items[index].as_int : 0;
}
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
int64_t rt_value_as_int(int64_t value) { return value; }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t *rt_string_data(int64_t value) { (void)value; return NULL; }

#include "../runtime_linux_group_owner_impl.h"

static char scope_path[4096];
static int scope_fd = -1, root_fd = -1;

static int write_text(int dir, const char *name, const char *text) {
    int fd = openat(dir, name, O_WRONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    ssize_t written = write(fd, text, strlen(text));
    close(fd);
    return written == (ssize_t)strlen(text);
}

static int read_text(int dir, const char *name, char *out, size_t cap) {
    int fd = openat(dir, name, O_RDONLY | O_CLOEXEC);
    if (fd < 0) return 0;
    ssize_t count = read(fd, out, cap - 1);
    close(fd);
    if (count < 0) return 0;
    out[count] = 0;
    return 1;
}

static int wait_empty(int group) {
    char events[256];
    for (int attempt = 0; attempt < 400; attempt++) {
        assert(read_text(group, "cgroup.events", events, sizeof(events)));
        if (strstr(events, "populated 0\n")) return 1;
        usleep(5000);
    }
    return 0;
}

static int member_of(int group, pid_t pid) {
    char members[4096], wanted[32];
    assert(read_text(group, "cgroup.procs", members, sizeof(members)));
    snprintf(wanted, sizeof(wanted), "%d\n", (int)pid);
    return strstr(members, wanted) == members || (strstr(members, wanted) && strstr(members, wanted)[-1] == '\n');
}

/* Not a PASS when the host gives no delegated cgroup to work in. */
static int enter_delegated_scope(void) {
    char line[4096];
    FILE *self = fopen("/proc/self/cgroup", "r");
    if (!self || !fgets(line, sizeof(line), self)) return 0;
    fclose(self);
    if (strncmp(line, "0::", 3)) return 0;
    line[strcspn(line, "\n")] = 0;
    snprintf(scope_path, sizeof(scope_path), "/sys/fs/cgroup%s", line + 3);
    scope_fd = open(scope_path, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (scope_fd < 0 || mkdirat(scope_fd, "residue-selfcheck-main", 0700)) return 0;
    int main_group = openat(scope_fd, "residue-selfcheck-main", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (main_group < 0 || !write_text(main_group, "cgroup.procs", "0") ||
        !write_text(scope_fd, "cgroup.subtree_control", "+memory")) {
        /* A shared scope: step back out and leave it as it was found. */
        if (main_group >= 0) close(main_group);
        (void)write_text(scope_fd, "cgroup.procs", "0");
        (void)unlinkat(scope_fd, "residue-selfcheck-main", AT_REMOVEDIR);
        return 0;
    }
    close(main_group);
    if (mkdirat(scope_fd, "residue-selfcheck-root", 0700)) return 0;
    root_fd = openat(scope_fd, "residue-selfcheck-root", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    return root_fd >= 0 && write_text(root_fd, "cgroup.subtree_control", "+memory");
}

typedef struct { pid_t leader, residue; int parent_fd, group_fd; char identity[65], native[80], parent[80]; } Fixture;

/* A helper group under its own parent beneath the delegated root, holding a
 * leader that leaves one live process behind and exits with `code`. */
static Fixture start_fixture(char fill, int code, int residue_word) {
    Fixture f;
    int report[2];
    memset(&f, 0, sizeof(f));
    memset(f.identity, fill, 64);
    snprintf(f.parent, sizeof(f.parent), "simple-parent-%c", fill);
    snprintf(f.native, sizeof(f.native), "simple-native-%s", f.identity);
    assert(mkdirat(root_fd, f.parent, 0700) == 0);
    f.parent_fd = openat(root_fd, f.parent, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(f.parent_fd >= 0 && write_text(f.parent_fd, "cgroup.subtree_control", "+memory"));
    assert(mkdirat(f.parent_fd, f.native, 0700) == 0);
    f.group_fd = openat(f.parent_fd, f.native, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(f.group_fd >= 0);
    assert(pipe(report) == 0);
    f.leader = fork();
    assert(f.leader >= 0);
    if (f.leader == 0) {
        close(report[0]);
        if (!write_text(f.group_fd, "cgroup.procs", "0")) _exit(120);
        pid_t residue = fork();
        if (residue < 0) _exit(121);
        if (residue == 0) { close(report[1]); for (;;) pause(); }
        if (write(report[1], &residue, sizeof(residue)) != (ssize_t)sizeof(residue)) _exit(122);
        _exit(code);
    }
    close(report[1]);
    assert(read(report[0], &f.residue, sizeof(f.residue)) == (ssize_t)sizeof(f.residue));
    close(report[0]);
    rt_linux_group = (RtLinuxGroup){.active = 1, .parent_fd = f.parent_fd, .group_fd = f.group_fd,
        .pidfd = open("/dev/null", O_RDONLY | O_CLOEXEC), .pid = f.leader, .stream_mode = 1,
        .started_ms = rt_lg_now_ms(), .timeout_ms = 0, .residue_move = residue_word};
    memcpy(rt_linux_group.name, f.native, strlen(f.native) + 1);
    memcpy(rt_linux_group.stream_identity, f.identity, 65);
    rt_lg_delegation.active = 1;
    rt_lg_delegation.root_fd = root_fd;
    rt_lg_delegation.parent_fd = f.parent_fd;
    return f;
}

/* Poll until the runtime reports the helper tree empty, then collect it.
 * Returns the leader exit code the runtime reports for the helper. */
static int retire_helper(const Fixture *f) {
    int empty = 0, reported;
    for (int attempt = 0; attempt < 600 && !empty; attempt++) {
        assert(rt_lg_poll(&rt_linux_group) == 0);
        empty = rt_linux_group.leader_reaped && rt_linux_group.tree_empty;
        if (!empty) usleep(5000);
    }
    assert(empty);
    reported = rt_linux_group.exit_code;
    SplArray *collected = rt_linux_group_collect_v1(1);
    assert(collected && collected->items[0].as_int == 0);
    rt_array_free(collected);
    assert(rt_linux_group.collected);
    /* Collect removed the helper group, so its now-empty parent can go too. */
    assert(unlinkat(root_fd, f->parent, AT_REMOVEDIR) == 0);
    rt_linux_group = (RtLinuxGroup){0};
    return reported;
}

static int engine_open(const Fixture *f) {
    char name[80];
    snprintf(name, sizeof(name), "simple-engine-%s", f->identity);
    return openat(root_fd, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
}

static void engine_remove(const Fixture *f, int engine) {
    char name[80];
    snprintf(name, sizeof(name), "simple-engine-%s", f->identity);
    assert(write_text(engine, "cgroup.kill", "1"));
    assert(wait_empty(engine));
    close(engine);
    assert(unlinkat(root_fd, name, AT_REMOVEDIR) == 0);
}

static void gone(pid_t pid) {
    for (int attempt = 0; attempt < 400; attempt++) {
        if (kill(pid, 0) != 0 && errno == ESRCH) return;
        usleep(5000);
    }
    assert(!"a process the runtime should have killed is still alive");
}

static void check_profile_words(void) {
    const char *broker = "/sys/fs/cgroup/service/broker";
    const char *policy = "cccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc";
    int64_t words[14] = {25, 2500, 100000, 11, 22, 3, 250000, 1000000, 250, 67108864, 134217728, 1, 1, 1};
    RtGroupStreamProfileV3 parsed;
    SplArray *twelve = owned_adapter_values(words, 12);
    assert(rt_lg_profile_parse_v3(broker, (int64_t)strlen(broker), policy, 64, twelve, &parsed) && parsed.v[12] == 0);
    rt_array_free(twelve);
    SplArray *thirteen = owned_adapter_values(words, 13);
    assert(rt_lg_profile_parse_v3(broker, (int64_t)strlen(broker), policy, 64, thirteen, &parsed) && parsed.v[12] == 1);
    rt_array_free(thirteen);
    for (int64_t bad = 0; bad <= 2; bad += 2) {
        words[12] = bad;
        SplArray *refused = owned_adapter_values(words, 13);
        assert(!rt_lg_profile_parse_v3(broker, (int64_t)strlen(broker), policy, 64, refused, &parsed));
        rt_array_free(refused);
    }
    words[12] = 1;
    SplArray *fourteen = owned_adapter_values(words, 14), *eleven = owned_adapter_values(words, 11);
    assert(!rt_lg_profile_parse_v3(broker, (int64_t)strlen(broker), policy, 64, fourteen, &parsed));
    assert(!rt_lg_profile_parse_v3(broker, (int64_t)strlen(broker), policy, 64, eleven, &parsed));
    rt_array_free(fourteen); rt_array_free(eleven);
}

int main(void) {
    char text[256];
    alarm(60);
    check_profile_words();
    if (!enter_delegated_scope()) {
        puts("SKIP: no delegated writable cgroup (run under systemd-run --user --scope -p Delegate=yes); not a PASS");
        return 77;
    }

    /* 1. Asked, leader exited 0: the residue is moved, thawed and alive; the
     *    helper group retires exactly as before. */
    Fixture moved = start_fixture('a', 0, 1);
    assert(retire_helper(&moved) == 0);
    int engine = engine_open(&moved);
    assert(engine >= 0);
    assert(member_of(engine, moved.residue) && kill(moved.residue, 0) == 0);
    assert(read_text(engine, "cgroup.freeze", text, sizeof(text)) && !strcmp(text, "0\n"));
    assert(read_text(engine, "cgroup.events", text, sizeof(text)) && strstr(text, "frozen 0\n"));
    /* The engine group takes the delegated root's limits, none of its own. */
    assert(read_text(engine, "memory.max", text, sizeof(text)) && !strcmp(text, "max\n"));
    engine_remove(&moved, engine);
    gone(moved.residue);

    /* 2. Asked, leader failed: nothing is moved and no group is made. */
    Fixture failed = start_fixture('b', 3, 1);
    assert(retire_helper(&failed) == 3);
    assert(engine_open(&failed) < 0 && errno == ENOENT);
    gone(failed.residue);

    /* 3. Not asked (twelve words): byte-for-byte the old behaviour. */
    Fixture plain = start_fixture('c', 0, 0);
    assert(retire_helper(&plain) == 0);
    assert(engine_open(&plain) < 0 && errno == ENOENT);
    gone(plain.residue);

    /* 4. Asked, leader exited 0, but cancelled: killed, never moved. */
    Fixture cancelled = start_fixture('d', 0, 1);
    rt_linux_group.cancelled = 1;
    assert(retire_helper(&cancelled) == 0);
    assert(engine_open(&cancelled) < 0 && errno == ENOENT);
    gone(cancelled.residue);

    /* 5. The name is already taken: never adopted. The residue is killed with
     *    its frozen helper group and the foreign directory is left as it was.
     *    The start is reported failed, not as a leader that exited 0. */
    Fixture taken = start_fixture('e', 0, 1);
    char name[80];
    snprintf(name, sizeof(name), "simple-engine-%s", taken.identity);
    assert(mkdirat(root_fd, name, 0700) == 0);
    assert(retire_helper(&taken) == RT_LG_RESIDUE_MOVE_FAILED_EXIT);
    engine = engine_open(&taken);
    assert(engine >= 0 && wait_empty(engine) && !member_of(engine, taken.residue));
    close(engine);
    assert(unlinkat(root_fd, name, AT_REMOVEDIR) == 0);
    gone(taken.residue);

    /* 6. A crash between freeze and move: the helper group stays frozen and
     *    populated. cgroup.kill still empties it, so recovery needs nothing new. */
    Fixture crashed = start_fixture('f', 0, 0);
    assert(waitpid(crashed.leader, NULL, 0) == crashed.leader);
    assert(write_text(crashed.group_fd, "cgroup.freeze", "1"));
    for (int attempt = 0; attempt < 400; attempt++) {
        assert(read_text(crashed.group_fd, "cgroup.events", text, sizeof(text)));
        if (strstr(text, "frozen 1\n")) break;
        usleep(5000);
    }
    assert(strstr(text, "frozen 1\n") && strstr(text, "populated 1\n"));
    assert(write_text(crashed.group_fd, "cgroup.kill", "1") && wait_empty(crashed.group_fd));
    gone(crashed.residue);
    close(crashed.group_fd);
    assert(unlinkat(crashed.parent_fd, crashed.native, AT_REMOVEDIR) == 0);
    close(crashed.parent_fd);
    assert(unlinkat(root_fd, crashed.parent, AT_REMOVEDIR) == 0);
    rt_linux_group = (RtLinuxGroup){0};

    /* 7. The delegated root refuses the engine group (EACCES or EPERM on
     *    mkdirat): nothing is made, the residue is killed with its helper
     *    group, and the leader that exited 0 is reported with the permission
     *    exit code. The cgroup root stands in for a root this uid may not
     *    create under; root itself can create anywhere, so it cannot check this. */
    assert(rt_lg_residue_refusal(EACCES) == RT_LG_RESIDUE_MOVE_PERMISSION_EXIT &&
        rt_lg_residue_refusal(EPERM) == RT_LG_RESIDUE_MOVE_PERMISSION_EXIT &&
        rt_lg_residue_refusal(EROFS) == RT_LG_RESIDUE_MOVE_PERMISSION_EXIT &&
        rt_lg_residue_refusal(EEXIST) == RT_LG_RESIDUE_MOVE_FAILED_EXIT &&
        RT_LG_RESIDUE_MOVE_FAILED_EXIT > 255 && RT_LG_RESIDUE_MOVE_PERMISSION_EXIT > 255);
    if (geteuid() == 0) {
        puts("SKIP: delegated-root permission refusal cannot be checked as root; not a PASS");
        return 77;
    }
    int denied_fd = open("/sys/fs/cgroup", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    assert(denied_fd >= 0);
    Fixture denied = start_fixture('g', 0, 1);
    snprintf(name, sizeof(name), "simple-engine-%s", denied.identity);
    errno = 0;
    assert(mkdirat(denied_fd, name, 0700) != 0 && (errno == EACCES || errno == EPERM || errno == EROFS));
    rt_lg_delegation.root_fd = denied_fd;
    assert(retire_helper(&denied) == RT_LG_RESIDUE_MOVE_PERMISSION_EXIT);
    assert(engine_open(&denied) < 0 && errno == ENOENT);
    assert(openat(denied_fd, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC) < 0 && errno == ENOENT);
    close(denied_fd);
    gone(denied.residue);

    close(root_fd);
    assert(unlinkat(scope_fd, "residue-selfcheck-root", AT_REMOVEDIR) == 0);
    puts("runtime_linux_group_residue_move_selfcheck: PASS (7 cases, real cgroup v2)");
    return 0;
}
#endif
