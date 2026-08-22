#include "runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/time.h>
#include <sys/socket.h>
#include <sys/resource.h>
#include <sys/ipc.h>
#include <sys/ioctl.h>
#include <sys/msg.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static const char** test_args;
static int64_t test_arg_count;
static volatile sig_atomic_t sigpipe_count;
static volatile sig_atomic_t alarm_count;

int64_t rt_array_len(SplArray* ignored) {
    (void)ignored;
    return test_arg_count;
}

int64_t rt_array_get(SplArray* ignored, int64_t index) {
    (void)ignored;
    return index + 1;
}

const uint8_t* rt_string_data(int64_t value) {
    return (const uint8_t*)test_args[value - 1];
}

static void count_signal(int signal_number) {
    if (signal_number == SIGPIPE) sigpipe_count++;
    if (signal_number == SIGALRM) alarm_count++;
}

static int64_t spawn_shell(const char* script) {
    static const char* args[2];
    static SplArray placeholder;
    args[0] = "-c";
    args[1] = script;
    test_args = args;
    test_arg_count = 2;
    return rt_process_spawn_piped("/bin/sh", &placeholder);
}

static int sandbox_limit_is(int resource, rlim_t current, rlim_t maximum) {
    struct rlimit limit = {0};
    return syscall(SYS_getrlimit, resource, &limit) == 0 &&
        limit.rlim_cur == current && limit.rlim_max == maximum;
}

static int remove_sysv_objects(int shmid, int msgid, int semid) {
    int removed = 1;
    if (shmid >= 0 && shmctl(shmid, IPC_RMID, NULL) != 0) removed = 0;
    if (msgid >= 0 && msgctl(msgid, IPC_RMID, NULL) != 0) removed = 0;
    if (semid >= 0 && semctl(semid, 0, IPC_RMID) != 0) removed = 0;
    return removed;
}

static int sandbox_pre_main_denials;

static const char* representative_hostile_loader_env_names[] = {
    "LD_PRELOAD",
    "LD_AUDIT",
    "LD_DEBUG",
    "LD_DEBUG_OUTPUT",
    "LD_LIBRARY_PATH",
    "LD_ORIGIN_PATH",
};

#ifdef __linux__
extern bool rt_browser_renderer_preinit_active_for_test(void);

__attribute__((constructor))
static void sandbox_pre_main_probe(void) {
    if (!rt_browser_renderer_preinit_active_for_test()) return;
    errno = 0;
    int file_denied = open("/etc/passwd", O_RDONLY) < 0 && errno == EACCES;
    errno = 0;
    int socket_denied = socket(AF_INET, SOCK_STREAM, 0) < 0 && errno == EPERM;
    errno = 0;
    pid_t child = fork();
    if (child == 0) _exit(125);
    if (child > 0) {
        int status;
        while (waitpid(child, &status, 0) < 0 && errno == EINTR) {}
    }
    int fork_denied = child < 0 && errno == EPERM;
    sandbox_pre_main_denials = file_denied && socket_denied && fork_denied;
}
#else
static bool rt_browser_renderer_preinit_active_for_test(void) {
    return false;
}
#endif

static int sandbox_probe(int argc, char** argv) {
    if (argc != 7 || strcmp(argv[0], "simple-browser-renderer") != 0 ||
        getenv("SIMPLE_BROWSER_RENDERER_SECRET") != NULL) {
        return 10;
    }
    for (size_t i = 0;
         i < sizeof(representative_hostile_loader_env_names) /
             sizeof(representative_hostile_loader_env_names[0]);
         i++) {
        if (getenv(representative_hostile_loader_env_names[i]) != NULL) {
            return 30;
        }
    }
    if (!sandbox_pre_main_denials) return 29;
    char cwd[8];
    if (!getcwd(cwd, sizeof(cwd)) || strcmp(cwd, "/") != 0) return 11;
    int inherited_fd = atoi(argv[2]);
    errno = 0;
    if (fcntl(inherited_fd, F_GETFD) >= 0 || errno != EBADF) return 12;
    if (!rt_browser_renderer_sandbox_enter()) return 13;
    if (!sandbox_limit_is(RLIMIT_CORE, 0, 0) ||
        !sandbox_limit_is(
            RLIMIT_AS, 512U * 1024U * 1024U, 512U * 1024U * 1024U) ||
        !sandbox_limit_is(RLIMIT_CPU, 30, 30) ||
        !sandbox_limit_is(RLIMIT_FSIZE, 0, 0) ||
        !sandbox_limit_is(RLIMIT_NPROC, 0, 0) ||
        !sandbox_limit_is(RLIMIT_NOFILE, 4, 4)) {
        return 14;
    }
    errno = 0;
    if (open("/etc/passwd", O_RDONLY) >= 0 || errno != EACCES) return 15;
    errno = 0;
    if (socket(AF_INET, SOCK_STREAM, 0) >= 0 || errno != EPERM) return 16;
    errno = 0;
    if (fork() >= 0 || errno != EPERM) return 17;
    errno = 0;
    if (kill(getpid(), 0) >= 0 || errno != EPERM) return 18;
#if defined(SYS_get_robust_list)
    void* robust_head = NULL;
    size_t robust_len = 0;
    errno = 0;
    if (syscall(
            SYS_get_robust_list, getppid(), &robust_head, &robust_len) >= 0 ||
        errno != EPERM) {
        return 42;
    }
#endif
    char* exec_args[] = {(char*)"true", NULL};
    char* exec_env[] = {NULL};
    errno = 0;
    if (syscall(SYS_execve, "/bin/true", exec_args, exec_env) >= 0 ||
        errno != EPERM) {
        return 19;
    }
    errno = 0;
    if (fcntl(STDIN_FILENO, F_SETOWN, getppid()) >= 0 || errno != EPERM) {
        return 34;
    }
    int async_owner = getppid();
    errno = 0;
    if (ioctl(STDIN_FILENO, FIOSETOWN, &async_owner) >= 0 || errno != EPERM) {
        return 35;
    }
    errno = 0;
    if (setpriority(PRIO_PROCESS, getppid(), 1) >= 0 || errno != EPERM) {
        return 20;
    }
#if defined(SYS_newfstatat) || defined(SYS_fstatat64) || defined(SYS_stat)
    struct stat path_state;
#endif
#if defined(SYS_newfstatat)
    errno = 0;
    if (syscall(SYS_newfstatat, AT_FDCWD, "/etc/passwd", &path_state, 0) >= 0 ||
        errno != EPERM) {
        return 29;
    }
#elif defined(SYS_fstatat64)
    errno = 0;
    if (syscall(SYS_fstatat64, AT_FDCWD, "/etc/passwd", &path_state, 0) >= 0 ||
        errno != EPERM) {
        return 29;
    }
#endif
#if defined(SYS_stat)
    errno = 0;
    if (syscall(SYS_stat, "/etc/passwd", &path_state) >= 0 ||
        errno != EPERM) {
        return 33;
    }
#endif
#if defined(SYS_readlink) || defined(SYS_readlinkat)
    char path_target[32];
#endif
#if defined(SYS_readlink)
    errno = 0;
    if (syscall(SYS_readlink, "/proc/self/exe", path_target,
            sizeof(path_target)) >= 0 || errno != EPERM) {
        return 30;
    }
#elif defined(SYS_readlinkat)
    errno = 0;
    if (syscall(SYS_readlinkat, AT_FDCWD, "/proc/self/exe", path_target,
            sizeof(path_target)) >= 0 || errno != EPERM) {
        return 30;
    }
#endif
#if defined(SYS_name_to_handle_at)
    errno = 0;
    if (syscall(SYS_name_to_handle_at, AT_FDCWD, "/etc/passwd",
            NULL, NULL, 0) >= 0 || errno != EPERM) {
        return 34;
    }
#endif
#if defined(SYS_getxattr)
    errno = 0;
    if (syscall(SYS_getxattr, "/etc/passwd", "user.simple",
            NULL, 0) >= 0 || errno != EPERM) {
        return 35;
    }
#endif
#if defined(SYS_statfs)
    errno = 0;
    if (syscall(SYS_statfs, "/etc/passwd", NULL) >= 0 || errno != EPERM) {
        return 36;
    }
#endif
#if defined(SYS_inotify_init1)
    errno = 0;
    if (syscall(SYS_inotify_init1, O_CLOEXEC) >= 0 || errno != EPERM) {
        return 31;
    }
#endif
#if defined(SYS_membarrier)
    errno = 0;
    if (syscall(SYS_membarrier, 0, 0) >= 0 || errno != EPERM) return 32;
#endif
#if defined(SYS_io_uring_enter)
    errno = 0;
    if (syscall(SYS_io_uring_enter, -1, 0, 0, 0, NULL, 0) >= 0 ||
        errno != EPERM) {
        return 37;
    }
#endif
#if defined(SYS_personality)
    errno = 0;
    if (syscall(SYS_personality, ~0UL) >= 0 || errno != EPERM) return 38;
#endif
#if defined(SYS_chmod)
    errno = 0;
    if (syscall(SYS_chmod, argv[6], 0) >= 0 || errno != EPERM) return 39;
#endif
#if defined(SYS_truncate)
    errno = 0;
    if (syscall(SYS_truncate, argv[6], 0) >= 0 || errno != EPERM) return 40;
#endif
#if defined(SYS_utimensat)
    struct timespec changed_times[2] = {{1, 0}, {1, 0}};
    errno = 0;
    if (syscall(
            SYS_utimensat, AT_FDCWD, argv[6], changed_times, 0) >= 0 ||
        errno != EPERM) {
        return 41;
    }
#endif
    unsigned long affinity = 1;
    errno = 0;
    if (syscall(
            SYS_sched_setaffinity, getppid(), sizeof(affinity),
            &affinity) >= 0 || errno != EPERM) {
        return 21;
    }
    int shmid = atoi(argv[3]);
    int msgid = atoi(argv[4]);
    int semid = atoi(argv[5]);
    struct shmid_ds shm_state;
    struct msqid_ds msg_state;
    errno = 0;
    if (shmctl(shmid, IPC_STAT, &shm_state) >= 0 || errno != EPERM) return 22;
    errno = 0;
    if (msgctl(msgid, IPC_STAT, &msg_state) >= 0 || errno != EPERM) return 23;
    errno = 0;
    if (semctl(semid, 0, GETVAL) >= 0 || errno != EPERM) return 24;
    const char* input = rt_browser_renderer_read_stdin_some(8192);
    if (!input || strcmp(input, "small") != 0) return 25;
    if (write(STDOUT_FILENO, "stdout-leak", 11) < 0) return 26;
    if (write(STDERR_FILENO, "stderr-leak", 11) < 0) return 27;
    return rt_browser_renderer_write_protocol_some(
        "sandbox-ok", 10, 0, 10) == 10 ? 0 : 28;
}

static int sandboxed_renderer_is_sanitized_and_contained(void) {
    static SplArray placeholder;
    int inherited_fd = open("/etc/passwd", O_RDONLY);
    if (inherited_fd < 3) return 0;
    int shmid = shmget(IPC_PRIVATE, 4096, IPC_CREAT | 0600);
    int msgid = msgget(IPC_PRIVATE, IPC_CREAT | 0600);
    int semid = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600);
    if (shmid < 0 || msgid < 0 || semid < 0) {
        remove_sysv_objects(shmid, msgid, semid);
        return 0;
    }
    char mutation_path[] = "/tmp/simple-browser-sandbox-mutation-XXXXXX";
    int mutation_fd = mkstemp(mutation_path);
    struct timespec fixed_times[2] = {
        {1234567890, 0}, {1234567890, 0}
    };
    if (mutation_fd < 0 ||
        write(mutation_fd, "safe", 4) != 4 ||
        fchmod(mutation_fd, 0600) != 0 ||
        futimens(mutation_fd, fixed_times) != 0 ||
        close(mutation_fd) != 0) {
        if (mutation_fd >= 0) close(mutation_fd);
        unlink(mutation_path);
        remove_sysv_objects(shmid, msgid, semid);
        close(inherited_fd);
        return 0;
    }
    char inherited_text[32];
    char shmid_text[32];
    char msgid_text[32];
    char semid_text[32];
    snprintf(inherited_text, sizeof(inherited_text), "%d", inherited_fd);
    snprintf(shmid_text, sizeof(shmid_text), "%d", shmid);
    snprintf(msgid_text, sizeof(msgid_text), "%d", msgid);
    snprintf(semid_text, sizeof(semid_text), "%d", semid);
    static const char* args[6];
    args[0] = "--sandbox-probe";
    args[1] = inherited_text;
    args[2] = shmid_text;
    args[3] = msgid_text;
    args[4] = semid_text;
    args[5] = mutation_path;
    test_args = args;
    test_arg_count = 6;
    int loader_env_ready = 1;
    for (size_t i = 0;
         i < sizeof(representative_hostile_loader_env_names) /
             sizeof(representative_hostile_loader_env_names[0]);
         i++) {
        if (setenv(
                representative_hostile_loader_env_names[i],
                "/hostile/loader", 1) != 0) {
            loader_env_ready = 0;
        }
    }
    if (!loader_env_ready ||
        setenv("SIMPLE_BROWSER_RENDERER_SECRET", "must-not-leak", 1) != 0) {
        for (size_t i = 0;
             i < sizeof(representative_hostile_loader_env_names) /
                 sizeof(representative_hostile_loader_env_names[0]);
             i++) {
            unsetenv(representative_hostile_loader_env_names[i]);
        }
        close(inherited_fd);
        unlink(mutation_path);
        remove_sysv_objects(shmid, msgid, semid);
        return 0;
    }
    int64_t first_pid = rt_browser_renderer_spawn_sandboxed(
        "/proc/self/exe", &placeholder);
    int64_t second_pid = rt_browser_renderer_spawn_sandboxed(
        "/proc/self/exe", &placeholder);
    close(inherited_fd);
    unsetenv("SIMPLE_BROWSER_RENDERER_SECRET");
    for (size_t i = 0;
         i < sizeof(representative_hostile_loader_env_names) /
             sizeof(representative_hostile_loader_env_names[0]);
         i++) {
        unsetenv(representative_hostile_loader_env_names[i]);
    }
    if (first_pid <= 0 || second_pid <= 0) {
        if (first_pid > 0) rt_process_close_piped(first_pid);
        if (second_pid > 0) rt_process_close_piped(second_pid);
        unlink(mutation_path);
        remove_sysv_objects(shmid, msgid, semid);
        return 0;
    }
    if (!rt_process_write_stdin(first_pid, "small")) {
        rt_process_close_piped(first_pid);
        rt_process_close_piped(second_pid);
        unlink(mutation_path);
        remove_sysv_objects(shmid, msgid, semid);
        return 0;
    }
    int saw_ok = 0;
    for (int i = 0; i < 2000 && !saw_ok; i++) {
        const char* chunk = rt_process_read_stdout(first_pid);
        saw_ok = chunk && strcmp(chunk, "sandbox-ok") == 0;
        if (!saw_ok) usleep(1000);
    }
    int first_closed = rt_process_close_piped(first_pid);
    int second_independent = rt_process_is_alive(second_pid) &&
        rt_process_write_stdin(second_pid, "small");
    int second_saw_ok = 0;
    for (int i = 0; i < 2000 && !second_saw_ok; i++) {
        const char* chunk = rt_process_read_stdout(second_pid);
        second_saw_ok = chunk && strcmp(chunk, "sandbox-ok") == 0;
        if (!second_saw_ok) usleep(1000);
    }
    int second_closed = rt_process_close_piped(second_pid);
    int64_t restarted_pid = rt_browser_renderer_spawn_sandboxed(
        "/proc/self/exe", &placeholder);
    int renderer_slot_released = restarted_pid > 0 &&
        rt_process_close_piped(restarted_pid);
    struct stat mutation_state = {0};
    int mutation_blocked =
        stat(mutation_path, &mutation_state) == 0 &&
        mutation_state.st_size == 4 &&
        (mutation_state.st_mode & 0777) == 0600 &&
        mutation_state.st_mtime == 1234567890;
    unlink(mutation_path);
    int cleaned = remove_sysv_objects(shmid, msgid, semid);
    return saw_ok && first_closed && second_independent && second_saw_ok &&
        second_closed && cleaned && renderer_slot_released && mutation_blocked;
}

static int sandbox_enter_without_preinit_fails_closed(void) {
    pid_t child = fork();
    if (child == 0) {
        _exit(rt_browser_renderer_sandbox_enter() ? 1 : 0);
    }
    if (child < 0) return 0;
    int status = 0;
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR) return 0;
    }
    return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

static int stopped(pid_t pid) {
    if (pid <= 0) return 0;
    if (kill(pid, 0) != 0) return errno == ESRCH;
#ifdef __linux__
    char path[64];
    snprintf(path, sizeof(path), "/proc/%ld/stat", (long)pid);
    FILE* file = fopen(path, "r");
    if (!file) return 1;
    long ignored = 0;
    char name[256];
    char state = 0;
    int fields = fscanf(file, "%ld %255s %c", &ignored, name, &state);
    fclose(file);
    return fields == 3 && state == 'Z';
#else
    return 0;
#endif
}

static int read_pid_from_child(int64_t pid, pid_t* child_pid) {
    for (int i = 0; i < 1000; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        if (chunk && sscanf(chunk, "%d", child_pid) == 1) return 1;
        usleep(1000);
    }
    return 0;
}

static int closed_child_write_is_nonfatal(void) {
    struct sigaction action = {0};
    action.sa_handler = count_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGPIPE, &action, NULL) != 0) return 0;

    int64_t pid = spawn_shell("exec 0<&-; sleep 1");
    if (pid <= 0) return 0;
    usleep(20000);
    char payload[65537];
    memset(payload, 'x', sizeof(payload) - 1);
    payload[sizeof(payload) - 1] = '\0';
    int ok = !rt_process_write_stdin(pid, payload) && sigpipe_count == 0;
    kill((pid_t)pid, SIGTERM);
    while (rt_process_is_alive(pid)) usleep(1000);
    return ok;
}

static int interrupted_large_write_completes(void) {
    struct sigaction action = {0};
    action.sa_handler = count_signal;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGALRM, &action, NULL) != 0) return 0;

    int64_t pid = spawn_shell(
        "sleep 0.05; dd bs=1 count=262144 of=/dev/null 2>/dev/null; printf ok"
    );
    if (pid <= 0) return 0;
    char* payload = (char*)malloc(262145);
    if (!payload) return 0;
    memset(payload, 'y', 262144);
    payload[262144] = '\0';

    struct itimerval timer = {0};
    timer.it_value.tv_usec = 10000;
    setitimer(ITIMER_REAL, &timer, NULL);
    int wrote = rt_process_write_stdin(pid, payload);
    free(payload);

    int saw_ok = 0;
    for (int i = 0; i < 1000 && !saw_ok; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        saw_ok = chunk && strstr(chunk, "ok") != NULL;
        if (!saw_ok) usleep(1000);
    }
    while (rt_process_is_alive(pid)) usleep(1000);
    return wrote && alarm_count > 0 && saw_ok;
}

static int bounded_write_reports_backpressure(void) {
    int64_t pid = spawn_shell("sleep 1");
    if (pid <= 0) return 0;
    char payload[4096];
    memset(payload, 'z', sizeof(payload));
    int saw_would_block = 0;
    for (int64_t offset = 0; offset < 1048576; offset += sizeof(payload)) {
        int64_t written = rt_process_write_stdin_some(
            pid, payload, sizeof(payload), 0, sizeof(payload));
        if (written < 0) {
            rt_process_close_piped(pid);
            return 0;
        }
        if (written == 0) {
            saw_would_block = 1;
            break;
        }
    }
    int closed = rt_process_close_piped(pid);
    return saw_would_block && closed &&
        rt_process_write_stdin_some(pid, payload, sizeof(payload), 0, sizeof(payload)) == -1;
}

static int inherited_descriptor_is_closed(void) {
#if !defined(__linux__) && !defined(__APPLE__)
    return 1;
#else
    int source_fd = open("/etc/passwd", O_RDONLY);
    if (source_fd < 0) return 0;
    int inherited_fd = fcntl(source_fd, F_DUPFD, 64);
    close(source_fd);
    if (inherited_fd < 0 ||
        fcntl(inherited_fd, F_SETFD, 0) != 0) {
        if (inherited_fd >= 0) close(inherited_fd);
        return 0;
    }
    char script[160];
    snprintf(
        script, sizeof(script),
#ifdef __APPLE__
        "if [ -e /dev/fd/%d ]; then printf leak; else printf clean; fi; sleep 30",
#else
        "if [ -e /proc/self/fd/%d ]; then printf leak; else printf clean; fi; sleep 30",
#endif
        inherited_fd
    );
    int64_t pid = spawn_shell(script);
    if (pid <= 0) {
        close(inherited_fd);
        return 0;
    }
    int clean = 0;
    int leaked = 0;
    for (int i = 0; i < 1000 && !clean; i++) {
        const char* chunk = rt_process_read_stdout(pid);
        clean = chunk && strstr(chunk, "clean") != NULL;
        leaked = chunk && strstr(chunk, "leak") != NULL;
        if (!clean) usleep(1000);
    }
    int closed = rt_process_close_piped(pid);
    close(inherited_fd);
    if (!clean || !closed) {
        fprintf(
            stderr, "inherited fd check: clean=%d leak=%d closed=%d\n",
            clean, leaked, closed);
    }
    return clean && closed;
#endif
}

static int exact_close_kills_and_reaps_group(void) {
    int64_t pid = spawn_shell("sleep 30 & echo $!; wait");
    pid_t grandchild = -1;
    if (pid <= 0 || !read_pid_from_child(pid, &grandchild)) return 0;
    if (!rt_process_close_piped(pid)) return 0;
#ifdef __APPLE__
    for (int i = 0; i < 1000; i++) {
        if (kill(-(pid_t)pid, 0) != 0 && errno == ESRCH) {
            return stopped((pid_t)pid);
        }
        usleep(1000);
    }
    return 0;
#else
    for (int i = 0; i < 1000 && !stopped(grandchild); i++) usleep(1000);
    return stopped((pid_t)pid) && stopped(grandchild);
#endif
}

static int reaped_leader_still_kills_group(void) {
    int64_t pid = spawn_shell("trap '' TERM; sleep 30 & echo $!; exit 0");
    pid_t grandchild = -1;
    if (pid <= 0 || !read_pid_from_child(pid, &grandchild)) return 0;
    usleep(20000);
    if (!rt_process_close_piped(pid)) return 0;
#ifdef __APPLE__
    for (int i = 0; i < 1000; i++) {
        if (kill(-(pid_t)pid, 0) != 0 && errno == ESRCH) return 1;
        usleep(1000);
    }
    return 0;
#else
    for (int i = 0; i < 1000 && !stopped(grandchild); i++) usleep(1000);
    return stopped(grandchild);
#endif
}

static int close_recycles_slots_and_rejects_unknown_handles(void) {
    if (rt_process_close_piped(-1) || rt_process_close_piped(999999999)) return 0;
    struct timespec started;
    struct timespec finished;
    if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) return 0;
    for (int i = 0; i < 32; i++) {
        int64_t pid = spawn_shell("exit 0");
        if (pid <= 0) return 0;
        usleep(1000);
        if (!rt_process_close_piped(pid)) return 0;
        if (rt_process_write_stdin(pid, "late") || rt_process_is_alive(pid)) return 0;
    }
    if (clock_gettime(CLOCK_MONOTONIC, &finished) != 0) return 0;
    double elapsed = (double)(finished.tv_sec - started.tv_sec) +
        (double)(finished.tv_nsec - started.tv_nsec) / 1000000000.0;
    return elapsed < 5.0;
}

static int checked_read_and_liveness_preserve_statuses(void) {
    int32_t status = 99;
    const char* invalid = rt_process_read_stdout_checked(-1, &status);
    if (!invalid || invalid[0] != '\0' || status != -2 ||
        rt_process_read_stdout_checked(-1, NULL)[0] != '\0' ||
        rt_process_is_alive_checked(-1) != -2) {
        return 0;
    }

    int64_t idle_pid = spawn_shell("sleep 30");
    if (idle_pid <= 0) return 0;
    status = 99;
    const char* idle = rt_process_read_stdout_checked(idle_pid, &status);
    int idle_ok = idle && idle[0] == '\0' && status == 0 &&
        rt_process_is_alive_checked(idle_pid) == 1;
    int idle_closed = rt_process_close_piped(idle_pid);
    if (!idle_ok || !idle_closed) return 0;

    int64_t data_pid = spawn_shell("printf checked-data");
    if (data_pid <= 0) return 0;
    int saw_data = 0;
    int saw_eof = 0;
    for (int i = 0; i < 1000 && !saw_eof; i++) {
        status = 99;
        const char* chunk = rt_process_read_stdout_checked(data_pid, &status);
        if (status == 1) {
            if (!chunk || strstr(chunk, "checked-data") == NULL) return 0;
            saw_data = 1;
        } else if (status == 2) {
            saw_eof = 1;
        } else if (status != 0) {
            return 0;
        }
        if (!saw_eof) usleep(1000);
    }
    int exited = 0;
    for (int i = 0; i < 1000 && !exited; i++) {
        int32_t alive = rt_process_is_alive_checked(data_pid);
        if (alive == 0) exited = 1;
        else if (alive != 1) return 0;
        if (!exited) usleep(1000);
    }
    int closed = rt_process_close_piped(data_pid);
    return saw_data && saw_eof && exited && closed &&
        rt_process_is_alive_checked(data_pid) == -2;
}

static int parent_death_stops_child(void) {
#ifndef __linux__
    return 1;
#else
    char path[128];
    snprintf(path, sizeof(path), "/tmp/simple-piped-parent-%ld.pid", (long)getpid());
    unlink(path);
    pid_t launcher = fork();
    if (launcher == 0) {
        char script[256];
        snprintf(script, sizeof(script), "echo $$ > '%s'; exec sleep 30", path);
        if (spawn_shell(script) <= 0) _exit(2);
        for (int i = 0; i < 1000 && access(path, R_OK) != 0; i++) usleep(1000);
        _exit(access(path, R_OK) == 0 ? 0 : 3);
    }
    if (launcher < 0) return 0;
    int status = 0;
    if (waitpid(launcher, &status, 0) != launcher ||
        !WIFEXITED(status) || WEXITSTATUS(status) != 0) {
        return 0;
    }
    FILE* file = fopen(path, "r");
    long child = -1;
    if (!file || fscanf(file, "%ld", &child) != 1) {
        if (file) fclose(file);
        unlink(path);
        return 0;
    }
    fclose(file);
    unlink(path);
    for (int i = 0; i < 1000 && !stopped((pid_t)child); i++) usleep(1000);
    return stopped((pid_t)child);
#endif
}

int main(int argc, char** argv) {
    if (argc > 1 && strcmp(argv[1], "--sandbox-probe") == 0) {
        return sandbox_probe(argc, argv);
    }
    if (rt_browser_renderer_preinit_active_for_test()) return 11;
    if (!closed_child_write_is_nonfatal()) return 1;
    if (!interrupted_large_write_completes()) return 2;
    if (!bounded_write_reports_backpressure()) return 3;
    if (!inherited_descriptor_is_closed()) return 4;
    if (!exact_close_kills_and_reaps_group()) return 5;
    if (!reaped_leader_still_kills_group()) return 6;
    if (!close_recycles_slots_and_rejects_unknown_handles()) return 7;
    if (!checked_read_and_liveness_preserve_statuses()) return 8;
    if (!parent_death_stops_child()) return 9;
    if (!sandboxed_renderer_is_sanitized_and_contained()) return 10;
    if (!sandbox_enter_without_preinit_fails_closed()) return 11;
    return 0;
}
