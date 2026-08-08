#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

extern int64_t rt_process_spawn_guarded(const char*, const char**, int64_t);

static pid_t read_pid(const char* path) {
    FILE* file = fopen(path, "r");
    long value = -1;
    if (!file) return -1;
    if (fscanf(file, "%ld", &value) != 1) value = -1;
    fclose(file);
    return (pid_t)value;
}

static int wait_for_file(const char* path) {
    for (int i = 0; i < 100; i++) {
        if (access(path, R_OK) == 0) return 1;
        usleep(10000);
    }
    return 0;
}

static int stopped(pid_t pid) {
    if (pid <= 0) return 0;
    if (kill(pid, 0) != 0) return errno == ESRCH;
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
}

static int guarded_status(const char* command) {
    const char* args[] = {"-c", command};
    int64_t guardian = rt_process_spawn_guarded("/bin/sh", args, 2);
    int status = 0;
    if (guardian <= 0 || waitpid((pid_t)guardian, &status, 0) < 0) return -2;
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

int main(void) {
    char dir[128];
    char wrapper_file[160];
    char child_file[160];
    char command[640];
    if (guarded_status("exit 0") != 0 || guarded_status("exit 7") != 7 ||
        guarded_status("kill -TERM $$") != -1) return 5;
    snprintf(dir, sizeof(dir), "/tmp/simple-guarded-%ld", (long)getpid());
    if (mkdir(dir, 0700) != 0) return 1;
    snprintf(wrapper_file, sizeof(wrapper_file), "%s/wrapper.pid", dir);
    snprintf(child_file, sizeof(child_file), "%s/child.pid", dir);
    snprintf(command, sizeof(command),
             "echo $$ > '%s'; /bin/sh -c 'echo $$ > \"%s\"; while :; do sleep 1; done' & wait",
             wrapper_file, child_file);

    pid_t launcher = fork();
    if (launcher == 0) {
        const char* args[] = {"-c", command};
        int64_t guardian = rt_process_spawn_guarded("/bin/sh", args, 2);
        int status = 0;
        if (guardian <= 0 || waitpid((pid_t)guardian, &status, 0) < 0) _exit(2);
        _exit(WIFEXITED(status) ? WEXITSTATUS(status) : 3);
    }
    if (launcher < 0 || !wait_for_file(wrapper_file) || !wait_for_file(child_file)) return 2;
    pid_t wrapper = read_pid(wrapper_file);
    pid_t child = read_pid(child_file);
    if (wrapper <= 1 || child <= 1 || kill(wrapper, 0) != 0 || kill(child, 0) != 0) return 3;

    kill(launcher, SIGKILL);
    waitpid(launcher, NULL, 0);
    for (int i = 0; i < 200 && (!stopped(wrapper) || !stopped(child)); i++) usleep(10000);
    int ok = stopped(wrapper) && stopped(child);
    if (!ok) {
        kill(wrapper, SIGKILL);
        kill(child, SIGKILL);
    }
    unlink(wrapper_file);
    unlink(child_file);
    rmdir(dir);
    return ok ? 0 : 4;
}
