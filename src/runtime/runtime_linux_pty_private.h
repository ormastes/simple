#ifndef SIMPLE_RUNTIME_LINUX_PTY_PRIVATE_H
#define SIMPLE_RUNTIME_LINUX_PTY_PRIVATE_H

/* Included by runtime_process.c after the POSIX process and text helpers. */
enum { LINUX_PTY_SLOTS = 64, LINUX_PTY_GRACE_MS = 1000, LINUX_PTY_KILL_MS = 5000 };
struct LinuxPty {
    pthread_mutex_t lock;
    int handle;
    int generation;
    int master;
    int slave;
    pid_t child;
    int exit_code;
    int64_t hangup_ms;
    char slave_name[128];
    struct PipedUtf8Tail read_tail;
};

static struct LinuxPty linux_ptys[LINUX_PTY_SLOTS];
static pthread_once_t linux_ptys_once = PTHREAD_ONCE_INIT;

static void linux_pty_init(void) {
    for (size_t i = 0; i < LINUX_PTY_SLOTS; ++i) {
        pthread_mutex_init(&linux_ptys[i].lock, NULL);
    }
}

static struct LinuxPty* linux_pty_lock(int64_t handle) {
    if (handle <= 0 || handle > INT32_MAX) return NULL;
    pthread_once(&linux_ptys_once, linux_pty_init);
    struct LinuxPty* slot = &linux_ptys[(handle - 1) % LINUX_PTY_SLOTS];
    pthread_mutex_lock(&slot->lock);
    if (slot->handle == handle) return slot;
    pthread_mutex_unlock(&slot->lock);
    return NULL;
}

static int64_t linux_pty_now_ms(void) {
    struct timespec time;
    if (clock_gettime(CLOCK_MONOTONIC, &time) != 0) return -1;
    return (int64_t)time.tv_sec * 1000 + time.tv_nsec / 1000000;
}

static bool linux_pty_resize_fd(int fd, int32_t rows, int32_t cols) {
    if (rows < 1 || rows > UINT16_MAX || cols < 1 || cols > UINT16_MAX) return false;
    struct winsize size = {.ws_row = (unsigned short)rows, .ws_col = (unsigned short)cols};
    return ioctl(fd, TIOCSWINSZ, &size) == 0;
}

/* Preserve the caller's standard descriptors even when one is already closed. */
static int linux_pty_above_stdio(int fd) {
    if (fd < 0 || fd > STDERR_FILENO) return fd;
    int next = fcntl(fd, F_DUPFD_CLOEXEC, STDERR_FILENO + 1);
    close(fd);
    return next;
}

int32_t rt_pty_open(int32_t rows, int32_t cols) {
    pthread_once(&linux_ptys_once, linux_pty_init);
    for (int i = 0; i < LINUX_PTY_SLOTS; ++i) {
        struct LinuxPty* slot = &linux_ptys[i];
        if (pthread_mutex_trylock(&slot->lock) != 0) continue;
        if (slot->handle != 0 || slot->generation >= (INT32_MAX / LINUX_PTY_SLOTS) - 1) {
            pthread_mutex_unlock(&slot->lock);
            continue;
        }
        int master = linux_pty_above_stdio(posix_openpt(O_RDWR | O_NOCTTY | O_CLOEXEC | O_NONBLOCK));
        int slave = -1;
        if (master >= 0 && grantpt(master) == 0 && unlockpt(master) == 0 &&
            ptsname_r(master, slot->slave_name, sizeof(slot->slave_name)) == 0) {
            slave = linux_pty_above_stdio(open(slot->slave_name, O_RDWR | O_NOCTTY | O_CLOEXEC));
        }
        if (slave < 0 || !linux_pty_resize_fd(master, rows, cols)) {
            if (slave >= 0) close(slave);
            if (master >= 0) close(master);
            pthread_mutex_unlock(&slot->lock);
            return -1;
        }
        int handle = slot->generation++ * LINUX_PTY_SLOTS + i + 1;
        slot->handle = handle;
        slot->master = master;
        slot->slave = slave;
        slot->child = 0;
        slot->exit_code = -2;
        slot->hangup_ms = -1;
        slot->read_tail = (struct PipedUtf8Tail){{0, 0, 0}, 0};
        pthread_mutex_unlock(&slot->lock);
        return handle;
    }
    return -1;
}

static pid_t linux_pty_spawn_locked(struct LinuxPty* slot, const char* program, char* const argv[],
        const char* cwd, char* const environment[], bool search) {
    if (slot->child != 0 || slot->slave < 0) return -1;
    posix_spawn_file_actions_t actions;
    posix_spawnattr_t attr;
    if (posix_spawn_file_actions_init(&actions) != 0) return -1;
    int error = posix_spawnattr_init(&attr);
    if (error) {
        posix_spawn_file_actions_destroy(&actions);
        return -1;
    }
    sigset_t empty, defaults;
    sigemptyset(&empty);
    sigemptyset(&defaults);
    const int reset[] = {SIGINT, SIGTERM, SIGHUP, SIGPIPE, SIGQUIT, SIGCHLD, SIGTSTP, SIGTTIN, SIGTTOU};
    for (size_t i = 0; i < sizeof(reset) / sizeof(reset[0]); ++i) sigaddset(&defaults, reset[i]);
    /* The child becomes a session leader before opening the slave. Opening it
     * without O_NOCTTY assigns the controlling terminal to that session. */
    pid_t child = -1;
    if ((!cwd || !*cwd || posix_spawn_file_actions_addchdir_np(&actions, cwd) == 0) &&
        posix_spawn_file_actions_addopen(&actions, STDIN_FILENO, slot->slave_name, O_RDWR, 0) == 0 &&
        posix_spawn_file_actions_adddup2(&actions, STDIN_FILENO, STDOUT_FILENO) == 0 &&
        posix_spawn_file_actions_adddup2(&actions, STDIN_FILENO, STDERR_FILENO) == 0 &&
        /* A PTY child owns stdio only. Inherited request sockets would keep
         * client connections alive after their owner closes them. */
        posix_spawn_file_actions_addclosefrom_np(&actions, STDERR_FILENO + 1) == 0 &&
        posix_spawnattr_setsigmask(&attr, &empty) == 0 &&
        posix_spawnattr_setsigdefault(&attr, &defaults) == 0 &&
        posix_spawnattr_setflags(&attr, POSIX_SPAWN_SETSID | POSIX_SPAWN_SETSIGMASK | POSIX_SPAWN_SETSIGDEF) == 0) {
        error = search ? posix_spawnp(&child, program, &actions, &attr, argv, environment)
                       : posix_spawn(&child, program, &actions, &attr, argv, environment);
        if (error) child = -1;
    }
    posix_spawn_file_actions_destroy(&actions);
    posix_spawnattr_destroy(&attr);
    if (child > 0) {
        close(slot->slave);
        slot->slave = -1;
        slot->child = child;
        slot->exit_code = -1;
    }
    return child;
}

int64_t rt_pty_spawn(int32_t handle, int64_t program) {
    int64_t length = rt_string_len(program);
    const uint8_t* bytes = rt_string_data(program);
    if (length <= 0 || (uint64_t)length > SIZE_MAX - 6 || !bytes || memchr(bytes, 0, (size_t)length)) return -1;
    char* line = malloc((size_t)length + 6);
    if (!line) return -1;
    memcpy(line, "exec ", 5);
    memcpy(line + 5, bytes, (size_t)length);
    line[length + 5] = 0;
    char* command = line + 5;
    char* basename = strrchr(command, '/');
    char* argv[] = {basename ? basename + 1 : command, NULL};
    char* shell_argv[] = {"sh", "-c", line, NULL};
    struct LinuxPty* slot = linux_pty_lock(handle);
    pid_t child = -1;
    if (slot) {
        child = linux_pty_spawn_locked(slot, command, argv, NULL, environ, true);
        if (child < 0) child = linux_pty_spawn_locked(slot, "/bin/sh", shell_argv, NULL, environ, false);
        pthread_mutex_unlock(&slot->lock);
    }
    free(line);
    return child;
}

static bool linux_pty_add_environment(char** environment, size_t* used, const char* change) {
    if (!change || (*change != '+' && *change != '-')) return false;
    bool set = *change++ == '+';
    const char* equals = strchr(change, '=');
    if ((set && !equals) || (!set && equals)) return false;
    size_t length = equals ? (size_t)(equals - change) : strlen(change);
    if (length == 0) return false;
    for (size_t i = 0; i < *used;) {
        if (strncmp(environment[i], change, length) == 0 && environment[i][length] == '=') {
            environment[i] = environment[--*used];
        } else ++i;
    }
    if (set) environment[(*used)++] = (char*)change;
    return true;
}

static pid_t linux_pty_spawn_program(struct LinuxPty* slot, const char* program, char* const argv[],
        const char* cwd, char* const environment[]) {
    if (strchr(program, '/')) return linux_pty_spawn_locked(slot, program, argv, cwd, environment, false);
    const char* path = "/bin:/usr/bin";
    for (size_t i = 0; environment[i]; ++i) {
        if (strncmp(environment[i], "PATH=", 5) == 0) {
            path = environment[i] + 5;
            break;
        }
    }
    char file[4096];
    do {
        const char* end = strchr(path, ':');
        size_t length = end ? (size_t)(end - path) : strlen(path);
        int written = snprintf(file, sizeof(file), "%.*s%s%s",
            length < sizeof(file) ? (int)length : 0, length ? path : ".", "/", program);
        if (length < sizeof(file) && written > 0 && (size_t)written < sizeof(file)) {
            pid_t child = linux_pty_spawn_locked(slot, file, argv, cwd, environment, false);
            if (child > 0) return child;
        }
        path = end ? end + 1 : NULL;
    } while (path);
    return -1;
}

static const char* linux_pty_text(int64_t value) {
    int64_t length = rt_string_len(value);
    const uint8_t* bytes = rt_string_data(value);
    return length >= 0 && bytes && !memchr(bytes, 0, (size_t)length) ? (const char*)bytes : NULL;
}

int64_t rt_pty_spawn_exec_v1(int32_t handle, const char* program, SplArray* args,
        const char* cwd, SplArray* changes) {
    program = linux_pty_text((int64_t)(uintptr_t)program);
    if (!program || !*program) return -1;
    if (cwd) {
        cwd = linux_pty_text((int64_t)(uintptr_t)cwd);
        if (!cwd) return -1;
    }
    size_t n_args = (size_t)rt_array_len(args);
    size_t n_changes = (size_t)rt_array_len(changes);
    size_t used = 0;
    while (environ[used]) ++used;
    if (n_args > SIZE_MAX / sizeof(char*) - 2 ||
        n_changes > SIZE_MAX / sizeof(char*) - used - 1) return -1;
    char** argv = calloc(n_args + 2, sizeof(char*));
    char** environment = calloc(used + n_changes + 1, sizeof(char*));
    pid_t child = -1;
    if (argv && environment) {
        argv[0] = (char*)program;
        memcpy(environment, environ, used * sizeof(char*));
        bool valid = true;
        for (size_t i = 0; i < n_args; ++i) {
            argv[i + 1] = (char*)linux_pty_text(rt_array_get_text(args, (int64_t)i));
            if (!argv[i + 1]) valid = false;
        }
        for (size_t i = 0; valid && i < n_changes; ++i) {
            valid = linux_pty_add_environment(environment, &used,
                linux_pty_text(rt_array_get_text(changes, (int64_t)i)));
        }
        environment[used] = NULL;
        struct LinuxPty* slot = valid ? linux_pty_lock(handle) : NULL;
        if (slot) {
            child = linux_pty_spawn_program(slot, program, argv, cwd, environment);
            pthread_mutex_unlock(&slot->lock);
        }
    }
    free(environment);
    free(argv);
    return child;
}

static int64_t linux_pty_write_some(struct LinuxPty* slot, const uint8_t* bytes, size_t length) {
    ssize_t count;
    do { count = write(slot->master, bytes, length); } while (count < 0 && errno == EINTR);
    return count < 0 && (errno == EAGAIN || errno == EWOULDBLOCK) ? 0 : count;
}

/* These legacy operations share the hosted runtime's tagged bool result.
 * Resize and hangup use the separate unboxed bool ABI. */
int64_t rt_pty_write(int64_t handle, int64_t data) {
    int64_t length = rt_string_len(data);
    const uint8_t* bytes = rt_string_data(data);
    if (length < 0 || (length > 0 && !bytes)) return rt_value_bool(false);
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return rt_value_bool(false);
    int64_t sent = length == 0 ? 0 : linux_pty_write_some(slot, bytes, (size_t)length);
    pthread_mutex_unlock(&slot->lock);
    return rt_value_bool(sent == length);
}

int64_t rt_pty_write_bytes_v1(int64_t handle, SplArray* data) {
    if (!data) return -1;
    int64_t length = rt_array_len(data);
    uint8_t bytes[4096];
    if (length < 0) return -1;
    int64_t offered = length > (int64_t)sizeof(bytes) ? (int64_t)sizeof(bytes) : length;
    for (int64_t i = 0; i < offered; ++i) {
        int64_t value = rt_array_get(data, i);
        if (!rt_value_is_int(value)) return -1;
        int64_t byte = rt_value_as_int(value);
        if (byte < 0 || byte > UINT8_MAX) return -1;
        bytes[i] = (uint8_t)byte;
    }
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return -1;
    int64_t sent = offered == 0 ? 0 : linux_pty_write_some(slot, bytes, (size_t)offered);
    pthread_mutex_unlock(&slot->lock);
    return sent;
}

int64_t rt_pty_read(int64_t handle, int64_t timeout_ms) {
    uint8_t out[3 * (PIPED_RAW_CAP + 3)];
    size_t used = 0;
    struct LinuxPty* slot = timeout_ms < 0 ? NULL : linux_pty_lock(handle);
    if (slot) {
        struct pollfd pollfd = {.fd = slot->master, .events = POLLIN};
        int timeout = timeout_ms > INT32_MAX ? INT32_MAX : (int)timeout_ms;
        if (poll(&pollfd, 1, timeout) > 0) {
            uint8_t bytes[PIPED_RAW_CAP];
            ssize_t length = read(slot->master, bytes, sizeof(bytes));
            bool eof = length == 0 || (length < 0 && errno == EIO);
            if (length > 0 || eof) {
                piped_utf8_frame(&slot->read_tail, bytes, length > 0 ? (size_t)length : 0,
                    eof, out, sizeof(out), &used);
            }
        }
        pthread_mutex_unlock(&slot->lock);
    }
    return rt_string_new(out, used);
}

static bool linux_pty_running(struct LinuxPty* slot) {
    if (slot->child <= 0) return false;
    /* Keep the leader unreaped until close so its PID anchors the owned
     * process group even if a status probe first observes it exit. */
    siginfo_t status = {0};
    int result;
    do {
        result = waitid(P_PID, (id_t)slot->child, &status, WEXITED | WNOHANG | WNOWAIT);
    } while (result < 0 && errno == EINTR);
    if (result == 0) {
        if (status.si_pid == 0) return true;
        slot->exit_code = status.si_code == CLD_EXITED ? status.si_status : 128 + status.si_status;
    } else if (errno == ECHILD) {
        slot->child = 0;
        slot->exit_code = -2;
    } else return true;
    return false;
}

int64_t rt_pty_is_running(int64_t handle) {
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return rt_value_bool(false);
    bool running = linux_pty_running(slot);
    pthread_mutex_unlock(&slot->lock);
    return rt_value_bool(running);
}

bool rt_pty_resize(int64_t handle, int32_t rows, int32_t cols) {
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return false;
    bool ok = linux_pty_resize_fd(slot->master, rows, cols);
    pthread_mutex_unlock(&slot->lock);
    return ok;
}

static bool linux_pty_hangup(struct LinuxPty* slot) {
    linux_pty_running(slot);
    if (slot->child <= 0) return false;
    if (slot->hangup_ms >= 0) return true;
    if (kill(-slot->child, SIGHUP) != 0) return false;
    slot->hangup_ms = linux_pty_now_ms();
    return true;
}

bool rt_pty_hangup(int64_t handle) {
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return false;
    bool signaled = linux_pty_hangup(slot);
    pthread_mutex_unlock(&slot->lock);
    return signaled;
}

static bool linux_pty_wait(struct LinuxPty* slot, int64_t begin, int64_t limit) {
    const struct timespec slice = {.tv_sec = 0, .tv_nsec = 5000000L};
    while (linux_pty_running(slot)) {
        int64_t now = linux_pty_now_ms();
        if (begin < 0 || now < 0 || now - begin >= limit) return false;
        nanosleep(&slice, NULL);
    }
    return true;
}

int64_t rt_pty_close(int64_t handle) {
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return rt_value_bool(handle > 0 && handle <= INT32_MAX);
    linux_pty_hangup(slot);
    if (slot->master >= 0) {
        close(slot->master);
        slot->master = -1;
    }
    bool stopped = linux_pty_wait(slot, slot->hangup_ms, LINUX_PTY_GRACE_MS);
    if (slot->child > 0) {
        /* The unreaped leader still pins the original group. Stop remaining
         * members of that group before releasing the PID. */
        if (kill(-slot->child, SIGKILL) == 0 || errno == ESRCH) {
            if (!stopped) stopped = linux_pty_wait(slot, linux_pty_now_ms(), LINUX_PTY_KILL_MS);
        } else stopped = false;
        if (stopped && slot->child > 0) {
            pid_t reaped;
            do { reaped = waitpid(slot->child, NULL, 0); } while (reaped < 0 && errno == EINTR);
            stopped = reaped == slot->child || (reaped < 0 && errno == ECHILD);
        }
    }
    if (stopped) {
        if (slot->slave >= 0) close(slot->slave);
        slot->handle = 0;
    }
    pthread_mutex_unlock(&slot->lock);
    return rt_value_bool(stopped);
}

int64_t rt_pty_exit_code_v1(int64_t handle) {
    struct LinuxPty* slot = linux_pty_lock(handle);
    if (!slot) return -2;
    linux_pty_running(slot);
    int64_t code = slot->exit_code;
    pthread_mutex_unlock(&slot->lock);
    return code;
}

#endif
