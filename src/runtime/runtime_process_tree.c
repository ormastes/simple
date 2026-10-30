/* Session-owned process trees. See runtime_process_tree.h for the contract.
 *
 * libc only: this translation unit is compiled into the Rust runtime crate
 * (src/compiler_rust/runtime/build.rs) and into the core-C archives
 * (native_project/tools.rs, backend/runtime_compiler.spl), so it must not
 * reference runtime.h types or any other rt_* symbol. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#if defined(__APPLE__) && !defined(_DARWIN_C_SOURCE)
#define _DARWIN_C_SOURCE
#endif

#include "runtime_process_tree.h"

#include <errno.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#if defined(_WIN32)
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#include <windows.h>
#else
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
#endif

#if defined(__linux__)
#include <dirent.h>
#include <sys/prctl.h>
#endif
#if defined(__APPLE__)
#include <libproc.h>
#endif
#if defined(__FreeBSD__)
#include <sys/param.h>
#include <sys/procctl.h>
#include <sys/sysctl.h>
#include <sys/user.h>
#endif

/* The owner exists on exactly these hosts. */
#if defined(__linux__) || defined(__APPLE__) || defined(__FreeBSD__)
#define RT_PTREE_HAVE_OWNER 1
#else
#define RT_PTREE_HAVE_OWNER 0
#endif

int64_t rt_process_tree_support(void) {
    return RT_PTREE_HAVE_OWNER ? 0 : RT_PTREE_UNSUPPORTED;
}

/* ------------------------------------------------------------------------- */
/* Process enumeration: fills *out_pids / *out_sids (malloc'd, caller frees)  */
/* with every live process and its session id. Returns count or -errno.      */
/* ------------------------------------------------------------------------- */
#if RT_PTREE_HAVE_OWNER

typedef struct {
    pid_t pid;
    pid_t sid;
} ptree_entry;

static int64_t ptree_enumerate(ptree_entry** out, size_t* out_count) {
    *out = NULL;
    *out_count = 0;
#if defined(__linux__)
    DIR* proc = opendir("/proc");
    if (!proc) return -(int64_t)errno;
    size_t cap = 256, n = 0;
    ptree_entry* list = (ptree_entry*)malloc(cap * sizeof(*list));
    if (!list) {
        closedir(proc);
        return -ENOMEM;
    }
    struct dirent* entry;
    while ((entry = readdir(proc)) != NULL) {
        const char* name = entry->d_name;
        if (name[0] < '1' || name[0] > '9') continue;
        char* end = NULL;
        errno = 0;
        unsigned long long value = strtoull(name, &end, 10);
        if (errno != 0 || !end || *end != '\0' || value == 0 || value > INT32_MAX) continue;
        pid_t pid = (pid_t)value;
        pid_t sid = getsid(pid); /* ESRCH when it exited between readdir and here */
        if (sid < 0) continue;
        if (n == cap) {
            size_t new_cap = cap * 2;
            ptree_entry* grown = (ptree_entry*)realloc(list, new_cap * sizeof(*list));
            if (!grown) {
                free(list);
                closedir(proc);
                return -ENOMEM;
            }
            list = grown;
            cap = new_cap;
        }
        list[n].pid = pid;
        list[n].sid = sid;
        n++;
    }
    closedir(proc);
    *out = list;
    *out_count = n;
    return (int64_t)n;
#elif defined(__APPLE__)
    /* proc_listallpids(NULL, 0) answers the current count; processes may be
     * created before the second call, so leave headroom and retry on growth. */
    for (int attempt = 0; attempt < 8; attempt++) {
        int count = proc_listallpids(NULL, 0);
        if (count <= 0) return errno ? -(int64_t)errno : -EIO;
        size_t cap = (size_t)count + 256;
        pid_t* pids = (pid_t*)calloc(cap, sizeof(pid_t));
        if (!pids) return -ENOMEM;
        int filled = proc_listallpids(pids, (int)(cap * sizeof(pid_t)));
        if (filled < 0) {
            int saved = errno;
            free(pids);
            return saved ? -(int64_t)saved : -EIO;
        }
        if ((size_t)filled >= cap) { /* table grew past our headroom: retry */
            free(pids);
            continue;
        }
        ptree_entry* list = (ptree_entry*)malloc(((size_t)filled + 1) * sizeof(*list));
        if (!list) {
            free(pids);
            return -ENOMEM;
        }
        size_t n = 0;
        for (int i = 0; i < filled; i++) {
            if (pids[i] <= 0) continue;
            pid_t sid = getsid(pids[i]);
            if (sid < 0) continue;
            list[n].pid = pids[i];
            list[n].sid = sid;
            n++;
        }
        free(pids);
        *out = list;
        *out_count = n;
        return (int64_t)n;
    }
    return -EAGAIN;
#elif defined(__FreeBSD__)
    int mib[4] = {CTL_KERN, KERN_PROC, KERN_PROC_PROC, 0};
    for (int attempt = 0; attempt < 8; attempt++) {
        size_t size = 0;
        if (sysctl(mib, 3, NULL, &size, NULL, 0) != 0) return -(int64_t)errno;
        size += size / 8 + 4096; /* headroom for processes created meanwhile */
        struct kinfo_proc* procs = (struct kinfo_proc*)malloc(size);
        if (!procs) return -ENOMEM;
        if (sysctl(mib, 3, procs, &size, NULL, 0) != 0) {
            int saved = errno;
            free(procs);
            if (saved == ENOMEM) continue;
            return -(int64_t)saved;
        }
        size_t count = size / sizeof(struct kinfo_proc);
        ptree_entry* list = (ptree_entry*)malloc((count + 1) * sizeof(*list));
        if (!list) {
            free(procs);
            return -ENOMEM;
        }
        size_t n = 0;
        for (size_t i = 0; i < count; i++) {
            if (procs[i].ki_pid <= 0) continue;
            list[n].pid = procs[i].ki_pid;
            list[n].sid = procs[i].ki_sid;
            n++;
        }
        free(procs);
        *out = list;
        *out_count = n;
        return (int64_t)n;
    }
    return -EAGAIN;
#else
    return RT_PTREE_UNSUPPORTED;
#endif
}

static void ptree_sleep_ms(int ms) {
    struct timespec ts;
    ts.tv_sec = ms / 1000;
    ts.tv_nsec = (long)(ms % 1000) * 1000000L;
    while (nanosleep(&ts, &ts) != 0 && errno == EINTR) {}
}

static int64_t ptree_monotonic_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Exit status in the rt_process_wait convention. */
static int64_t ptree_status_code(int status) {
    if (WIFEXITED(status)) return (int64_t)WEXITSTATUS(status);
    if (WIFSIGNALED(status)) return -(128 + (int64_t)WTERMSIG(status));
    return -1;
}

#endif /* RT_PTREE_HAVE_OWNER */

/* ------------------------------------------------------------------------- */
/* Spawn                                                                      */
/* ------------------------------------------------------------------------- */
int64_t rt_process_spawn_session(const char* cmd, const char** args, int64_t arg_count) {
#if !RT_PTREE_HAVE_OWNER
    (void)cmd; (void)args; (void)arg_count;
    return RT_PTREE_UNSUPPORTED;
#else
    if (!cmd || !*cmd || arg_count < 0 || (arg_count > 0 && !args)) return -EINVAL;
    if ((uint64_t)arg_count > (uint64_t)INT32_MAX) return -E2BIG;
    for (int64_t i = 0; i < arg_count; i++) {
        if (!args[i]) return -EINVAL;
    }
    /* argv is built in the parent: nothing may allocate between fork and exec
     * in a multithreaded parent. */
    char** argv = (char**)calloc((size_t)arg_count + 2, sizeof(char*));
    if (!argv) return -ENOMEM;
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];

    /* The child reports an exec failure through a CLOEXEC pipe, so the caller
     * gets -errno instead of a pid that exits 127 a moment later. */
    int err_pipe[2];
#if defined(__linux__) || defined(__FreeBSD__)
    /* Atomic: no window in which a concurrent fork+exec elsewhere in the
     * process inherits the pipe. (macOS defines O_CLOEXEC but has no pipe2.) */
    if (pipe2(err_pipe, O_CLOEXEC) != 0) {
        int saved = errno;
        free(argv);
        return -(int64_t)saved;
    }
#else
    if (pipe(err_pipe) != 0) {
        int saved = errno;
        free(argv);
        return -(int64_t)saved;
    }
    if (fcntl(err_pipe[0], F_SETFD, FD_CLOEXEC) != 0 || fcntl(err_pipe[1], F_SETFD, FD_CLOEXEC) != 0) {
        int saved = errno;
        close(err_pipe[0]);
        close(err_pipe[1]);
        free(argv);
        return -(int64_t)saved;
    }
#endif

    fflush(stdout);
    fflush(stderr);
    pid_t pid = fork();
    if (pid < 0) {
        int saved = errno;
        close(err_pipe[0]);
        close(err_pipe[1]);
        free(argv);
        return -(int64_t)saved;
    }
    if (pid == 0) {
        /* === CHILD: async-signal-safe calls only === */
        close(err_pipe[0]);
        int failure = 0;
        if (setsid() < 0) {
            failure = errno ? errno : EPERM;
        } else {
            sigset_t none;
            sigemptyset(&none);
            (void)sigprocmask(SIG_SETMASK, &none, NULL);
            (void)signal(SIGINT, SIG_DFL);
            (void)signal(SIGTERM, SIG_DFL);
            (void)signal(SIGPIPE, SIG_DFL);
            (void)signal(SIGHUP, SIG_DFL);
            execvp(cmd, argv);
            failure = errno ? errno : ENOENT;
        }
        int32_t code = (int32_t)failure;
        const char* bytes = (const char*)&code;
        size_t left = sizeof(code);
        while (left > 0) {
            ssize_t wrote = write(err_pipe[1], bytes, left);
            if (wrote < 0) {
                if (errno == EINTR) continue;
                break;
            }
            bytes += wrote;
            left -= (size_t)wrote;
        }
        _exit(127);
    }
    /* === PARENT === */
    close(err_pipe[1]);
    free(argv);
    int32_t child_errno = 0;
    size_t got = 0;
    while (got < sizeof(child_errno)) {
        ssize_t n = read(err_pipe[0], (char*)&child_errno + got, sizeof(child_errno) - got);
        if (n < 0) {
            if (errno == EINTR) continue;
            break; /* treat as exec'd: the pipe is gone */
        }
        if (n == 0) break; /* EOF: exec succeeded (CLOEXEC closed the write end) */
        got += (size_t)n;
    }
    close(err_pipe[0]);
    if (got == sizeof(child_errno) && child_errno != 0) {
        int status = 0;
        while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
        return -(int64_t)child_errno;
    }
    return (int64_t)pid;
#endif
}

/* ------------------------------------------------------------------------- */
/* Wait / liveness                                                            */
/* ------------------------------------------------------------------------- */
int64_t rt_process_session_wait(int64_t pid, int64_t timeout_ms) {
#if !RT_PTREE_HAVE_OWNER
    (void)pid; (void)timeout_ms;
    return RT_PTREE_UNSUPPORTED;
#else
    if (pid <= 1 || pid > INT32_MAX) return -1;
    int status = 0;
    if (timeout_ms <= 0) {
        pid_t waited;
        do {
            waited = waitpid((pid_t)pid, &status, 0);
        } while (waited < 0 && errno == EINTR);
        if (waited < 0) return -1;
        return ptree_status_code(status);
    }
    int64_t deadline = ptree_monotonic_ms() + timeout_ms;
    int sleep_ms = 1;
    for (;;) {
        pid_t waited = waitpid((pid_t)pid, &status, WNOHANG);
        if (waited == (pid_t)pid) return ptree_status_code(status);
        if (waited < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        if (ptree_monotonic_ms() >= deadline) return -2;
        ptree_sleep_ms(sleep_ms);
        if (sleep_ms < 10) sleep_ms++;
    }
#endif
}

int64_t rt_process_session_is_running(int64_t pid) {
#if !RT_PTREE_HAVE_OWNER
    (void)pid;
    return RT_PTREE_UNSUPPORTED;
#else
    if (pid <= 1 || pid > INT32_MAX) return 0;
    /* WNOWAIT leaves the zombie for rt_process_session_wait to reap. */
    siginfo_t info;
    memset(&info, 0, sizeof(info));
    int rc;
    do {
        rc = waitid(P_PID, (id_t)pid, &info, WEXITED | WNOHANG | WNOWAIT);
    } while (rc < 0 && errno == EINTR);
    if (rc == 0) {
        if (info.si_pid == (pid_t)pid) return 0; /* exited, reapable */
        return 1;                                 /* our child, still running */
    }
    if (errno == ECHILD) {
        /* Not our child (already reaped, or spawned by another owner). */
        return (kill((pid_t)pid, 0) == 0 || errno == EPERM) ? 1 : 0;
    }
    return 0;
#endif
}

/* ------------------------------------------------------------------------- */
/* Kill                                                                       */
/* ------------------------------------------------------------------------- */
int64_t rt_process_kill_session(int64_t sid, int32_t signo) {
#if !RT_PTREE_HAVE_OWNER
    (void)sid; (void)signo;
    return RT_PTREE_UNSUPPORTED;
#else
    if (sid <= 1 || sid > INT32_MAX || signo < 0) return -EINVAL;
    /* Never our own session: that would take the runner down with the tree. */
    if ((pid_t)sid == getsid(0)) return -EINVAL;
    ptree_entry* list = NULL;
    size_t count = 0;
    int64_t rc = ptree_enumerate(&list, &count);
    if (rc < 0) return rc;
    pid_t self = getpid();
    int64_t signalled = 0;
    for (size_t i = 0; i < count; i++) {
        if (list[i].sid != (pid_t)sid || list[i].pid == self || list[i].pid <= 1) continue;
        if (kill(list[i].pid, signo) == 0) signalled++;
        /* ESRCH: exited since enumeration; EPERM: not ours to signal. Neither
         * is an enumeration failure, so the pass continues. */
    }
    free(list);
    return signalled;
#endif
}

int64_t rt_process_kill_tree(int64_t pid) {
#if !RT_PTREE_HAVE_OWNER
    (void)pid;
    return RT_PTREE_UNSUPPORTED;
#else
    if (pid <= 1 || pid > INT32_MAX) return -EINVAL;
    pid_t sid = getsid((pid_t)pid);
    if (sid >= 0 && sid != (pid_t)pid) {
        /* Alive, but not a session leader: not spawned by this owner. Refuse
         * rather than kill a session that belongs to someone else. */
        return RT_PTREE_NOT_SESSION_LEADER;
    }
    /* sid < 0 (ESRCH): the leader already exited. Its orphans still carry
     * session id == pid, so the sweep below is still meaningful. */
    int64_t rc = rt_process_kill_session(pid, SIGKILL);
    if (rc < 0) return rc;

    /* Reap the leader if it is our child. SIGKILL is not deferrable, so this
     * completes quickly; the bound only guards against a stopped/traced leader. */
    int64_t deadline = ptree_monotonic_ms() + 2000;
    int leader_gone = 0; /* reaped here, or no longer waitable by us */
    for (;;) {
        int status = 0;
        pid_t waited = waitpid((pid_t)pid, &status, WNOHANG);
        if (waited == (pid_t)pid) { leader_gone = 1; break; }
        if (waited < 0) {
            if (errno == EINTR) continue;
            if (errno == ECHILD) leader_gone = 1;
            break; /* ECHILD: not our child, or already reaped */
        }
        if (ptree_monotonic_ms() >= deadline) break;
        ptree_sleep_ms(1);
    }

    /* Second sweep: a member may have forked between enumeration and its own
     * SIGKILL; the new process inherited the session and is caught here. */
    ptree_sleep_ms(5);
    rc = rt_process_kill_session(pid, SIGKILL);
    if (rc < 0) return leader_gone ? RT_PTREE_SWEEP_FAILED_AFTER_REAP : rc;
    return 0;
#endif
}

/* ------------------------------------------------------------------------- */
/* Parent-death signal (child side)                                           */
/* ------------------------------------------------------------------------- */
int64_t rt_child_set_pdeathsig(int32_t signo) {
#if defined(__linux__)
    if (prctl(PR_SET_PDEATHSIG, (unsigned long)signo, 0, 0, 0) != 0) return -(int64_t)errno;
    return 0;
#elif defined(__FreeBSD__)
    int sig = (int)signo;
    if (procctl(P_PID, 0, PROC_PDEATHSIG_CTL, &sig) != 0) return -(int64_t)errno;
    return 0;
#else
    (void)signo;
    return RT_PTREE_UNSUPPORTED;
#endif
}

/* ------------------------------------------------------------------------- */
/* Birth identity                                                             */
/* ------------------------------------------------------------------------- */
int64_t rt_proc_start_time(int64_t pid) {
    if (pid <= 0) return 0;
#if defined(_WIN32)
    if (pid > (int64_t)UINT32_MAX) return 0;
    HANDLE process = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, FALSE, (DWORD)pid);
    if (!process) return 0;
    FILETIME created, exited, kernel, user;
    BOOL ok = GetProcessTimes(process, &created, &exited, &kernel, &user);
    CloseHandle(process);
    if (!ok) return 0;
    ULARGE_INTEGER value;
    value.LowPart = created.dwLowDateTime;
    value.HighPart = created.dwHighDateTime;
    return value.QuadPart > (ULONGLONG)INT64_MAX ? 0 : (int64_t)value.QuadPart;
#elif defined(__linux__)
    char path[64], line[2048];
    snprintf(path, sizeof(path), "/proc/%lld/stat", (long long)pid);
    FILE* file = fopen(path, "r");
    if (!file) return 0;
    if (!fgets(line, sizeof(line), file)) {
        fclose(file);
        return 0;
    }
    fclose(file);
    /* The comm field may contain spaces and parentheses; skip past its ')'. */
    char* cursor = strrchr(line, ')');
    if (!cursor || cursor[1] != ' ') return 0;
    cursor += 2;
    for (int field = 3; field < 22; field++) {
        cursor = strchr(cursor, ' ');
        if (!cursor) return 0;
        cursor++;
    }
    errno = 0;
    char* end = NULL;
    unsigned long long value = strtoull(cursor, &end, 10);
    return errno == 0 && end != cursor && value <= (unsigned long long)INT64_MAX ? (int64_t)value : 0;
#elif defined(__APPLE__)
    if (pid > INT32_MAX) return 0;
    struct proc_bsdinfo info;
    int bytes = proc_pidinfo((int)pid, PROC_PIDTBSDINFO, 0, &info, sizeof(info));
    if (bytes != (int)sizeof(info)) return 0;
    uint64_t seconds = (uint64_t)info.pbi_start_tvsec;
    uint64_t micros = (uint64_t)info.pbi_start_tvusec;
    if (seconds > (uint64_t)INT64_MAX / 1000000ULL) return 0;
    return (int64_t)(seconds * 1000000ULL + micros);
#elif defined(__FreeBSD__)
    if (pid > INT32_MAX) return 0;
    int mib[4] = {CTL_KERN, KERN_PROC, KERN_PROC_PID, (int)pid};
    struct kinfo_proc info;
    size_t size = sizeof(info);
    if (sysctl(mib, 4, &info, &size, NULL, 0) != 0 || size != sizeof(info)) return 0;
    if (info.ki_pid != (pid_t)pid) return 0;
    uint64_t seconds = (uint64_t)info.ki_start.tv_sec;
    uint64_t micros = (uint64_t)info.ki_start.tv_usec;
    if (seconds > (uint64_t)INT64_MAX / 1000000ULL) return 0;
    return (int64_t)(seconds * 1000000ULL + micros);
#else
    return 0;
#endif
}
