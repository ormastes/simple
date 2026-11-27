/* Privilege drop + privilege-dropping spawn. Contract: runtime_privdrop_v1.h.
 * Twin: src/compiler_rust/runtime/src/value/sffi/privdrop_v1.rs (same steps,
 * same codes, same order). */
#if !defined(_WIN32)
/* Effective when this unit is compiled on its own; under the runtime.c unity
 * build the including TU has already chosen the same feature macros. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#ifndef _DEFAULT_SOURCE
#define _DEFAULT_SOURCE
#endif
#endif
#include "runtime_privdrop_v1.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#define RT_PRIVDROP_ERR(step, e) (-(((int64_t)(step) << 16) + (int64_t)(e)))
#define RT_PRIVCRED_MAGIC  0x5052495643524544ULL /* "PRIVCRED" */
#define RT_PRIVSPAWN_MAGIC 0x5052495653504e57ULL /* "PRIVSPNW" */
#define RT_PRIVDROP_MAX_GROUPS 4096
#define RT_PRIVDROP_MAX_ITEMS  65536

#if (defined(__linux__) || defined(__FreeBSD__)) && !defined(_WIN32)
#include <unistd.h>
#include <fcntl.h>
#include <grp.h>
#include <pwd.h>
#include <signal.h>
#include <pthread.h>
#include <stdatomic.h>
#include <sys/types.h>
#include <sys/wait.h>
#if defined(__linux__)
#include <sys/syscall.h>
#endif

/* glibc hides setres*id / getres*id behind _GNU_SOURCE; declare them so this
 * unit is independent of which feature macros the including TU chose. */
extern int setresuid(uid_t, uid_t, uid_t);
extern int setresgid(gid_t, gid_t, gid_t);
extern int getresuid(uid_t*, uid_t*, uid_t*);
extern int getresgid(gid_t*, gid_t*, gid_t*);

typedef struct RtPrivCred {
    uint64_t magic;
    uid_t uid;
    gid_t gid;
    int ngroups;
    gid_t groups[RT_PRIVDROP_MAX_GROUPS];
} RtPrivCred;

typedef struct RtPrivSpawn {
    uint64_t magic;
    char* path;
    char** argv;
    int64_t argc;
    char** envp;
    int64_t envc;
    RtPrivCred cred;
    int has_cred;
    int new_session;
    int procs_dir_fd;
    char* procs_name;
} RtPrivSpawn;

/* Live-handle registry: a handle is dereferenced only if it is currently
 * registered, so a forged, stale or double-freed integer is refused instead
 * of being read. Lockless: slots are claimed and released with CAS. */
#define RT_PRIVDROP_LIVE_SLOTS 256
/* Child signal-reset bound: Linux has 64 signals, FreeBSD 128 (its NSIG is
 * only 32); numbers the host lacks make sigaction fail and are skipped. */
#define RT_PRIVDROP_SIG_BOUND 129
/* One registry per handle kind: a credential is never live as a spawn. */
static _Atomic uintptr_t rt_privcred_live[RT_PRIVDROP_LIVE_SLOTS];
static _Atomic uintptr_t rt_privspawn_live[RT_PRIVDROP_LIVE_SLOTS];

static int rt_privdrop_register(_Atomic uintptr_t* live, void* p) {
    for (int i = 0; i < RT_PRIVDROP_LIVE_SLOTS; i++) {
        uintptr_t empty = 0;
        if (atomic_compare_exchange_strong(&live[i], &empty, (uintptr_t)p)) return 1;
    }
    return 0;
}

static int rt_privdrop_is_live(_Atomic uintptr_t* live, int64_t h) {
    if (h <= 0) return 0;
    for (int i = 0; i < RT_PRIVDROP_LIVE_SLOTS; i++)
        if (atomic_load(&live[i]) == (uintptr_t)h) return 1;
    return 0;
}

/* Unregister before free; only the caller that wins the CAS may free. */
static int rt_privdrop_unregister(_Atomic uintptr_t* live, void* p) {
    for (int i = 0; i < RT_PRIVDROP_LIVE_SLOTS; i++) {
        uintptr_t want = (uintptr_t)p;
        if (atomic_compare_exchange_strong(&live[i], &want, 0)) return 1;
    }
    return 0;
}

static RtPrivCred* rt_privcred_get(int64_t h) {
    if (!rt_privdrop_is_live(rt_privcred_live, h)) return NULL;
    RtPrivCred* c = (RtPrivCred*)(intptr_t)h;
    return c->magic == RT_PRIVCRED_MAGIC ? c : NULL;
}

static RtPrivSpawn* rt_privspawn_get(int64_t h) {
    if (!rt_privdrop_is_live(rt_privspawn_live, h)) return NULL;
    RtPrivSpawn* s = (RtPrivSpawn*)(intptr_t)h;
    return s->magic == RT_PRIVSPAWN_MAGIC ? s : NULL;
}

/* NUL-free copy of a byte span, or NULL. */
static char* rt_privdrop_cstr(const uint8_t* p, uint64_t n) {
    if (p == NULL && n != 0) return NULL;
    if (n > 65536 || (n > 0 && memchr(p, 0, (size_t)n) != NULL)) return NULL;
    char* out = (char*)malloc((size_t)n + 1);
    if (out == NULL) return NULL;
    if (n) memcpy(out, p, (size_t)n);
    out[n] = 0;
    return out;
}

int64_t rt_privcred_new_v1(int64_t uid, int64_t gid) {
    /* uid 0 and gid 0 are refused: a root target cannot pass the
     * "root is unrecoverable" verification, so reject it up front. */
    if (uid <= 0 || gid <= 0 || uid > 0x7fffffff || gid > 0x7fffffff)
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    RtPrivCred* c = (RtPrivCred*)calloc(1, sizeof(RtPrivCred));
    if (c == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, ENOMEM);
    c->magic = RT_PRIVCRED_MAGIC;
    c->uid = (uid_t)uid;
    c->gid = (gid_t)gid;
    c->ngroups = 0;
    if (!rt_privdrop_register(rt_privcred_live, c)) { free(c); return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, EMFILE); }
    return (int64_t)(intptr_t)c;
}

/* Parent-side resolution: getpwnam_r + getgrouplist. initgroups() is never
 * used, so no NSS work can run in a forked child. */
int64_t rt_privcred_from_user_v1(const uint8_t* name, uint64_t name_len) {
    char* user = rt_privdrop_cstr(name, name_len);
    if (user == NULL || user[0] == 0) {
        free(user);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    }
    struct passwd pw;
    struct passwd* found = NULL;
    char buf[16384];
    int rc = getpwnam_r(user, &pw, buf, sizeof buf, &found);
    if (rc != 0 || found == NULL) {
        free(user);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_LOOKUP, rc != 0 ? rc : ENOENT);
    }
    int64_t h = rt_privcred_new_v1((int64_t)pw.pw_uid, (int64_t)pw.pw_gid);
    if (h < 0) { free(user); return h; }
    RtPrivCred* c = rt_privcred_get(h);
    int n = RT_PRIVDROP_MAX_GROUPS;
    if (getgrouplist(user, pw.pw_gid, c->groups, &n) < 0) {
        free(user);
        rt_privcred_free_v1(h);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_LOOKUP, E2BIG);
    }
    c->ngroups = n;
    free(user);
    return h;
}

int64_t rt_privcred_add_group_v1(int64_t cred, int64_t gid) {
    RtPrivCred* c = rt_privcred_get(cred);
    if (c == NULL || gid < 0 || gid > 0x7fffffff) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    if (c->ngroups >= RT_PRIVDROP_MAX_GROUPS) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, E2BIG);
    c->groups[c->ngroups++] = (gid_t)gid;
    return 0;
}

int64_t rt_privcred_uid_v1(int64_t cred) {
    RtPrivCred* c = rt_privcred_get(cred);
    return c ? (int64_t)c->uid : RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
}

int64_t rt_privcred_gid_v1(int64_t cred) {
    RtPrivCred* c = rt_privcred_get(cred);
    return c ? (int64_t)c->gid : RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
}

int64_t rt_privcred_group_count_v1(int64_t cred) {
    RtPrivCred* c = rt_privcred_get(cred);
    return c ? (int64_t)c->ngroups : RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
}

int64_t rt_privcred_group_at_v1(int64_t cred, int64_t index) {
    RtPrivCred* c = rt_privcred_get(cred);
    if (c == NULL || index < 0 || index >= c->ngroups) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    return (int64_t)c->groups[index];
}

int64_t rt_privcred_free_v1(int64_t cred) {
    RtPrivCred* c = rt_privcred_get(cred);
    if (c == NULL || !rt_privdrop_unregister(rt_privcred_live, c)) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    c->magic = 0;
    free(c);
    return 0;
}

/* The fixed drop sequence. Async-signal-safe only: it runs in forked
 * children as well as in-process. */
static int64_t rt_privdrop_apply(const RtPrivCred* c) {
    if (setgroups((size_t)c->ngroups, c->groups) != 0) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_SETGROUPS, errno);
    if (setresgid(c->gid, c->gid, c->gid) != 0) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_SETGID, errno);
    if (setresuid(c->uid, c->uid, c->uid) != 0) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_SETUID, errno);
    uid_t ru, eu, su;
    gid_t rg, eg, sg;
    if (getresuid(&ru, &eu, &su) != 0 || getresgid(&rg, &eg, &sg) != 0)
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, errno);
    if (ru != c->uid || eu != c->uid || su != c->uid || rg != c->gid || eg != c->gid || sg != c->gid)
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, EPERM);
    gid_t now[RT_PRIVDROP_MAX_GROUPS];
    int n = getgroups(RT_PRIVDROP_MAX_GROUPS, now);
    if (n < 0) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, errno);
    /* Set equality, modulo the primary gid: Linux returns the list sorted and
     * FreeBSD < 14 keeps the egid in slot 0. */
    for (int i = 0; i < n; i++) {
        int ok = now[i] == c->gid;
        for (int j = 0; !ok && j < c->ngroups; j++) ok = now[i] == c->groups[j];
        if (!ok) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, EPERM);
    }
    for (int j = 0; j < c->ngroups; j++) {
        int ok = 0;
        for (int i = 0; !ok && i < n; i++) ok = now[i] == c->groups[j];
        if (!ok) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, EPERM);
    }
    /* Regaining root must be impossible. */
    if (setresuid(0, 0, 0) == 0 || setresgid(0, 0, 0) == 0 || setuid(0) == 0)
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_VERIFY, EPERM);
    return 0;
}

int64_t rt_privcred_drop_self_v1(int64_t cred) {
    RtPrivCred* c = rt_privcred_get(cred);
    if (c == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    return rt_privdrop_apply(c);
}

int64_t rt_privspawn_new_v1(const uint8_t* path, uint64_t path_len) {
    char* p = rt_privdrop_cstr(path, path_len);
    if (p == NULL || p[0] != '/') { free(p); return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL); }
    RtPrivSpawn* s = (RtPrivSpawn*)calloc(1, sizeof(RtPrivSpawn));
    char** argv = (char**)calloc(2, sizeof(char*));
    char** envp = (char**)calloc(1, sizeof(char*));
    if (s == NULL || argv == NULL || envp == NULL) {
        free(p); free(s); free(argv); free(envp);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, ENOMEM);
    }
    s->magic = RT_PRIVSPAWN_MAGIC;
    s->path = p;
    argv[0] = strdup(p);
    if (argv[0] == NULL) { free(p); free(s); free(argv); free(envp); return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, ENOMEM); }
    s->argv = argv;
    s->argc = 1;
    s->envp = envp;
    s->envc = 0;
    s->procs_dir_fd = -1;
    if (!rt_privdrop_register(rt_privspawn_live, s)) {
        free(argv[0]); free(p); free(s); free(argv); free(envp);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, EMFILE);
    }
    return (int64_t)(intptr_t)s;
}

static int64_t rt_privspawn_push(char*** list, int64_t* count, const uint8_t* p, uint64_t n, int need_eq) {
    if (*count >= RT_PRIVDROP_MAX_ITEMS) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, E2BIG);
    char* item = rt_privdrop_cstr(p, n);
    if (item == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    if (need_eq && (item[0] == '=' || strchr(item, '=') == NULL)) { free(item); return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL); }
    char** grown = (char**)realloc(*list, (size_t)(*count + 2) * sizeof(char*));
    if (grown == NULL) { free(item); return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_NOMEM, ENOMEM); }
    grown[*count] = item;
    grown[*count + 1] = NULL;
    *list = grown;
    *count += 1;
    return 0;
}

int64_t rt_privspawn_arg_v1(int64_t spawn, const uint8_t* arg, uint64_t arg_len) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    return rt_privspawn_push(&s->argv, &s->argc, arg, arg_len, 0);
}

int64_t rt_privspawn_env_v1(int64_t spawn, const uint8_t* entry, uint64_t entry_len) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    return rt_privspawn_push(&s->envp, &s->envc, entry, entry_len, 1);
}

int64_t rt_privspawn_cred_v1(int64_t spawn, int64_t cred) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    RtPrivCred* c = rt_privcred_get(cred);
    if (s == NULL || c == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    s->cred = *c; /* copied: the spawn never aliases the caller's handle */
    s->has_cred = 1;
    return 0;
}

int64_t rt_privspawn_join_procs_v1(int64_t spawn, int64_t dir_fd, const uint8_t* name, uint64_t name_len) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL || dir_fd < 0 || dir_fd > 0x7fffffff) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    char* leaf = rt_privdrop_cstr(name, name_len);
    /* a single path component: no '/', not '.' or '..' */
    if (leaf == NULL || leaf[0] == 0 || strchr(leaf, '/') != NULL || strcmp(leaf, ".") == 0 || strcmp(leaf, "..") == 0) {
        free(leaf);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    }
    free(s->procs_name);
    s->procs_name = leaf;
    s->procs_dir_fd = (int)dir_fd;
    return 0;
}

int64_t rt_privspawn_new_session_v1(int64_t spawn) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    s->new_session = 1;
    return 0;
}

static void rt_privspawn_report(int fd, int64_t code) {
    const char* p = (const char*)&code;
    size_t left = sizeof code;
    while (left > 0) {
        ssize_t w = write(fd, p, left);
        if (w < 0 && errno == EINTR) continue;
        if (w <= 0) break;
        p += w;
        left -= (size_t)w;
    }
    _exit(127);
}

/* Mark every inherited descriptor >= 3 close-on-exec (the error pipe too). */
static int rt_privspawn_cloexec_from3(void) {
#if defined(__linux__) && defined(SYS_close_range)
    if (syscall(SYS_close_range, 3U, ~0U, 4U /* CLOSE_RANGE_CLOEXEC */) == 0) return 0;
#endif
    long max = sysconf(_SC_OPEN_MAX);
    if (max < 0 || max > 1048576) max = 1048576;
    for (long fd = 3; fd < max; fd++) {
        int flags = fcntl((int)fd, F_GETFD);
        if (flags >= 0 && fcntl((int)fd, F_SETFD, flags | FD_CLOEXEC) != 0) return -1;
    }
    return 0;
}

int64_t rt_privspawn_run_v1(int64_t spawn) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL || !s->has_cred) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    int pipefd[2];
#if defined(__linux__) || defined(__FreeBSD__)
    if (pipe2(pipefd, O_CLOEXEC) != 0) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_PIPE, errno);
#endif
    /* Block every signal across fork so no parent handler can run in the
     * still-privileged child before its dispositions are reset. */
    sigset_t all, saved;
    sigfillset(&all);
    pthread_sigmask(SIG_SETMASK, &all, &saved);
    pid_t pid = fork();
    if (pid < 0) {
        int e = errno;
        pthread_sigmask(SIG_SETMASK, &saved, NULL);
        close(pipefd[0]); close(pipefd[1]);
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_FORK, e);
    }
    if (pid == 0) {
        /* Child: async-signal-safe calls only, in the fixed order. Reset
         * every caught handler (and SIGPIPE) to default, then unblock. */
        for (int sig = 1; sig < RT_PRIVDROP_SIG_BOUND; sig++) {
            if (sig == SIGKILL || sig == SIGSTOP) continue;
            struct sigaction old;
            if (sigaction(sig, NULL, &old) != 0) continue;
            if (sig == SIGPIPE || (old.sa_handler != SIG_IGN && old.sa_handler != SIG_DFL)) {
                struct sigaction dfl;
                memset(&dfl, 0, sizeof dfl);
                dfl.sa_handler = SIG_DFL;
                sigemptyset(&dfl.sa_mask);
                sigaction(sig, &dfl, NULL);
            }
        }
        sigset_t none;
        sigemptyset(&none);
        sigprocmask(SIG_SETMASK, &none, NULL);
        if (s->new_session && setsid() < 0) rt_privspawn_report(pipefd[1], RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_SETSID, errno));
        if (s->procs_name != NULL) {
            int fd = openat(s->procs_dir_fd, s->procs_name, O_WRONLY | O_NOFOLLOW | O_CLOEXEC | O_NOCTTY);
            if (fd < 0) rt_privspawn_report(pipefd[1], RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_CGROUP_OPEN, errno));
            char digits[24];
            int len = 0;
            char rev[24];
            long v = (long)getpid();
            do { rev[len++] = (char)('0' + (v % 10)); v /= 10; } while (v > 0);
            for (int i = 0; i < len; i++) digits[i] = rev[len - 1 - i];
            ssize_t w = write(fd, digits, (size_t)len);
            int e = errno;
            close(fd);
            if (w != len) rt_privspawn_report(pipefd[1], RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_CGROUP_WRITE, w < 0 ? e : EIO));
        }
        if (rt_privspawn_cloexec_from3() != 0) rt_privspawn_report(pipefd[1], RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_FDS, errno));
        int64_t drop = rt_privdrop_apply(&s->cred);
        if (drop != 0) rt_privspawn_report(pipefd[1], drop);
        execve(s->path, s->argv, s->envp);
        rt_privspawn_report(pipefd[1], RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_EXEC, errno));
    }
    pthread_sigmask(SIG_SETMASK, &saved, NULL);
    close(pipefd[1]);
    int64_t code = 0;
    size_t got = 0;
    while (got < sizeof code) {
        ssize_t r = read(pipefd[0], ((char*)&code) + got, sizeof code - got);
        if (r < 0 && errno == EINTR) continue;
        if (r <= 0) break;
        got += (size_t)r;
    }
    close(pipefd[0]);
    if (got == 0) return (int64_t)pid; /* exec succeeded: pipe closed by CLOEXEC */
    int status = 0;
    while (waitpid(pid, &status, 0) < 0 && errno == EINTR) {}
    return got == sizeof code && code < 0 ? code : RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_EXEC, EIO);
}

int64_t rt_privspawn_wait_v1(int64_t pid) {
    if (pid <= 0 || pid > 0x7fffffff) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    int status = 0;
    for (;;) {
        pid_t r = waitpid((pid_t)pid, &status, 0);
        if (r == (pid_t)pid) return (int64_t)(uint32_t)status;
        if (r < 0 && errno == EINTR) continue;
        return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_WAIT, r < 0 ? errno : ECHILD);
    }
}

int64_t rt_privspawn_free_v1(int64_t spawn) {
    RtPrivSpawn* s = rt_privspawn_get(spawn);
    if (s == NULL || !rt_privdrop_unregister(rt_privspawn_live, s)) return RT_PRIVDROP_ERR(RT_PRIVDROP_STEP_INVALID, EINVAL);
    for (int64_t i = 0; i < s->argc; i++) free(s->argv[i]);
    for (int64_t i = 0; i < s->envc; i++) free(s->envp[i]);
    free(s->argv);
    free(s->envp);
    free(s->path);
    free(s->procs_name);
    s->magic = 0;
    free(s);
    return 0;
}

#else /* no POSIX credentials on this host (Windows, others): typed unsupported */

#define RT_PRIVDROP_UNSUPPORTED (-(((int64_t)RT_PRIVDROP_STEP_UNSUPPORTED) << 16))
int64_t rt_privcred_new_v1(int64_t uid, int64_t gid) { (void)uid; (void)gid; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_from_user_v1(const uint8_t* n, uint64_t l) { (void)n; (void)l; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_add_group_v1(int64_t c, int64_t g) { (void)c; (void)g; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_uid_v1(int64_t c) { (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_gid_v1(int64_t c) { (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_group_count_v1(int64_t c) { (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_group_at_v1(int64_t c, int64_t i) { (void)c; (void)i; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_drop_self_v1(int64_t c) { (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privcred_free_v1(int64_t c) { (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_new_v1(const uint8_t* p, uint64_t l) { (void)p; (void)l; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_arg_v1(int64_t s, const uint8_t* p, uint64_t l) { (void)s; (void)p; (void)l; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_env_v1(int64_t s, const uint8_t* p, uint64_t l) { (void)s; (void)p; (void)l; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_cred_v1(int64_t s, int64_t c) { (void)s; (void)c; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_join_procs_v1(int64_t s, int64_t d, const uint8_t* p, uint64_t l) { (void)s; (void)d; (void)p; (void)l; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_new_session_v1(int64_t s) { (void)s; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_run_v1(int64_t s) { (void)s; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_free_v1(int64_t s) { (void)s; return RT_PRIVDROP_UNSUPPORTED; }
int64_t rt_privspawn_wait_v1(int64_t p) { (void)p; return RT_PRIVDROP_UNSUPPORTED; }

#endif
