/* Darwin qualification probe for the SOSIX Seatbelt activation leaf
 * (runtime_sosix_darwin_sandbox_v1.h). The activation is irreversible, so it
 * runs ONLY in a disposable forked child; the parent observes the verdicts.
 *
 * usage: sosix_darwin_sandbox_v1_selfcheck <profile.sb> <state_root> <attempt_key>
 *   <profile.sb> is the text seatbelt_profile_compile_v1 produced for
 *   seatbelt_attempt_policy_v1(seatbelt_attempt_dir_plan_v1(state_root, key), [], "endpoint-v1").
 * Build: same recipe as local_unix_v1_selfcheck (see
 * doc/06_spec/01_unit/lib/io/local_ipc_v1_native_evidence.sdn), plus on Darwin
 * -Wl,-dead_strip -Wl,-undefined,dynamic_lookup. */
#if !defined(__APPLE__)
#include <stdio.h>
int main(void) { puts("SKIP: sosix_darwin_sandbox_v1_selfcheck is Darwin-only"); return 77; }
#else
#include "../runtime.h"
#define SOSIX_DARWIN_SANDBOX_PROFILE_MAX_V1 262144
/* Linked from runtime_process_owned.c, the production owner of the leaf. */
SplArray* sosix_darwin_sandbox_apply_profile_v1(SplArray* profile);
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <stdio.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>
#include <netdb.h>
#include <spawn.h>
#include <servers/bootstrap.h>

static char root[1024], att[1024];

static void put_file(const char* path) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd >= 0) { (void)write(fd, "sentinel\n", 9); close(fd); }
}
static void mk(const char* path) { mkdir(path, 0700); }
static int can_read(const char* path) {
    int fd = open(path, O_RDONLY);
    if (fd < 0) return 0;
    close(fd);
    return 1;
}
static int can_create(const char* path) {
    int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return 0;
    close(fd);
    return 1;
}
static int can_connect_unix(const char* path) {
    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) return 0;
    struct sockaddr_un a; memset(&a, 0, sizeof a); a.sun_family = AF_UNIX;
    strncpy(a.sun_path, path, sizeof a.sun_path - 1);
    int ok = connect(fd, (struct sockaddr*)&a, sizeof a) == 0;
    close(fd);
    return ok;
}
static int can_connect_inet(int port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return 0;
    struct sockaddr_in a; memset(&a, 0, sizeof a); a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port); a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    int ok = connect(fd, (struct sockaddr*)&a, sizeof a) == 0;
    close(fd);
    return ok;
}

int main(int argc, char** argv) {
    if (argc != 4) { fprintf(stderr, "usage: %s <profile.sb> <state_root> <attempt_key>\n", argv[0]); return 2; }
    FILE* pf = fopen(argv[1], "rb");
    if (!pf) { perror("profile"); return 2; }
    static char text[SOSIX_DARWIN_SANDBOX_PROFILE_MAX_V1];
    size_t n = fread(text, 1, sizeof text - 1, pf); fclose(pf);
    snprintf(root, sizeof root, "%s", argv[2]);
    snprintf(att, sizeof att, "%s/attempts/%s", root, argv[3]);
    char p[1200];
    mk(root); snprintf(p, sizeof p, "%s/attempts", root); mk(p); mk(att);
    const char* subs[] = {"private", "workspace", "output", "home", "tmp", "ipc"};
    for (int i = 0; i < 6; i++) { snprintf(p, sizeof p, "%s/%s", att, subs[i]); mk(p); }
    snprintf(p, sizeof p, "%s/host-scope", root); mk(p);
    snprintf(p, sizeof p, "%s/host-scope/s", root); put_file(p);
    snprintf(p, sizeof p, "%s/private/s", att); put_file(p);
    snprintf(p, sizeof p, "%s/workspace/in", att); put_file(p);
    snprintf(p, sizeof p, "%s/attempts/sibling-a1", root); mk(p);
    snprintf(p, sizeof p, "%s/attempts/sibling-a1/s", root); put_file(p);

    /* Parent-owned listeners: the attempt broker socket and a loopback port. */
    char sock[1200]; snprintf(sock, sizeof sock, "%s/ipc/broker.sock", att); unlink(sock);
    /* strncpy below would silently truncate and bind a DIFFERENT path. */
    if (strlen(sock) >= sizeof ((struct sockaddr_un*)0)->sun_path) {
        fprintf(stderr, "state_root too long: broker socket path exceeds sun_path\n"); return 2;
    }
    int ul = socket(AF_UNIX, SOCK_STREAM, 0);
    struct sockaddr_un ua; memset(&ua, 0, sizeof ua); ua.sun_family = AF_UNIX;
    strncpy(ua.sun_path, sock, sizeof ua.sun_path - 1);
    if (bind(ul, (struct sockaddr*)&ua, sizeof ua) != 0 || listen(ul, 4) != 0) { perror("broker"); return 2; }
    int il = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in ia; memset(&ia, 0, sizeof ia); ia.sin_family = AF_INET;
    ia.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    socklen_t il_len = sizeof ia;
    if (bind(il, (struct sockaddr*)&ia, sizeof ia) != 0 || listen(il, 4) != 0 ||
        getsockname(il, (struct sockaddr*)&ia, &il_len) != 0) { perror("inet"); return 2; }
    int port = ntohs(ia.sin_port);

    /* Extra fixtures for the remaining canaries. */
    char link[1200]; snprintf(link, sizeof link, "%s/workspace/link", att);
    snprintf(p, sizeof p, "%s/private/s", att); unlink(link); (void)symlink(p, link);
    char alias[1200]; snprintf(alias, sizeof alias, "%s/PRIVATE/s", att);
    char home_sentinel[1200];
    snprintf(home_sentinel, sizeof home_sentinel, "%s/.simple_seatbelt_probe_%d", getenv("HOME") ? getenv("HOME") : "/tmp", (int)getpid());
    put_file(home_sentinel);
    char other[1200]; snprintf(other, sizeof other, "%s/other.sock", root); unlink(other);
    int ol = socket(AF_UNIX, SOCK_STREAM, 0);
    struct sockaddr_un oa; memset(&oa, 0, sizeof oa); oa.sun_family = AF_UNIX;
    strncpy(oa.sun_path, other, sizeof oa.sun_path - 1);
    if (bind(ol, (struct sockaddr*)&oa, sizeof oa) != 0 || listen(ol, 4) != 0) { perror("other"); return 2; }
    int l6 = socket(AF_INET6, SOCK_STREAM, 0);
    struct sockaddr_in6 a6; memset(&a6, 0, sizeof a6); a6.sin6_family = AF_INET6; a6.sin6_addr = in6addr_loopback;
    socklen_t a6_len = sizeof a6;
    int port6 = -1;
    if (l6 >= 0 && bind(l6, (struct sockaddr*)&a6, sizeof a6) == 0 && listen(l6, 4) == 0 &&
        getsockname(l6, (struct sockaddr*)&a6, &a6_len) == 0) port6 = ntohs(a6.sin6_port);

    /* Unconfined controls: every deny canary must be reachable without the
     * sandbox, otherwise a deny proves nothing. */
    int controls_ok = 1;
    snprintf(p, sizeof p, "%s/host-scope/s", root); controls_ok &= can_read(p);
    controls_ok &= can_read(link) & can_read(alias) & can_read(home_sentinel);
    controls_ok &= can_connect_unix(other) & can_connect_inet(port) & (port6 > 0);
    {
        struct addrinfo* res = NULL;
        controls_ok &= getaddrinfo("apple.com", "443", NULL, &res) == 0;
        if (res) freeaddrinfo(res);
        mach_port_t mp = MACH_PORT_NULL;
        controls_ok &= bootstrap_look_up(bootstrap_port, "com.apple.system.notification_center", &mp) == KERN_SUCCESS;
    }
    printf("control unconfined-reachability %s\n", controls_ok ? "ok" : "FAIL");

    /* activation-failure-never-execs-target: a refused profile must be
     * reported as refused, so the worker never reaches exec. */
    int refused = 0;
    {
        int fp[2]; if (pipe(fp) != 0) return 2;
        pid_t c = fork();
        if (c == 0) {
            const char* bad = "(version 1)(allow bogus-operation-xyz)";
            SplArray* b = rt_array_new((int64_t)strlen(bad));
            for (size_t i = 0; bad[i]; i++) rt_array_push(b, rt_value_int((unsigned char)bad[i]));
            SplArray* r = sosix_darwin_sandbox_apply_profile_v1(b);
            char v = (r && rt_value_as_int(rt_array_get(r, 0)) == -3) ? 1 : 0;
            (void)write(fp[1], &v, 1); _exit(0);
        }
        close(fp[1]); char v = 0; if (read(fp[0], &v, 1) == 1) refused = v; close(fp[0]); waitpid(c, NULL, 0);
    }

    /* child-inherits-confinement: the strict profile denies fork, so prove
     * inheritance with the same profile plus (allow process-fork) only; a
     * grandchild that cannot be created reports nothing (stays not-run). */
    int inherit_reported = 0, inherit_allow = 0;
    {
        char forked[SOSIX_DARWIN_SANDBOX_PROFILE_MAX_V1 + 32];
        int fl = snprintf(forked, sizeof forked, "%.*s\n(allow process-fork)\n", (int)n, text);
        int fp[2]; if (pipe(fp) != 0) return 2;
        pid_t c = fork();
        if (c == 0) {
            SplArray* b = rt_array_new((int64_t)fl);
            for (int i = 0; i < fl; i++) rt_array_push(b, rt_value_int((unsigned char)forked[i]));
            SplArray* r = sosix_darwin_sandbox_apply_profile_v1(b);
            char v = 0;
            if (r && rt_value_as_int(rt_array_get(r, 0)) == 0) {
                pid_t gc = fork();
                if (gc == 0) {
                    char z[1200]; snprintf(z, sizeof z, "%s/host-scope/s", root);
                    _exit(can_read(z) ? 11 : 10);
                }
                int st = 0;
                if (gc > 0 && waitpid(gc, &st, 0) == gc && WIFEXITED(st))
                    v = WEXITSTATUS(st) == 11 ? 'A' : (WEXITSTATUS(st) == 10 ? 'D' : 0);
            }
            (void)write(fp[1], &v, 1); _exit(0);
        }
        close(fp[1]); char v = 0;
        if (read(fp[0], &v, 1) == 1 && v) { inherit_reported = 1; inherit_allow = v == 'A'; }
        close(fp[0]); waitpid(c, NULL, 0);
    }

    enum { N = 23 };
    static const char* ids[N] = {
        "activation-failure-never-execs-target", "workspace-read-allowed", "output-write-allowed",
        "workspace-write-outside-grant-denied", "ungranted-exec-denied", "child-inherits-confinement",
        "sibling-attempt-read-denied", "host-scope-state-read-denied", "attempt-private-read-denied",
        "user-home-credential-read-denied", "symlink-to-protected-root-denied", "case-alias-protected-root-denied",
        "tcp-ipv4-connect-denied", "tcp-ipv6-connect-denied", "udp-send-denied", "dns-resolve-denied",
        "localhost-connect-denied", "inet-listen-denied", "broker-endpoint-connect-allowed",
        "other-unix-socket-connect-denied", "mach-lookup-denied", "process-fork-denied", "posix-spawn-denied"};
    /* got[i] = 1 when the operation SUCCEEDED (allow), 0 when it failed (deny). */
    char got[N + 1]; memset(got, 0, sizeof got);
    got[0] = refused ? 0 : 1;

    int pipefd[2]; if (pipe(pipefd) != 0) return 2;
    pid_t child = fork();
    if (child == 0) {
        close(pipefd[0]);
        SplArray* bytes = rt_array_new((int64_t)n);
        for (size_t i = 0; i < n; i++) rt_array_push(bytes, rt_value_int((unsigned char)text[i]));
        SplArray* r = sosix_darwin_sandbox_apply_profile_v1(bytes);
        char g[N + 1]; memset(g, 0, sizeof g);
        g[N] = r && rt_value_as_int(rt_array_get(r, 0)) == 0;
        if (g[N]) {
            char q[1200];
            snprintf(q, sizeof q, "%s/workspace/in", att); g[1] = can_read(q);
            snprintf(q, sizeof q, "%s/output/out", att); g[2] = can_create(q);
            snprintf(q, sizeof q, "%s/workspace/new", att); g[3] = can_create(q);
            snprintf(q, sizeof q, "%s/attempts/sibling-a1/s", root); g[6] = can_read(q);
            snprintf(q, sizeof q, "%s/host-scope/s", root); g[7] = can_read(q);
            snprintf(q, sizeof q, "%s/private/s", att); g[8] = can_read(q);
            g[9] = can_read(home_sentinel);
            g[10] = can_read(link);
            g[11] = can_read(alias);
            g[12] = can_connect_inet(port);
            {
                int fd = socket(AF_INET6, SOCK_STREAM, 0);
                struct sockaddr_in6 d; memset(&d, 0, sizeof d); d.sin6_family = AF_INET6;
                d.sin6_addr = in6addr_loopback; d.sin6_port = htons((uint16_t)port6);
                g[13] = fd >= 0 && connect(fd, (struct sockaddr*)&d, sizeof d) == 0;
                if (fd >= 0) close(fd);
            }
            {
                int fd = socket(AF_INET, SOCK_DGRAM, 0);
                struct sockaddr_in d; memset(&d, 0, sizeof d); d.sin_family = AF_INET;
                d.sin_port = htons((uint16_t)port); d.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
                g[14] = fd >= 0 && sendto(fd, "x", 1, 0, (struct sockaddr*)&d, sizeof d) == 1;
                if (fd >= 0) close(fd);
            }
            {
                struct addrinfo* res = NULL;
                g[15] = getaddrinfo("apple.com", "443", NULL, &res) == 0;
                if (res) freeaddrinfo(res);
            }
            g[16] = can_connect_inet(port);
            {
                int fd = socket(AF_INET, SOCK_STREAM, 0);
                struct sockaddr_in d; memset(&d, 0, sizeof d); d.sin_family = AF_INET;
                d.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
                g[17] = fd >= 0 && bind(fd, (struct sockaddr*)&d, sizeof d) == 0 && listen(fd, 1) == 0;
                if (fd >= 0) close(fd);
            }
            g[18] = can_connect_unix(sock);
            g[19] = can_connect_unix(other);
            {
                mach_port_t mp = MACH_PORT_NULL;
                g[20] = bootstrap_look_up(bootstrap_port, "com.apple.system.notification_center", &mp) == KERN_SUCCESS;
            }
            {
                pid_t gc = fork();
                if (gc == 0) {
                    _exit(0);
                }
                g[21] = gc > 0;
                int st = 0;
                if (gc > 0) waitpid(gc, &st, 0);
            }
            {
                pid_t sp = 0; char* av[] = {"/usr/bin/true", NULL};
                g[22] = posix_spawn(&sp, "/usr/bin/true", NULL, NULL, av, NULL) == 0;
                if (g[22]) waitpid(sp, NULL, 0);
            }
        }
        (void)write(pipefd[1], g, sizeof g);
        if (g[N]) {
            /* ungranted-exec-denied: last act; a returning execve is a deny. */
            char* av[] = {"/usr/bin/true", NULL};
            execve("/usr/bin/true", av, NULL);
            char d = 'D'; (void)write(pipefd[1], &d, 1);
        }
        _exit(0);
    }
    close(pipefd[1]);
    char cg[N + 1];
    ssize_t rd = read(pipefd[0], cg, sizeof cg);
    char d = 0; ssize_t rd2 = read(pipefd[0], &d, 1);
    int status = 0; waitpid(child, &status, 0);
    unlink(sock); unlink(other); unlink(home_sentinel); unlink(link);
    if (rd != (ssize_t)sizeof cg) { puts("FAIL child produced no verdicts"); return 1; }
    if (!cg[N]) { puts("FAIL sandbox_init refused the compiled profile"); return 1; }
    for (int i = 1; i < N; i++) got[i] = cg[i];
    got[5] = (char)inherit_allow;
    got[4] = !(rd2 == 1 && d == 'D');
    static const char expect_allow[N] = {0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0};
    int failed = controls_ok ? 0 : 1;
    for (int i = 0; i < N; i++) {
        if (i == 5 && !inherit_reported) { failed++; printf("FAIL %s not observed\n", ids[i]); continue; }
        printf("canary %s %s\n", ids[i], got[i] ? "allow" : "deny");
        if ((got[i] != 0) != (expect_allow[i] != 0)) { failed++; printf("FAIL %s\n", ids[i]); }
    }
    if (failed) { printf("FAIL %d Darwin Seatbelt qualification mismatch(es) of %d canaries\n", failed, N); return 1; }
    printf("PASS Darwin Seatbelt qualification: %d canaries match seatbelt_qualification_plan_v1\n", N);
    return 0;
}
#endif
