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

struct probe { const char* name; int expect; int got; };

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

    struct probe probes[] = {
        {"control-unconfined-host-scope-readable", 1, 0},
        {"applied", 1, 0},
        {"workspace-read-allowed", 1, 0},
        {"output-create-allowed", 1, 0},
        {"workspace-write-denied", 0, 0},
        {"private-read-denied", 0, 0},
        {"host-scope-read-denied", 0, 0},
        {"sibling-attempt-read-denied", 0, 0},
        {"host-etc-read-denied", 0, 0},
        {"broker-socket-connect-allowed", 1, 0},
        {"loopback-inet-connect-denied", 0, 0},
        {"fork-denied", 0, 0},
    };
    const int count = (int)(sizeof probes / sizeof probes[0]);
    snprintf(p, sizeof p, "%s/host-scope/s", root);
    probes[0].got = can_read(p);

    int pipefd[2]; if (pipe(pipefd) != 0) return 2;
    pid_t child = fork();
    if (child == 0) {
        close(pipefd[0]);
        SplArray* bytes = rt_array_new((int64_t)n);
        for (size_t i = 0; i < n; i++) rt_array_push(bytes, rt_value_int((unsigned char)text[i]));
        SplArray* r = sosix_darwin_sandbox_apply_profile_v1(bytes);
        char got[16] = {0};
        got[1] = r && rt_value_as_int(rt_array_get(r, 0)) == 0;
        if (got[1]) {
            char q[1200];
            snprintf(q, sizeof q, "%s/workspace/in", att); got[2] = can_read(q);
            snprintf(q, sizeof q, "%s/output/out", att); got[3] = can_create(q);
            snprintf(q, sizeof q, "%s/workspace/new", att); got[4] = can_create(q);
            snprintf(q, sizeof q, "%s/private/s", att); got[5] = can_read(q);
            snprintf(q, sizeof q, "%s/host-scope/s", root); got[6] = can_read(q);
            snprintf(q, sizeof q, "%s/attempts/sibling-a1/s", root); got[7] = can_read(q);
            got[8] = can_read("/private/etc/hosts");
            got[9] = can_connect_unix(sock);
            got[10] = can_connect_inet(port);
            pid_t g = fork();
            if (g == 0) _exit(0);
            got[11] = g > 0;
            if (g > 0) waitpid(g, NULL, 0);
        }
        (void)write(pipefd[1], got, sizeof got);
        _exit(0);
    }
    close(pipefd[1]);
    char got[16] = {0};
    ssize_t rd = read(pipefd[0], got, sizeof got);
    int status = 0; waitpid(child, &status, 0);
    if (rd != (ssize_t)sizeof got) { puts("FAIL child produced no verdicts"); return 1; }
    for (int i = 1; i < count; i++) probes[i].got = got[i];
    int failed = 0;
    for (int i = 0; i < count; i++) {
        int ok = (probes[i].got != 0) == (probes[i].expect != 0);
        if (!ok) failed++;
        printf("%s %s\n", ok ? "ok  " : "FAIL", probes[i].name);
    }
    unlink(sock);
    if (failed) { printf("FAIL %d of %d Darwin Seatbelt activation probes\n", failed, count); return 1; }
    printf("PASS Darwin Seatbelt activation: %d probes (fs isolation, sibling/host deny, broker-only network, fork deny)\n", count);
    return 0;
}
#endif
