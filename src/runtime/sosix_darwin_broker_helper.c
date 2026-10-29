/* Canonical closed-admission helper. Deliberately no workload execution yet:
 * this direct child has no disjoint-coalition authority. The provisioned image
 * binds these bytes, removes exception entitlements, constrains libraries and
 * runs with an empty environment established by the kernel before dyld. */
#include "runtime_sosix_darwin_broker_admission_private.h"
#include <crt_externs.h>

static int parse_identity(const char *text, uint32_t *value) {
    if (!text || !*text) return EINVAL;
    uint64_t n = 0;
    for (const char *p = text; *p; ++p) {
        if (*p < '0' || *p > '9' || n > (UINT32_MAX - (unsigned)(*p - '0')) / 10) return EINVAL;
        n = n * 10 + (unsigned)(*p - '0');
    }
    *value = (uint32_t)n; return 0;
}
int main(int argc, char **argv) {
    if (argc != 5 || strcmp(argv[1], SOSIX_DARWIN_BROKER_CLOSED_MODE)) return 90;
    /* Defense in depth; this is not a substitute for the spawn-time empty env. */
    if (**_NSGetEnviron()) return 91;
    uint32_t pid, version;
    if (parse_identity(argv[3], &pid) || parse_identity(argv[4], &version) || pid <= 1 || pid > INT_MAX) return 92;
    struct sockaddr_un address = {.sun_family = AF_UNIX};
    if (argv[2][0] != '/' || strlen(argv[2]) >= sizeof(address.sun_path)) return 93;
    strcpy(address.sun_path, argv[2]);
    int fd = socket(AF_UNIX, SOCK_STREAM, 0); if (fd < 0) return 94;
    if (sosix_darwin_broker_connect(fd, &address, 10000)) { close(fd); return 95; }
    audit_token_t token; SosixDarwinProcessIdentity identity;
    int e = sosix_darwin_broker_peer_identity(fd, (pid_t)pid, version, &token, &identity);
    /* No byte leaves the helper until the controller kernel identity matches. */
    if (!e) e = sosix_darwin_broker_send_byte(fd, 'R');
    char byte;
    if (!e) e = sosix_darwin_broker_read_byte(fd, &byte, 10000);
    if (!e && byte != 'A') e = EPROTO;
    if (!e) e = sosix_darwin_broker_send_byte(fd, 'A');
    while (!e) {
        e = sosix_darwin_broker_read_byte(fd, &byte, 10000);
        if (e || byte == 'Q') break;
        if (byte != 'P') { e = EPROTO; break; }
        e = sosix_darwin_broker_send_byte(fd, 'P');
    }
    close(fd); return e ? 96 : 0;
}
