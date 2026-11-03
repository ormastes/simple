/* Loopback one-shot server for check-runtime-http-framing.shs (POSIX only).
 * usage: rt_http_framing_server PORT_FILE STRIDE WIRE_FILE
 * Binds 127.0.0.1:0, publishes the port, serves WIRE_FILE bytes in STRIDE-byte
 * writes to one client after its request headers, then exits 0. */
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

int main(int argc, char **argv) {
    if (argc != 4) return 64;
    size_t stride = (size_t)strtoul(argv[2], NULL, 10);
    if (!stride) return 64;
    FILE *wf = fopen(argv[3], "rb");
    if (!wf) return 1;
    static char wire[65536];
    size_t n = fread(wire, 1, sizeof(wire), wf);
    fclose(wf);
    alarm(6);
    int ls = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in a;
    memset(&a, 0, sizeof(a));
    a.sin_family = AF_INET;
    a.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    socklen_t al = sizeof(a);
    if (ls < 0 || bind(ls, (struct sockaddr *)&a, sizeof(a)) || listen(ls, 1) ||
        getsockname(ls, (struct sockaddr *)&a, &al)) return 1;
    char tmp[4096];
    snprintf(tmp, sizeof(tmp), "%s.tmp", argv[1]);
    FILE *pf = fopen(tmp, "w");
    if (!pf) return 1;
    fprintf(pf, "%d\n", (int)ntohs(a.sin_port));
    fclose(pf);
    if (rename(tmp, argv[1])) return 1;
    int c = accept(ls, NULL, NULL);
    if (c < 0) return 1;
    char req[8192];
    size_t have = 0;
    while (have < sizeof(req) - 1) {
        ssize_t r = recv(c, req + have, sizeof(req) - 1 - have, 0);
        if (r <= 0) return 1;
        have += (size_t)r;
        req[have] = 0;
        if (strstr(req, "\r\n\r\n")) break;
    }
    for (size_t off = 0; off < n; off += stride) {
        size_t len = n - off < stride ? n - off : stride;
        if (send(c, wire + off, len, 0) != (ssize_t)len) return 1;
        if (stride < 4096) usleep(200);
    }
    close(c);
    close(ls);
    return 0;
}
