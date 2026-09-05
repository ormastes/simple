#define _POSIX_C_SOURCE 200809L

#include <arpa/inet.h>
#include <netinet/tcp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

static int64_t now_micros(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000000LL + ts.tv_nsec / 1000LL;
}

static int64_t env_i64(const char *name, int64_t fallback) {
    const char *value = getenv(name);
    if (value == NULL || value[0] == '\0') return fallback;
    return atoll(value);
}

static int connect_loopback(int port) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return -1;
    int enabled = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &enabled, sizeof(enabled));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons((uint16_t)port);
    if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) != 0) {
        close(fd);
        return -1;
    }
    return fd;
}

static int read_exact(int fd, char *buffer, int size) {
    int total = 0;
    while (total < size) {
        ssize_t got = read(fd, buffer + total, (size_t)(size - total));
        if (got <= 0) return -1;
        total += (int)got;
    }
    return total;
}

int main(void) {
    int64_t iters = env_i64("NET_PARITY_ITERS", 10000);
    int payload_size = (int)env_i64("NET_PARITY_PAYLOAD", 1024);
    int port = (int)env_i64("NET_PARITY_PORT", 39091);
    char *payload = malloc((size_t)payload_size);
    char *reply = malloc((size_t)payload_size);
    memset(payload, 'x', (size_t)payload_size);

    int fd = connect_loopback(port);
    if (fd < 0) {
        fprintf(stderr, "[netbench-error] lang=c case=tcp_echo connect\n");
        return 1;
    }

    int64_t checksum = 0;
    int64_t start = now_micros();
    for (int64_t i = 0; i < iters; i++) {
        if (write(fd, payload, (size_t)payload_size) != payload_size) return 1;
        if (read_exact(fd, reply, payload_size) != payload_size) return 1;
        checksum += payload_size;
    }
    int64_t elapsed = now_micros() - start;
    close(fd);
    printf("[netbench] lang=c case=tcp_echo bytes=%lld iters=%lld micros=%lld checksum=%lld\n",
           (long long)checksum, (long long)iters, (long long)elapsed, (long long)checksum);
    free(payload);
    free(reply);
    return 0;
}
