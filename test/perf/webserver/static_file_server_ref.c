// Minimal C static HTTP baseline for test/perf/webserver/live_static_compare.py.
//
// Environment:
//   C_STATIC_SERVER_ADDR      default: 127.0.0.1
//   C_STATIC_SERVER_PORT      default: 18081
//   C_STATIC_SERVER_FILE      default: README.md
//   C_STATIC_SERVER_REQUESTS  default: 128

#define _POSIX_C_SOURCE 200809L
#include <arpa/inet.h>
#include <errno.h>
#include <netinet/in.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

static const char *env_text(const char *key, const char *fallback) {
    const char *value = getenv(key);
    return value && value[0] ? value : fallback;
}

static long env_long(const char *key, long fallback) {
    const char *value = getenv(key);
    if (!value || !value[0]) return fallback;
    char *end = NULL;
    long parsed = strtol(value, &end, 10);
    return end && *end == '\0' ? parsed : fallback;
}

static char *read_file(const char *path, size_t *len_out, int *found_out) {
    FILE *file = fopen(path, "rb");
    if (!file) {
        const char *missing = "missing fixture\n";
        *len_out = strlen(missing);
        *found_out = 0;
        char *buf = malloc(*len_out + 1);
        if (buf) memcpy(buf, missing, *len_out + 1);
        return buf;
    }
    fseek(file, 0, SEEK_END);
    long len = ftell(file);
    fseek(file, 0, SEEK_SET);
    if (len < 0) len = 0;
    char *buf = malloc((size_t)len + 1);
    if (!buf) {
        fclose(file);
        return NULL;
    }
    size_t read_len = fread(buf, 1, (size_t)len, file);
    fclose(file);
    buf[read_len] = '\0';
    *len_out = read_len;
    *found_out = 1;
    return buf;
}

static const char *content_type(const char *path) {
    const char *dot = strrchr(path, '.');
    if (!dot) return "text/plain; charset=utf-8";
    if (strcmp(dot, ".html") == 0 || strcmp(dot, ".htm") == 0) return "text/html; charset=utf-8";
    if (strcmp(dot, ".css") == 0) return "text/css; charset=utf-8";
    if (strcmp(dot, ".js") == 0) return "application/javascript; charset=utf-8";
    if (strcmp(dot, ".json") == 0) return "application/json; charset=utf-8";
    return "text/plain; charset=utf-8";
}

static void drain_request(int fd, char *method, size_t method_len) {
    char buf[4096];
    ssize_t n = recv(fd, buf, sizeof(buf) - 1, 0);
    if (n <= 0) {
        snprintf(method, method_len, "GET");
        return;
    }
    buf[n] = '\0';
    sscanf(buf, "%15s", method);
}

static void send_all(int fd, const char *data, size_t len) {
    size_t sent = 0;
    while (sent < len) {
        ssize_t n = send(fd, data + sent, len - sent, 0);
        if (n <= 0) return;
        sent += (size_t)n;
    }
}

int main(void) {
    const char *addr = env_text("C_STATIC_SERVER_ADDR", "127.0.0.1");
    int port = (int)env_long("C_STATIC_SERVER_PORT", 18081);
    long limit = env_long("C_STATIC_SERVER_REQUESTS", 128);
    const char *path = env_text("C_STATIC_SERVER_FILE", "README.md");

    size_t body_len = 0;
    int found = 0;
    char *body = read_file(path, &body_len, &found);
    if (!body) return 2;

    int server = socket(AF_INET, SOCK_STREAM, 0);
    if (server < 0) return 3;
    int one = 1;
    setsockopt(server, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in sa;
    memset(&sa, 0, sizeof(sa));
    sa.sin_family = AF_INET;
    sa.sin_port = htons((uint16_t)port);
    if (inet_pton(AF_INET, addr, &sa.sin_addr) != 1) return 4;
    if (bind(server, (struct sockaddr *)&sa, sizeof(sa)) != 0) return 5;
    if (listen(server, 128) != 0) return 6;

    printf("[c-static-server-ready] addr=%s:%d file=%s requests=%ld\n", addr, port, path, limit);
    fflush(stdout);

    const char *status = found ? "200 OK" : "404 Not Found";
    const char *mime = content_type(path);
    for (long served = 0; served < limit; served++) {
        int client = accept(server, NULL, NULL);
        if (client < 0) continue;
        char method[16] = {0};
        drain_request(client, method, sizeof(method));

        char header[512];
        int header_len;
        if (strcmp(method, "GET") == 0 || strcmp(method, "HEAD") == 0) {
            header_len = snprintf(header, sizeof(header),
                "HTTP/1.1 %s\r\nServer: CStaticPerf\r\nContent-Type: %s\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n",
                status, mime, body_len);
            send_all(client, header, (size_t)header_len);
            if (strcmp(method, "HEAD") != 0) send_all(client, body, body_len);
        } else {
            const char *msg = "method not allowed\n";
            header_len = snprintf(header, sizeof(header),
                "HTTP/1.1 405 Method Not Allowed\r\nContent-Type: text/plain; charset=utf-8\r\nContent-Length: %zu\r\nConnection: close\r\n\r\n",
                strlen(msg));
            send_all(client, header, (size_t)header_len);
            send_all(client, msg, strlen(msg));
        }
        close(client);
    }

    close(server);
    free(body);
    return 0;
}
