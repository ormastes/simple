#include "runtime.h"

#include <arpa/inet.h>
#include <openssl/ssl.h>
#include <pthread.h>
#include <stdint.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

typedef struct TestString {
    uint64_t len;
    uint8_t data[];
} TestString;

typedef struct TestServer {
    int listener;
    const char *cert_path;
    const char *key_path;
    int stall;
    int reset;
    int trickle;
} TestServer;

static _Atomic int failures = 0;
static int64_t live_strings = 0;

static void check(int condition, const char *message) {
    if (!condition) {
        fprintf(stderr, "FAIL: %s\n", message);
        atomic_fetch_add(&failures, 1);
    }
}

static int64_t now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

int64_t rt_string_new(const uint8_t *bytes, uint64_t len) {
    TestString *value = (TestString *)malloc(sizeof(*value) + (size_t)len + 1);
    if (!value) return 0;
    value->len = len;
    if (len > 0 && bytes) memcpy(value->data, bytes, (size_t)len);
    value->data[len] = 0;
    live_strings++;
    return (int64_t)(intptr_t)value;
}

int64_t rt_string_len(int64_t value) {
    TestString *text = (TestString *)(intptr_t)value;
    return text ? (int64_t)text->len : 0;
}

const uint8_t *rt_string_data(int64_t value) {
    TestString *text = (TestString *)(intptr_t)value;
    return text ? text->data : NULL;
}

int64_t rt_string_free(int64_t value) {
    TestString *text = (TestString *)(intptr_t)value;
    if (!text) return 0;
    free(text);
    live_strings--;
    return 1;
}

static ssize_t send_without_sigpipe(int fd, const void *data, size_t len) {
#ifdef MSG_NOSIGNAL
    return send(fd, data, len, MSG_NOSIGNAL);
#else
    return send(fd, data, len, 0);
#endif
}

static void *serve_once(void *raw) {
    TestServer *server = (TestServer *)raw;
    SSL_CTX *ctx = SSL_CTX_new(TLS_server_method());
    int client = -1;
    SSL *ssl = NULL;
    if (!ctx || SSL_CTX_use_certificate_chain_file(ctx, server->cert_path) != 1 ||
        SSL_CTX_use_PrivateKey_file(ctx, server->key_path, SSL_FILETYPE_PEM) != 1 ||
        SSL_CTX_check_private_key(ctx) != 1) {
        atomic_fetch_add(&failures, 1);
        goto done;
    }
    client = accept(server->listener, NULL, NULL);
    if (client < 0) {
        atomic_fetch_add(&failures, 1);
        goto done;
    }
    if (server->trickle) {
        const uint8_t record_header[] = {0x16, 0x03, 0x03, 0x40, 0x00};
        uint8_t zero = 0;
        size_t i;
#ifdef SO_NOSIGPIPE
        {
            int enabled = 1;
            (void)setsockopt(client, SOL_SOCKET, SO_NOSIGPIPE,
                             &enabled, sizeof(enabled));
        }
#endif
        for (i = 0; i < sizeof(record_header); ++i) {
            if (send_without_sigpipe(client, &record_header[i], 1) != 1) goto done;
            usleep(200000);
        }
        for (i = 0; i < 50; ++i) {
            if (send_without_sigpipe(client, &zero, 1) != 1) goto done;
            usleep(200000);
        }
        goto done;
    }
    ssl = SSL_new(ctx);
    if (!ssl || SSL_set_fd(ssl, client) != 1 || SSL_accept(ssl) != 1) goto done;
    if (server->reset) {
        struct linger reset = {1, 0};
        (void)setsockopt(client, SOL_SOCKET, SO_LINGER, &reset, sizeof(reset));
    } else if (server->stall) {
        sleep(7);
    } else {
        char request[16];
        if (SSL_read(ssl, request, sizeof(request)) > 0) {
            (void)SSL_write(ssl, "OK", 2);
        }
        (void)SSL_shutdown(ssl);
    }
done:
    if (ssl) SSL_free(ssl);
    if (client >= 0) close(client);
    if (ctx) SSL_CTX_free(ctx);
    return NULL;
}

static int start_server(TestServer *server, pthread_t *thread) {
    struct sockaddr_in address;
    socklen_t address_len = sizeof(address);
    int enabled = 1;
    server->listener = socket(AF_INET, SOCK_STREAM, 0);
    if (server->listener < 0) return -1;
    (void)setsockopt(server->listener, SOL_SOCKET, SO_REUSEADDR,
                     &enabled, sizeof(enabled));
    memset(&address, 0, sizeof(address));
    address.sin_family = AF_INET;
    address.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    address.sin_port = 0;
    if (bind(server->listener, (struct sockaddr *)&address, sizeof(address)) != 0 ||
        listen(server->listener, 1) != 0 ||
        getsockname(server->listener, (struct sockaddr *)&address, &address_len) != 0 ||
        pthread_create(thread, NULL, serve_once, server) != 0) {
        close(server->listener);
        return -1;
    }
    return (int)ntohs(address.sin_port);
}

int main(int argc, char **argv) {
    TestServer server;
    pthread_t thread;
    int port;
    int expect_success;
    int server_joined = 0;
    int64_t host;
    int64_t name;
    int64_t handle;
    int64_t baseline;
    int64_t connect_started_ms;
    int64_t connect_timeout_ms;
    if (argc != 5) return 64;
    memset(&server, 0, sizeof(server));
    server.listener = -1;
    server.cert_path = argv[2];
    server.key_path = argv[3];
    server.stall = strcmp(argv[1], "stall") == 0;
    server.reset = strcmp(argv[1], "reset") == 0;
    server.trickle = strcmp(argv[1], "trickle") == 0;
    expect_success = strcmp(argv[1], "trusted") == 0 ||
                     server.stall || server.reset;
    port = start_server(&server, &thread);
    check(port > 0, "server started");
    if (port <= 0) return 1;

    host = rt_string_new((const uint8_t *)"127.0.0.1", 9);
    name = rt_string_new((const uint8_t *)argv[4], strlen(argv[4]));
    baseline = live_strings;
    connect_timeout_ms = server.trickle ? 1000 : 5000;
    connect_started_ms = now_ms();
    handle = rt_tls_client_connect_address_with_sni_timeout(
        host, port, name, connect_timeout_ms
    );
    if (expect_success) {
        int64_t protocol;
        int64_t request;
        int64_t first;
        check(handle > 0, "trusted connection accepted");
        protocol = rt_tls_get_protocol_version(handle);
        check(rt_string_len(protocol) == 7, "TLS version reported");
        (void)rt_string_free(protocol);
        request = rt_string_new((const uint8_t *)"GET", 3);
        if (server.reset) {
            (void)pthread_join(thread, NULL);
            server_joined = 1;
            usleep(100000);
            check(rt_tls_client_write(handle, request) < 0,
                  "peer-reset write fails without SIGPIPE termination");
            check(rt_tls_client_close(handle) == 0,
                  "peer-reset handle closes as broken");
        } else {
            check(rt_tls_client_write(handle, request) == 3, "full request write");
        }
        (void)rt_string_free(request);
        if (server.reset) {
            first = rt_string_new(NULL, 0);
        } else {
            int64_t read_started_ms = now_ms();
            first = rt_tls_client_read(handle, 1);
            check(now_ms() - read_started_ms <= 6000,
                  "TLS read respects the runtime deadline");
        }
        if (server.stall) {
            int64_t close_started_ms = now_ms();
            check(rt_string_len(first) == 0, "stalled read fails closed");
            check(rt_tls_client_close(handle) == 0, "failed read marks handle broken");
            check(now_ms() - close_started_ms <= 1000,
                  "broken close does not wait for TLS shutdown");
        } else if (!server.reset) {
            int64_t second;
            check(rt_string_len(first) == 1, "read cap enforced");
            second = rt_tls_client_read(handle, 8);
            check(rt_string_len(second) == 1, "remaining response read");
            (void)rt_string_free(second);
            check(rt_tls_client_close(handle) == 1, "clean close succeeds");
        }
        (void)rt_string_free(first);
        if (!server.reset) {
            check(rt_tls_client_close(handle) == 0, "stale close rejected");
        }
    } else {
        check(handle < 0, "invalid certificate identity rejected");
        if (server.trickle) {
            check(now_ms() - connect_started_ms <= 1500,
                  "trickled handshake respects one absolute deadline");
        }
    }
    if (!server_joined) (void)pthread_join(thread, NULL);
    close(server.listener);
    check(live_strings == baseline, "returned runtime strings released");
    (void)rt_string_free(host);
    (void)rt_string_free(name);
    check(live_strings == 0, "all test strings released");
    if (atomic_load(&failures) != 0) return 1;
    printf("SELFCHECK PASSED mode=%s\n", argv[1]);
    return 0;
}
