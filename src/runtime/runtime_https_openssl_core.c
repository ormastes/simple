#include "runtime.h"

#include <stdint.h>

#if defined(__has_include)
#if __has_include(<openssl/ssl.h>) && __has_include(<openssl/x509v3.h>)
#define SIMPLE_CORE_HAS_OPENSSL 1
#endif
#endif

#ifndef SIMPLE_CORE_HAS_OPENSSL
#define SIMPLE_CORE_HAS_OPENSSL 0
#endif

#if SIMPLE_CORE_HAS_OPENSSL && !defined(_WIN32)
#include <arpa/inet.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <openssl/x509v3.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

#define SIMPLE_TLS_MAX_CONNECTIONS 256
#define SIMPLE_TLS_HOST_MAX 253
#define SIMPLE_TLS_READ_MAX 65536
#define SIMPLE_TLS_WRITE_MAX (50 * 1024 * 1024)
#define SIMPLE_TLS_TIMEOUT_MS 5000

typedef struct SimpleTlsConnection {
    int64_t handle;
    int fd;
    int broken;
    int closing;
    int refs;
    SSL *ssl;
    pthread_mutex_t lock;
    pthread_cond_t drained;
} SimpleTlsConnection;

typedef struct SimpleTlsSigpipeMask {
    sigset_t previous;
    int active;
    int was_pending;
} SimpleTlsSigpipeMask;

static SSL_CTX *simple_tls_client_ctx = NULL;
static pthread_once_t simple_tls_ctx_once = PTHREAD_ONCE_INIT;
static pthread_mutex_t simple_tls_table_lock = PTHREAD_MUTEX_INITIALIZER;
static SimpleTlsConnection *simple_tls_connections[SIMPLE_TLS_MAX_CONNECTIONS];
static int64_t simple_tls_next_handle = 1;

static int simple_tls_sigpipe_begin(SimpleTlsSigpipeMask *mask) {
    sigset_t blocked;
    sigset_t pending;
    memset(mask, 0, sizeof(*mask));
    sigemptyset(&blocked);
    sigaddset(&blocked, SIGPIPE);
    if (pthread_sigmask(SIG_BLOCK, &blocked, &mask->previous) != 0) return 0;
    mask->active = 1;
    if (sigpending(&pending) == 0) {
        mask->was_pending = sigismember(&pending, SIGPIPE) == 1;
    }
    return 1;
}

static void simple_tls_sigpipe_end(SimpleTlsSigpipeMask *mask) {
    sigset_t pending;
    if (!mask->active) return;
    if (!mask->was_pending && sigpending(&pending) == 0 &&
        sigismember(&pending, SIGPIPE) == 1) {
        sigset_t only_sigpipe;
        struct timespec no_wait;
        sigemptyset(&only_sigpipe);
        sigaddset(&only_sigpipe, SIGPIPE);
        no_wait.tv_sec = 0;
        no_wait.tv_nsec = 0;
        (void)sigtimedwait(&only_sigpipe, NULL, &no_wait);
    }
    (void)pthread_sigmask(SIG_SETMASK, &mask->previous, NULL);
}

static void simple_tls_init_ctx(void) {
    SSL_CTX *ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx) return;
    if (SSL_CTX_set_min_proto_version(ctx, TLS1_2_VERSION) != 1 ||
        SSL_CTX_set_default_verify_paths(ctx) != 1) {
        SSL_CTX_free(ctx);
        return;
    }
    SSL_CTX_set_verify(ctx, SSL_VERIFY_PEER, NULL);
    simple_tls_client_ctx = ctx;
}

static char *simple_tls_copy_text(int64_t value, int64_t max_len) {
    int64_t len = rt_string_len(value);
    const uint8_t *data = rt_string_data(value);
    if (!data || len <= 0 || len > max_len || memchr(data, 0, (size_t)len)) {
        return NULL;
    }
    char *copy = (char *)malloc((size_t)len + 1);
    if (!copy) return NULL;
    memcpy(copy, data, (size_t)len);
    copy[len] = '\0';
    return copy;
}

static int64_t simple_tls_now_ms(void) {
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
    return (int64_t)now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static int simple_tls_set_socket_timeouts(int fd, int64_t timeout_ms) {
    struct timeval timeout;
    if (timeout_ms < 1) timeout_ms = 1;
    timeout.tv_sec = (time_t)(timeout_ms / 1000);
    timeout.tv_usec = (suseconds_t)((timeout_ms % 1000) * 1000);
    if (setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &timeout, sizeof(timeout)) != 0 ||
        setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &timeout, sizeof(timeout)) != 0) {
        return 0;
    }
#ifdef SO_NOSIGPIPE
    {
        int enabled = 1;
        (void)setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &enabled, sizeof(enabled));
    }
#endif
    return 1;
}

static int simple_tls_wait_for_ssl(
    int fd, int ssl_error, int64_t deadline_ms
) {
    short events;
    if (ssl_error == SSL_ERROR_WANT_READ) {
        events = POLLIN;
    } else if (ssl_error == SSL_ERROR_WANT_WRITE) {
        events = POLLOUT;
    } else {
        return 0;
    }
    while (1) {
        struct pollfd poll_fd;
        int64_t now_ms = simple_tls_now_ms();
        int64_t remaining_ms;
        int result;
        if (now_ms < 0) return 0;
        remaining_ms = deadline_ms - now_ms;
        if (remaining_ms <= 0) return 0;
        poll_fd.fd = fd;
        poll_fd.events = events;
        poll_fd.revents = 0;
        result = poll(&poll_fd, 1, (int)remaining_ms);
        if (result > 0) {
            return (poll_fd.revents & POLLNVAL) == 0;
        }
        if (result == 0) return 0;
        if (errno != EINTR) return 0;
    }
}

static int simple_tls_connect_socket(
    const char *host, int64_t port, int64_t deadline_ms, int numeric_only
) {
    char port_text[6];
    struct addrinfo hints;
    struct addrinfo *addresses = NULL;
    struct addrinfo *address;
    int fd = -1;
    int port_len = snprintf(port_text, sizeof(port_text), "%lld", (long long)port);
    if (port_len <= 0 || (size_t)port_len >= sizeof(port_text)) return -1;

    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    if (numeric_only) hints.ai_flags = AI_NUMERICHOST;
    if (getaddrinfo(host, port_text, &hints, &addresses) != 0) return -1;

    for (address = addresses; address; address = address->ai_next) {
        int flags;
        int connected = 0;
        fd = socket(address->ai_family, address->ai_socktype, address->ai_protocol);
        if (fd < 0) continue;
        flags = fcntl(fd, F_GETFL, 0);
        if (flags >= 0 && fcntl(fd, F_SETFL, flags | O_NONBLOCK) == 0) {
            int result = connect(fd, address->ai_addr, address->ai_addrlen);
            if (result == 0) {
                connected = 1;
            } else if (errno == EINPROGRESS) {
                struct pollfd poll_fd;
                int socket_error = 0;
                int64_t now_ms = simple_tls_now_ms();
                int64_t remaining_ms;
                socklen_t socket_error_len = sizeof(socket_error);
                if (now_ms < 0) {
                    close(fd);
                    fd = -1;
                    break;
                }
                remaining_ms = deadline_ms - now_ms;
                if (remaining_ms <= 0) {
                    close(fd);
                    fd = -1;
                    break;
                }
                poll_fd.fd = fd;
                poll_fd.events = POLLOUT;
                poll_fd.revents = 0;
                result = poll(&poll_fd, 1, (int)remaining_ms);
                if (result > 0 && (poll_fd.revents & POLLOUT) &&
                    getsockopt(fd, SOL_SOCKET, SO_ERROR, &socket_error,
                               &socket_error_len) == 0 && socket_error == 0) {
                    connected = 1;
                }
            }
        }
        if (connected) break;
        close(fd);
        fd = -1;
    }
    freeaddrinfo(addresses);
    return fd;
}

static void simple_tls_connection_free(SimpleTlsConnection *connection) {
    if (!connection) return;
    if (connection->ssl) {
        if (!connection->broken) {
            SimpleTlsSigpipeMask sigpipe;
            if (simple_tls_sigpipe_begin(&sigpipe)) {
                (void)SSL_shutdown(connection->ssl);
                simple_tls_sigpipe_end(&sigpipe);
            }
        }
        SSL_free(connection->ssl);
    }
    if (connection->fd >= 0) {
        (void)shutdown(connection->fd, SHUT_RDWR);
        close(connection->fd);
    }
    pthread_cond_destroy(&connection->drained);
    pthread_mutex_destroy(&connection->lock);
    free(connection);
}

static SimpleTlsConnection *simple_tls_acquire(int64_t handle) {
    SimpleTlsConnection *connection = NULL;
    int i;
    pthread_mutex_lock(&simple_tls_table_lock);
    for (i = 0; i < SIMPLE_TLS_MAX_CONNECTIONS; ++i) {
        if (simple_tls_connections[i] &&
            simple_tls_connections[i]->handle == handle &&
            !simple_tls_connections[i]->closing) {
            connection = simple_tls_connections[i];
            connection->refs++;
            break;
        }
    }
    pthread_mutex_unlock(&simple_tls_table_lock);
    if (connection) pthread_mutex_lock(&connection->lock);
    return connection;
}

static void simple_tls_release(SimpleTlsConnection *connection) {
    pthread_mutex_unlock(&connection->lock);
    pthread_mutex_lock(&simple_tls_table_lock);
    connection->refs--;
    if (connection->closing && connection->refs == 0) {
        pthread_cond_signal(&connection->drained);
    }
    pthread_mutex_unlock(&simple_tls_table_lock);
}

static int64_t simple_tls_insert(SimpleTlsConnection *connection) {
    int i;
    int64_t handle = -1;
    pthread_mutex_lock(&simple_tls_table_lock);
    for (i = 0; i < SIMPLE_TLS_MAX_CONNECTIONS; ++i) {
        if (!simple_tls_connections[i]) {
            if (simple_tls_next_handle <= 0 ||
                simple_tls_next_handle >= INT64_MAX) break;
            handle = simple_tls_next_handle++;
            connection->handle = handle;
            simple_tls_connections[i] = connection;
            break;
        }
    }
    pthread_mutex_unlock(&simple_tls_table_lock);
    return handle;
}

static int simple_tls_identity(SSL *ssl, const char *server_name) {
    struct in_addr ipv4;
    struct in6_addr ipv6;
    X509_VERIFY_PARAM *params = SSL_get0_param(ssl);
    if (!params) return 0;
    X509_VERIFY_PARAM_set_hostflags(params, X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS);
    if (inet_pton(AF_INET, server_name, &ipv4) == 1 ||
        inet_pton(AF_INET6, server_name, &ipv6) == 1) {
        return X509_VERIFY_PARAM_set1_ip_asc(params, server_name) == 1;
    }
    if (SSL_set_tlsext_host_name(ssl, server_name) != 1) return 0;
    return SSL_set1_host(ssl, server_name) == 1;
}

static int64_t simple_tls_connect_impl(
    int64_t host_value, int64_t port, int64_t server_name_value,
    int64_t timeout_ms, int numeric_only
) {
    char *host = NULL;
    char *server_name = NULL;
    SimpleTlsConnection *connection = NULL;
    int64_t handle = -1;
    int64_t deadline_ms;
    int64_t started_ms;

    if (port <= 0 || port > 65535 || timeout_ms <= 0) return -1;
    if (timeout_ms > SIMPLE_TLS_TIMEOUT_MS) timeout_ms = SIMPLE_TLS_TIMEOUT_MS;
    host = simple_tls_copy_text(host_value, SIMPLE_TLS_HOST_MAX);
    server_name = simple_tls_copy_text(server_name_value, SIMPLE_TLS_HOST_MAX);
    if (!host || !server_name) goto cleanup;
    pthread_once(&simple_tls_ctx_once, simple_tls_init_ctx);
    if (!simple_tls_client_ctx) goto cleanup;
    started_ms = simple_tls_now_ms();
    if (started_ms < 0) goto cleanup;
    deadline_ms = started_ms + timeout_ms;

    connection = (SimpleTlsConnection *)calloc(1, sizeof(*connection));
    if (!connection) goto cleanup;
    connection->fd = -1;
    connection->broken = 1;
    if (pthread_mutex_init(&connection->lock, NULL) != 0) {
        free(connection);
        connection = NULL;
        goto cleanup;
    }
    if (pthread_cond_init(&connection->drained, NULL) != 0) {
        pthread_mutex_destroy(&connection->lock);
        free(connection);
        connection = NULL;
        goto cleanup;
    }
    connection->fd = simple_tls_connect_socket(
        host, port, deadline_ms, numeric_only
    );
    if (connection->fd < 0) goto cleanup;
    connection->ssl = SSL_new(simple_tls_client_ctx);
    if (!connection->ssl ||
        simple_tls_identity(connection->ssl, server_name) == 0 ||
        SSL_set_fd(connection->ssl, connection->fd) != 1) {
        goto cleanup;
    }
    {
        SimpleTlsSigpipeMask sigpipe;
        X509 *peer;
        if (!simple_tls_sigpipe_begin(&sigpipe)) goto cleanup;
        int connected = 0;
        while (!connected) {
            int result = SSL_connect(connection->ssl);
            int ssl_error;
            if (result == 1) {
                connected = 1;
                break;
            }
            ssl_error = SSL_get_error(connection->ssl, result);
            if (!simple_tls_wait_for_ssl(
                connection->fd, ssl_error, deadline_ms
            )) {
                simple_tls_sigpipe_end(&sigpipe);
                goto cleanup;
            }
        }
        if (!connected) {
            simple_tls_sigpipe_end(&sigpipe);
            goto cleanup;
        }
        simple_tls_sigpipe_end(&sigpipe);
#if OPENSSL_VERSION_NUMBER >= 0x30000000L
        peer = SSL_get1_peer_certificate(connection->ssl);
#else
        peer = SSL_get_peer_certificate(connection->ssl);
#endif
        if (SSL_get_verify_result(connection->ssl) != X509_V_OK || !peer) {
            if (peer) X509_free(peer);
            goto cleanup;
        }
        X509_free(peer);
    }
    connection->broken = 0;
    handle = simple_tls_insert(connection);
    if (handle >= 0) connection = NULL;

cleanup:
    free(host);
    free(server_name);
    simple_tls_connection_free(connection);
    return handle;
}

int64_t rt_tls_client_connect(int64_t host, int64_t port) {
    return simple_tls_connect_impl(
        host, port, host, SIMPLE_TLS_TIMEOUT_MS, 0
    );
}

int64_t rt_tls_client_connect_with_sni(
    int64_t host, int64_t port, int64_t server_name
) {
    return simple_tls_connect_impl(
        host, port, server_name, SIMPLE_TLS_TIMEOUT_MS, 0
    );
}

int64_t rt_tls_client_connect_address_with_sni_timeout(
    int64_t address, int64_t port, int64_t server_name, int64_t timeout_ms
) {
    return simple_tls_connect_impl(
        address, port, server_name, timeout_ms, 1
    );
}

static int64_t simple_tls_write(
    int64_t handle, int64_t data, int64_t timeout_ms
) {
    SimpleTlsConnection *connection;
    const uint8_t *bytes = rt_string_data(data);
    int64_t length = rt_string_len(data);
    int64_t offset = 0;
    int64_t deadline_ms;
    int64_t started_ms;
    if (!bytes || length < 0 || length > SIMPLE_TLS_WRITE_MAX ||
        timeout_ms <= 0) return -1;
    if (timeout_ms > SIMPLE_TLS_TIMEOUT_MS) timeout_ms = SIMPLE_TLS_TIMEOUT_MS;
    started_ms = simple_tls_now_ms();
    if (started_ms < 0) return -1;
    deadline_ms = started_ms + timeout_ms;
    connection = simple_tls_acquire(handle);
    if (!connection) return -1;
    if (connection->broken) {
        simple_tls_release(connection);
        return -1;
    }
    {
        SimpleTlsSigpipeMask sigpipe;
        if (!simple_tls_sigpipe_begin(&sigpipe)) {
            connection->broken = 1;
            simple_tls_release(connection);
            return -1;
        }
        while (offset < length) {
            int64_t now_ms = simple_tls_now_ms();
            if (now_ms < 0 || now_ms >= deadline_ms) {
                connection->broken = 1;
                offset = -1;
                break;
            }
            int written = SSL_write(connection->ssl, bytes + offset,
                                    (int)(length - offset));
            if (written <= 0) {
                int ssl_error = SSL_get_error(connection->ssl, written);
                if (simple_tls_wait_for_ssl(
                    connection->fd, ssl_error, deadline_ms
                )) continue;
                connection->broken = 1;
                offset = -1;
                break;
            }
            offset += written;
        }
        simple_tls_sigpipe_end(&sigpipe);
    }
    simple_tls_release(connection);
    return offset;
}

int64_t rt_tls_client_write(int64_t handle, int64_t data) {
    return simple_tls_write(handle, data, SIMPLE_TLS_TIMEOUT_MS);
}

int64_t rt_tls_client_write_timeout(
    int64_t handle, int64_t data, int64_t timeout_ms
) {
    return simple_tls_write(handle, data, timeout_ms);
}

static int64_t simple_tls_read(
    int64_t handle, int64_t max_bytes, int64_t timeout_ms
) {
    SimpleTlsConnection *connection;
    uint8_t *buffer;
    int read_count = -1;
    int ssl_error = SSL_ERROR_SYSCALL;
    int64_t result;
    int64_t deadline_ms;
    int64_t started_ms;
    if (max_bytes <= 0 || timeout_ms <= 0) return rt_string_new(NULL, 0);
    if (max_bytes > SIMPLE_TLS_READ_MAX) max_bytes = SIMPLE_TLS_READ_MAX;
    if (timeout_ms > SIMPLE_TLS_TIMEOUT_MS) timeout_ms = SIMPLE_TLS_TIMEOUT_MS;
    started_ms = simple_tls_now_ms();
    if (started_ms < 0) return rt_string_new(NULL, 0);
    deadline_ms = started_ms + timeout_ms;
    connection = simple_tls_acquire(handle);
    if (!connection) return rt_string_new(NULL, 0);
    if (connection->broken) {
        simple_tls_release(connection);
        return rt_string_new(NULL, 0);
    }
    buffer = (uint8_t *)malloc((size_t)max_bytes);
    if (!buffer) {
        connection->broken = 1;
        simple_tls_release(connection);
        return rt_string_new(NULL, 0);
    }
    {
        SimpleTlsSigpipeMask sigpipe;
        if (!simple_tls_sigpipe_begin(&sigpipe)) {
            free(buffer);
            connection->broken = 1;
            simple_tls_release(connection);
            return rt_string_new(NULL, 0);
        }
        while (1) {
            int64_t now_ms = simple_tls_now_ms();
            if (now_ms < 0 || now_ms >= deadline_ms) break;
            read_count = SSL_read(connection->ssl, buffer, (int)max_bytes);
            if (read_count > 0) break;
            ssl_error = SSL_get_error(connection->ssl, read_count);
            if (!simple_tls_wait_for_ssl(
                connection->fd, ssl_error, deadline_ms
            )) break;
        }
        simple_tls_sigpipe_end(&sigpipe);
    }
    if (read_count > 0) {
        result = rt_string_new(buffer, (uint64_t)read_count);
    } else {
        if (ssl_error != SSL_ERROR_ZERO_RETURN) connection->broken = 1;
        result = rt_string_new(NULL, 0);
    }
    free(buffer);
    simple_tls_release(connection);
    return result;
}

int64_t rt_tls_client_read(int64_t handle, int64_t max_bytes) {
    return simple_tls_read(handle, max_bytes, SIMPLE_TLS_TIMEOUT_MS);
}

int64_t rt_tls_client_read_timeout(
    int64_t handle, int64_t max_bytes, int64_t timeout_ms
) {
    return simple_tls_read(handle, max_bytes, timeout_ms);
}

int64_t rt_tls_get_protocol_version(int64_t handle) {
    SimpleTlsConnection *connection = simple_tls_acquire(handle);
    const char *version;
    int64_t result;
    if (!connection) return rt_string_new(NULL, 0);
    version = SSL_get_version(connection->ssl);
    if (strcmp(version, "TLSv1.3") == 0 || strcmp(version, "TLSv1.2") == 0) {
        result = rt_string_new((const uint8_t *)version, 7);
    } else {
        result = rt_string_new(NULL, 0);
    }
    simple_tls_release(connection);
    return result;
}

int8_t rt_tls_client_close(int64_t handle) {
    SimpleTlsConnection *connection = NULL;
    int success = 0;
    int i;
    pthread_mutex_lock(&simple_tls_table_lock);
    for (i = 0; i < SIMPLE_TLS_MAX_CONNECTIONS; ++i) {
        if (simple_tls_connections[i] &&
            simple_tls_connections[i]->handle == handle) {
            connection = simple_tls_connections[i];
            connection->closing = 1;
            simple_tls_connections[i] = NULL;
            break;
        }
    }
    while (connection && connection->refs > 0) {
        pthread_cond_wait(&connection->drained, &simple_tls_table_lock);
    }
    pthread_mutex_unlock(&simple_tls_table_lock);
    if (!connection) return 0;
    if (!simple_tls_set_socket_timeouts(connection->fd, 100)) {
        connection->broken = 1;
    }
    success = !connection->broken;
    simple_tls_connection_free(connection);
    return (int8_t)success;
}

int64_t rt_net_https_openssl_local_probe(void) {
    pthread_once(&simple_tls_ctx_once, simple_tls_init_ctx);
    return simple_tls_client_ctx ? 0 : -1;
}

#else

int64_t rt_tls_client_connect(int64_t host, int64_t port) {
    (void)host; (void)port; return -1;
}
int64_t rt_tls_client_connect_with_sni(int64_t host, int64_t port, int64_t server_name) {
    (void)host; (void)port; (void)server_name; return -1;
}
int64_t rt_tls_client_connect_address_with_sni_timeout(int64_t address, int64_t port, int64_t server_name, int64_t timeout_ms) {
    (void)address; (void)port; (void)server_name; (void)timeout_ms; return -1;
}
int64_t rt_tls_client_write(int64_t handle, int64_t data) {
    (void)handle; (void)data; return -1;
}
int64_t rt_tls_client_write_timeout(int64_t handle, int64_t data, int64_t timeout_ms) {
    (void)handle; (void)data; (void)timeout_ms; return -1;
}
int64_t rt_tls_client_read(int64_t handle, int64_t max_bytes) {
    (void)handle; (void)max_bytes; return rt_string_new(NULL, 0);
}
int64_t rt_tls_client_read_timeout(int64_t handle, int64_t max_bytes, int64_t timeout_ms) {
    (void)handle; (void)max_bytes; (void)timeout_ms; return rt_string_new(NULL, 0);
}
int64_t rt_tls_get_protocol_version(int64_t handle) {
    (void)handle; return rt_string_new(NULL, 0);
}
int8_t rt_tls_client_close(int64_t handle) {
    (void)handle; return 0;
}
int64_t rt_net_https_openssl_local_probe(void) { return -1; }

#endif
