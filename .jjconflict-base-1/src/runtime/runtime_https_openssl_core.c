#include <stdint.h>

#if defined(__has_include)
#if __has_include(<openssl/ssl.h>) && __has_include(<openssl/err.h>)
#define SIMPLE_CORE_HAS_OPENSSL 1
#endif
#endif

#if SIMPLE_CORE_HAS_OPENSSL && !defined(_WIN32)
#include <arpa/inet.h>
#include <netinet/in.h>
#include <openssl/err.h>
#include <openssl/ssl.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>
#endif

int64_t rt_net_https_openssl_local_probe(void) {
#if SIMPLE_CORE_HAS_OPENSSL && !defined(_WIN32)
    SSL_library_init();
    SSL_CTX* ctx = SSL_CTX_new(TLS_client_method());
    if (!ctx) return -2;

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) {
        SSL_CTX_free(ctx);
        return -3;
    }

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(443);
    inet_pton(AF_INET, "127.0.0.1", &addr.sin_addr);

    if (connect(fd, (struct sockaddr*)&addr, sizeof(addr)) == 0) {
        SSL* ssl = SSL_new(ctx);
        if (ssl) {
            SSL_set_fd(ssl, fd);
            SSL_connect(ssl);
            SSL_shutdown(ssl);
            SSL_free(ssl);
        }
    }

    close(fd);
    SSL_CTX_free(ctx);
    return 0;
#else
    return -1;
#endif
}
