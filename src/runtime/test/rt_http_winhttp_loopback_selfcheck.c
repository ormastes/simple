/* Regression for windows_core_http_client_unavailable_2026_10_27: drive the
 * real Windows rt_http_perform (WinHTTP provider) against a loopback Winsock
 * server. Checks text + exact binary bodies (incl. NUL/0xFF bytes), status,
 * reason, response headers, request body round-trip, no redirect following,
 * connection errors and the overall timeout. POSIX hosts compile to a no-op
 * pass because the socket provider is covered by the existing HTTP specs. */
#include "../runtime_native.c"
#include <stdio.h>

#if defined(_WIN32)
#include <winsock2.h>

static SOCKET g_listen = INVALID_SOCKET;

static void serve_one(SOCKET client) {
    char req[4096]; int got = 0, n;
    while (got < (int)sizeof(req) - 1 && (n = recv(client, req + got, (int)sizeof(req) - 1 - got, 0)) > 0) {
        got += n; req[got] = 0;
        char* end = strstr(req, "\r\n\r\n");
        if (!end) continue;
        const char* cl = strstr(req, "Content-Length: ");
        int want = cl ? atoi(cl + 16) : 0;
        if (got - (int)(end + 4 - req) >= want) break;
    }
    if (strncmp(req, "GET /bin", 8) == 0) {
        static const unsigned char payload[] = {0x00, 0xFF, 0x10, 0x00, 'z', 0x80};
        const char* head = "HTTP/1.1 200 OK\r\nContent-Type: application/octet-stream\r\nContent-Length: 6\r\nX-Probe: yes\r\n\r\n";
        send(client, head, (int)strlen(head), 0);
        send(client, (const char*)payload, 6, 0);
    } else if (strncmp(req, "GET /redir", 10) == 0) {
        const char* r = "HTTP/1.1 302 Found\r\nLocation: /bin\r\nContent-Length: 0\r\n\r\n";
        send(client, r, (int)strlen(r), 0);
    } else if (strncmp(req, "POST /echo", 10) == 0) {
        char* body = strstr(req, "\r\n\r\n") + 4;
        int len = got - (int)(body - req);
        char head[160];
        int hl = snprintf(head, sizeof(head), "HTTP/1.1 201 Created\r\nContent-Length: %d\r\n\r\n", len);
        send(client, head, hl, 0);
        send(client, body, len, 0);
    } else if (strncmp(req, "GET /slow", 9) == 0) {
        Sleep(3000);
    } else {
        const char* r = "HTTP/1.1 404 Not Found\r\nContent-Length: 4\r\n\r\nnope";
        send(client, r, (int)strlen(r), 0);
    }
    shutdown(client, SD_SEND);
    closesocket(client);
}

static DWORD WINAPI server_main(LPVOID arg) {
    (void)arg;
    for (;;) {
        SOCKET c = accept(g_listen, NULL, NULL);
        if (c == INVALID_SOCKET) return 0;
        serve_one(c);
    }
}

static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); failures++; } } while (0)

static int run(const char* method, const char* url, const uint8_t* body, size_t body_len,
               int64_t timeout_ms, int64_t* status, uint8_t** out, size_t* out_len,
               uint8_t** reason, size_t* reason_len, uint8_t** hdrs, size_t* hdrs_len, char* err) {
    return rt_http_perform(method, url, NULL, body, body_len, timeout_ms, status, out, out_len,
                           reason, reason_len, hdrs, hdrs_len, err, 160);
}

int main(void) {
    WSADATA wsa; WSAStartup(MAKEWORD(2, 2), &wsa);
    g_listen = socket(AF_INET, SOCK_STREAM, IPPROTO_TCP);
    struct sockaddr_in addr; memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET; addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK); addr.sin_port = 0;
    bind(g_listen, (struct sockaddr*)&addr, sizeof(addr));
    int alen = sizeof(addr); getsockname(g_listen, (struct sockaddr*)&addr, &alen);
    listen(g_listen, 8);
    int port = ntohs(addr.sin_port);
    CreateThread(NULL, 0, server_main, NULL, 0, NULL);
    char url[128]; int64_t st; uint8_t *out, *reason, *hdrs; size_t out_len, reason_len, hdrs_len; char err[160];

    snprintf(url, sizeof(url), "http://127.0.0.1:%d/bin", port);
    int ok = run("GET", url, NULL, 0, 5000, &st, &out, &out_len, &reason, &reason_len, &hdrs, &hdrs_len, err);
    static const unsigned char expect[] = {0x00, 0xFF, 0x10, 0x00, 'z', 0x80};
    CHECK(ok, err);
    CHECK(ok && st == 200, "binary status 200");
    CHECK(ok && out_len == 6 && memcmp(out, expect, 6) == 0, "exact binary body");
    CHECK(ok && reason_len == 2 && memcmp(reason, "OK", 2) == 0, "reason OK");
    CHECK(ok && hdrs && strstr((char*)hdrs, "X-Probe: yes") && strncmp((char*)hdrs, "HTTP/", 5) != 0, "headers block");
    if (ok) { free(out); free(reason); free(hdrs); }

    snprintf(url, sizeof(url), "http://127.0.0.1:%d/redir", port);
    ok = run("GET", url, NULL, 0, 5000, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    CHECK(ok && st == 302, "redirect not followed");
    if (ok) free(out);

    snprintf(url, sizeof(url), "http://127.0.0.1:%d/echo", port);
    static const uint8_t post[] = {'h', 'i', 0x00, 0xFE, '\n'};
    ok = run("POST", url, post, sizeof(post), 5000, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    CHECK(ok && st == 201 && out_len == sizeof(post) && memcmp(out, post, sizeof(post)) == 0, "binary POST echo");
    if (ok) free(out);

    snprintf(url, sizeof(url), "http://127.0.0.1:%d/missing", port);
    ok = run("GET", url, NULL, 0, 5000, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    CHECK(ok && st == 404 && out_len == 4 && memcmp(out, "nope", 4) == 0, "text 404 body");
    if (ok) free(out);

    snprintf(url, sizeof(url), "http://127.0.0.1:%d/slow", port);
    DWORD t0 = GetTickCount();
    ok = run("GET", url, NULL, 0, 500, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    DWORD dt = GetTickCount() - t0;
    if (!(!ok && st == -1 && strstr(err, "timed out") && dt < 2500)) printf("timeout: ok=%d st=%lld dt=%lu err=%s\n", ok, (long long)st, (unsigned long)dt, err);
    CHECK(!ok && st == -1 && strstr(err, "timed out") && dt < 2500, "timeout bound");
    if (ok) free(out);

    ok = run("GET", "http://127.0.0.1:1/", NULL, 0, 3000, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    CHECK(!ok && st == -1, "connection refused is an error");
    if (ok) free(out);

    ok = run("GET", "ftp://127.0.0.1/", NULL, 0, 0, &st, &out, &out_len, NULL, NULL, NULL, NULL, err);
    CHECK(!ok, "non-http scheme rejected");

    closesocket(g_listen);
    printf(failures ? "rt_http_winhttp_loopback_selfcheck: %d FAILED\n"
                    : "rt_http_winhttp_loopback_selfcheck: PASS%.0d\n", failures);
    return failures ? 1 : 0;
}
#else
int main(void) { printf("rt_http_winhttp_loopback_selfcheck: PASS (non-Windows no-op)\n"); return 0; }
#endif
