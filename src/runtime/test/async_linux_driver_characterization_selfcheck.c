/* Characterization selfcheck for the Linux spl_driver backends.
 *
 * Pins CURRENT observable behaviour of platform/async_linux_epoll.c and
 * platform/async_linux_uring.c so that internal dedup refactors can be proven
 * behaviour-preserving. Compiled once per backend:
 *
 *   epoll: clang-18 -std=gnu11 -I src/runtime/platform \
 *            src/runtime/test/async_linux_driver_characterization_selfcheck.c \
 *            src/runtime/platform/async_linux_epoll.c -lpthread
 *   uring: add -DCHAR_URING -DSPL_HAS_IO_URING -I<liburing include> \
 *            src/runtime/platform/async_linux_uring.c -l:liburing.so.2
 *
 * Run under ASan+UBSan and TSan by scripts/check/check-linux-dedup-characterization.shs.
 * Fails (never skips) if the backend cannot be created. */
#define _GNU_SOURCE
#include "async_driver.h"
#include "linux_char_harness.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <unistd.h>

/* Legacy epoll FFI in async_linux_epoll.c references these; unused here. */
typedef struct SplArray SplArray;
SplArray* spl_array_new(void) { return NULL; }
void spl_array_push_i64(SplArray* a, int64_t n) { (void)a; (void)n; }

static spl_driver* D;
#define V (D->vtable)

#ifdef CHAR_URING
#define BACKEND "uring"
static spl_driver* make_driver(int64_t depth) { return spl_driver_create_uring(depth); }
#else
#define BACKEND "epoll"
static spl_driver* make_driver(int64_t depth) { return spl_driver_create_epoll(depth); }
#endif

static int64_t gather(spl_driver* d, spl_completion* out, int64_t want, int ms) {
    int64_t got = 0, end = char_now_ms() + ms;
    while (got < want && char_now_ms() < end) {
        d->vtable->flush(d);
        int64_t n = d->vtable->poll(d, out + got, want - got, 20);
        if (n > 0) got += n;
    }
    return got;
}
static int64_t one(spl_completion* c, int ms) { return gather(D, c, 1, ms); }

static void pair(int sv[2]) {
    int rc = socketpair(AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0, sv);
    if (rc != 0) { perror("socketpair"); exit(2); }
}

static int tmpfile_with(const char* content) {
    const char* dir = getenv("TMPDIR");
    char path[4096];
    snprintf(path, sizeof path, "%s/charXXXXXX", dir ? dir : ".");
    int fd = mkstemp(path);
    if (fd < 0) { perror("mkstemp"); exit(2); }
    unlink(path);
    if (content) (void)!write(fd, content, strlen(content));
    return fd;
}

static int tcp_listener(int* port) {
    int l = socket(AF_INET, SOCK_STREAM | SOCK_NONBLOCK | SOCK_CLOEXEC, 0);
    struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    bind(l, (struct sockaddr*)&sa, sizeof sa);
    listen(l, 8);
    socklen_t len = sizeof sa;
    getsockname(l, (struct sockaddr*)&sa, &len);
    *port = ntohs(sa.sin_port);
    return l;
}

/* ---------------- common network cases ---------------- */

static void t_recv_data(void) {
    int sv[2]; pair(sv);
    (void)!write(sv[1], "hello", 5);
    int64_t id = V->submit_recv(D, sv[0], 64);
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id);
    CHECK(c.result == 5);
    CHECK(c.data_len == 5);
    CHECK(c.data && memcmp(c.data, "hello", 5) == 0);
    free(c.data);
    close(sv[0]); close(sv[1]);
}

static void t_recv_short(void) {
    int sv[2]; pair(sv);
    (void)!write(sv[1], "abc", 3);
    int64_t id = V->submit_recv(D, sv[0], 4096);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == 3 && c.data_len == 3);
    free(c.data);
    close(sv[0]); close(sv[1]);
}

static void t_recv_eof(void) {
    int sv[2]; pair(sv);
    close(sv[1]);
    int64_t id = V->submit_recv(D, sv[0], 64);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == 0);
    CHECK(c.data == NULL && c.data_len == 0);
    close(sv[0]);
}

static void t_recv_rearm_same_fd(void) {
    int sv[2]; pair(sv);
    for (int round = 0; round < 3; round++) {
        (void)!write(sv[1], "z", 1);
        int64_t id = V->submit_recv(D, sv[0], 8);
        spl_completion c = {0};
        CHECK(one(&c, 1000) == 1);
        CHECK(c.id == id && c.result == 1);
        free(c.data);
    }
    close(sv[0]); close(sv[1]);
}

static void t_send(void) {
    int sv[2]; pair(sv);
    int64_t id = V->submit_send(D, sv[0], "abc", 3);
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == 3);
    CHECK(c.data == NULL);
    char buf[8] = {0};
    CHECK(read(sv[1], buf, sizeof buf) == 3 && memcmp(buf, "abc", 3) == 0);
    close(sv[0]); close(sv[1]);
}

static void t_send_epipe(void) {
    int sv[2]; pair(sv);
    close(sv[1]);
    int64_t id = V->submit_send(D, sv[0], "abc", 3);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == -EPIPE);
    close(sv[0]);
}

static void t_send_short_write(void) {
    int sv[2]; pair(sv);
    int sz = 4096;
    setsockopt(sv[0], SOL_SOCKET, SO_SNDBUF, &sz, sizeof sz);
    const int64_t len = 4 * 1024 * 1024;
    char* big = calloc(1, (size_t)len);
    int64_t id = V->submit_send(D, sv[0], big, len);
    free(big); /* the driver copies the payload */
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result > 0 && c.result < len); /* short write */
    close(sv[0]); close(sv[1]);
}

static void t_accept(void) {
    int port = 0, l = tcp_listener(&port);
    int64_t id = V->submit_accept(D, l);
    CHECK(id > 0);
    V->flush(D);
    int cl = socket(AF_INET, SOCK_STREAM, 0);
    struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_port = htons((uint16_t)port);
    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    CHECK(connect(cl, (struct sockaddr*)&sa, sizeof sa) == 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result >= 0);
    if (c.result >= 0) close((int)c.result);
    close(cl); close(l);
}

static void t_accept_emfile(void) {
    int port = 0, l = tcp_listener(&port);
    int cl = socket(AF_INET, SOCK_STREAM, 0);
    struct rlimit old; getrlimit(RLIMIT_NOFILE, &old);
    int64_t id = V->submit_accept(D, l);
    V->flush(D);
    struct sockaddr_in sa; memset(&sa, 0, sizeof sa);
    sa.sin_family = AF_INET; sa.sin_port = htons((uint16_t)port);
    sa.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    CHECK(connect(cl, (struct sockaddr*)&sa, sizeof sa) == 0);
    struct rlimit lim = old; lim.rlim_cur = char_first_free_fd();
    CHECK(setrlimit(RLIMIT_NOFILE, &lim) == 0);
    spl_completion c = {0};
    int64_t n = one(&c, 1000);
    setrlimit(RLIMIT_NOFILE, &old);
    CHECK(n == 1);
#ifdef CHAR_URING
    /* Observed: an accept armed (flushed) before the limit was lowered still
     * installs an fd under io_uring. */
    CHECK(c.id == id && c.result >= 0);
#else
    CHECK(c.id == id && c.result == -EMFILE);  /* accept4 runs at poll time */
#endif
    if (c.result >= 0) close((int)c.result);
    close(cl); close(l);
}

static void t_connect_ok(void) {
    int port = 0, l = tcp_listener(&port);
    int s = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    int64_t id = V->submit_connect(D, s, "127.0.0.1", port);
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == 0);
    close(s); close(l);
}

static void t_connect_refused(void) {
    int port = 0, l = tcp_listener(&port);
    close(l); /* nothing listens on port now */
    int s = socket(AF_INET, SOCK_STREAM | SOCK_CLOEXEC, 0);
    int64_t id = V->submit_connect(D, s, "127.0.0.1", port);
    if (id < 0) {
        CHECK(id == -ECONNREFUSED);
    } else {
        spl_completion c = {0};
        CHECK(one(&c, 1000) == 1);
        CHECK(c.id == id && c.result == -ECONNREFUSED);
    }
    close(s);
}

static void t_timeout(void) {
    int64_t t0 = char_now_ms();
    int64_t id = V->submit_timeout(D, 30);
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id);
#ifdef CHAR_URING
    CHECK(c.result == -ETIME);
#else
    CHECK(c.result == 0);
#endif
    CHECK(char_now_ms() - t0 >= 25);
}

static void t_multi_and_max(void) {
    int a[2], b[2]; pair(a); pair(b);
    (void)!write(a[1], "1", 1); (void)!write(b[1], "2", 1);
    int64_t ia = V->submit_recv(D, a[0], 8), ib = V->submit_recv(D, b[0], 8);
    CHECK(ia > 0 && ib > ia);
    V->flush(D);
    usleep(30000);
    spl_completion out[4] = {{0}};
    int64_t n1 = V->poll(D, out, 1, 100);         /* max < ready */
    CHECK(n1 == 1);
    int64_t n2 = gather(D, out + 1, 1, 1000);     /* the other is still pending */
    CHECK(n2 == 1);
    CHECK((out[0].id == ia && out[1].id == ib) || (out[0].id == ib && out[1].id == ia));
    free(out[0].data); free(out[1].data);
    close(a[0]); close(a[1]); close(b[0]); close(b[1]);
}

static void t_multi_one_poll(void) {
    int a[2], b[2]; pair(a); pair(b);
    (void)!write(a[1], "1", 1); (void)!write(b[1], "2", 1);
    V->submit_recv(D, a[0], 8); V->submit_recv(D, b[0], 8);
    V->flush(D);
    usleep(30000);
    spl_completion out[8] = {{0}};
    int64_t n = V->poll(D, out, 8, 100);
    CHECK(n == 2);
    for (int64_t i = 0; i < n; i++) { CHECK(out[i].result == 1); free(out[i].data); }
    close(a[0]); close(a[1]); close(b[0]); close(b[1]);
}

/* recv + send pending on ONE fd that is both readable and writable. */
static void t_same_fd_recv_send(void) {
    int sv[2]; pair(sv);
    (void)!write(sv[1], "r", 1);
    int64_t rid = V->submit_recv(D, sv[0], 8);
    int64_t sid = V->submit_send(D, sv[0], "s", 1);
    CHECK(rid > 0 && sid > rid);
    V->flush(D);
    usleep(30000);
    spl_completion out[8] = {{0}};
    int64_t n = V->poll(D, out, 8, 100);
#ifdef CHAR_URING
    /* io_uring completes both independently. */
    CHECK(n == 2);
    for (int64_t i = 0; i < n; i++) { CHECK(out[i].result == 1); free(out[i].data); }
#else
    /* epoll: the send's EPOLL_CTL_MOD replaced the recv's interest, the
     * event loop handles one op per fd per event (continue), and then
     * removes the fd: exactly one completion, the send. The recv stays
     * pending until cancelled. */
    CHECK(n == 1);
    CHECK(out[0].id == sid && out[0].result == 1);
    CHECK(V->cancel(D, rid));
    int64_t n2 = V->poll(D, out, 8, 50);
    CHECK(n2 == 0);
#endif
    close(sv[0]); close(sv[1]);
}

static void t_cancel(void) {
    int sv[2]; pair(sv);
    int64_t id = V->submit_recv(D, sv[0], 8);
    CHECK(V->cancel(D, id));
    spl_completion out[4] = {{0}};
#ifdef CHAR_URING
    int64_t n = gather(D, out, 1, 1000);
    CHECK(n == 1);
    CHECK(out[0].id == id && out[0].result == -ECANCELED); /* no id-0 phantom */
    CHECK(out[0].data == NULL);
    CHECK(V->poll(D, out, 4, 30) == 0);
#else
    CHECK(V->poll(D, out, 4, 30) == 0);
    CHECK(!V->cancel(D, id));       /* already gone */
    CHECK(!V->cancel(D, 999999));   /* unknown id */
#endif
    close(sv[0]); close(sv[1]);
}

static volatile sig_atomic_t g_alarm;
static void on_alarm(int s) { (void)s; g_alarm = 1; }

static void t_poll_eintr(void) {
    int sv[2]; pair(sv);
    int64_t id = V->submit_recv(D, sv[0], 8);
    V->flush(D);
    struct sigaction sa; memset(&sa, 0, sizeof sa);
    sa.sa_handler = on_alarm; /* no SA_RESTART */
    struct sigaction old; sigaction(SIGALRM, &sa, &old);
    struct itimerval it; memset(&it, 0, sizeof it);
    it.it_value.tv_usec = 30000;
    g_alarm = 0;
    setitimer(ITIMER_REAL, &it, NULL);
    spl_completion out[4] = {{0}};
    int64_t t0 = char_now_ms();
    int64_t n = V->poll(D, out, 4, 400);
    int64_t el = char_now_ms() - t0;
    sigaction(SIGALRM, &old, NULL);
    CHECK(g_alarm == 1);
    CHECK(el < 350);           /* interrupted, not a full timeout */
#ifdef CHAR_URING
    CHECK(n == -EINTR);
#else
    CHECK(n == 0);             /* EINTR -> count (0) */
#endif
    (void)V->cancel(D, id);
    (void)gather(D, out, 1, 200);
    close(sv[0]); close(sv[1]);
}

/* ---------------- file / sendfile cases ---------------- */

static void t_file_read(void) {
    int fd = tmpfile_with("0123456789");
    spl_completion c = {0};
    int64_t id = V->submit_read(D, fd, 4096, 0);          /* short read */
    CHECK(id > 0);
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == 10 && c.data_len == 10);
    CHECK(c.data && memcmp(c.data, "0123456789", 10) == 0);
    free(c.data);
    memset(&c, 0, sizeof c);
    id = V->submit_read(D, fd, 3, 4);
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == 3 && c.data && memcmp(c.data, "456", 3) == 0);
    free(c.data);
    memset(&c, 0, sizeof c);
    id = V->submit_read(D, fd, 8, 10);                     /* EOF */
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == 0 && c.data == NULL && c.data_len == 0);
    close(fd);
}

static void t_file_read_ebadf(void) {
    spl_completion c = {0};
    int64_t id = V->submit_read(D, 999, 8, 0);
    CHECK(id > 0);
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == -EBADF && c.data == NULL);
}

static void t_file_write(void) {
    int fd = tmpfile_with("0123456789");
    spl_completion c = {0};
    int64_t id = V->submit_write(D, fd, "AB", 2, 4);
    CHECK(id > 0);
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == 2 && c.data == NULL);
    char buf[16] = {0};
    CHECK(pread(fd, buf, 10, 0) == 10 && memcmp(buf, "0123AB6789", 10) == 0);
    memset(&c, 0, sizeof c);
    id = V->submit_write(D, 999, "AB", 2, 0);
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == -EBADF);
    close(fd);
}

static void t_open_emfile(void) {
    int fd = tmpfile_with("x");
    char path[64]; snprintf(path, sizeof path, "/proc/self/fd/%d", fd);
    struct rlimit old; getrlimit(RLIMIT_NOFILE, &old);
    struct rlimit lim = old; lim.rlim_cur = char_first_free_fd();
    int64_t id = V->submit_open(D, path, O_RDONLY, 0);
    CHECK(id > 0);
    CHECK(setrlimit(RLIMIT_NOFILE, &lim) == 0);
    spl_completion c = {0};
    int64_t n = one(&c, 2000);
    setrlimit(RLIMIT_NOFILE, &old);
    CHECK(n == 1);
    CHECK(c.id == id && c.result == -EMFILE);
    if (c.result >= 0) close((int)c.result);
    close(fd);
}

static void t_sendfile(void) {
    int fd = tmpfile_with("0123456789");
    int sv[2]; pair(sv);
    int64_t id = V->submit_sendfile(D, sv[0], fd, 2, 5);
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 2000) == 1);
    CHECK(c.id == id && c.result == 5);
    char buf[8] = {0};
    CHECK(read(sv[1], buf, sizeof buf) == 5 && memcmp(buf, "23456", 5) == 0);
    close(sv[0]); close(sv[1]); close(fd);
}

static void t_many_ids_monotonic(void) {
    int sv[2]; pair(sv);
    int64_t last = 0; int ok = 1;
    for (int i = 0; i < 300; i++) {
        (void)!write(sv[1], "q", 1);
        int64_t id = V->submit_recv(D, sv[0], 4);
        if (id <= last) ok = 0;
        last = id;
        spl_completion c = {0};
        if (one(&c, 1000) != 1 || c.id != id || c.result != 1) ok = 0;
        free(c.data);
    }
    CHECK(ok);
    close(sv[0]); close(sv[1]);
}

#ifdef CHAR_URING
/* ---------------- io_uring argument contract ---------------- */

static void t_uring_einval(void) {
    int sv[2]; pair(sv);
    int64_t big = (int64_t)UINT_MAX + 1;
    CHECK(V->submit_recv(D, sv[0], 0) == -EINVAL);
    CHECK(V->submit_recv(D, sv[0], -1) == -EINVAL);
    CHECK(V->submit_recv(D, sv[0], big) == -EINVAL);
    CHECK(V->submit_read(D, sv[0], 0, 0) == -EINVAL);
    CHECK(V->submit_read(D, sv[0], 8, -1) == -EINVAL);
    CHECK(V->submit_read(D, sv[0], big, 0) == -EINVAL);
    CHECK(V->submit_send(D, sv[0], "x", -1) == -EINVAL);
    CHECK(V->submit_send(D, sv[0], NULL, 1) == -EINVAL);
    CHECK(V->submit_send(D, sv[0], "x", big) == -EINVAL);
    CHECK(V->submit_write(D, sv[0], "x", 0, 0) == -EINVAL);   /* write(0) */
    CHECK(V->submit_write(D, sv[0], NULL, 1, 0) == -EINVAL);
    CHECK(V->submit_write(D, sv[0], "x", 1, -1) == -EINVAL);
    CHECK(V->submit_write(D, sv[0], "x", big, 0) == -EINVAL);
    CHECK(V->submit_timeout(D, -1) == -EINVAL);
    CHECK(V->submit_accept(D, -1) == -EINVAL);
    close(sv[0]); close(sv[1]);
}

static void t_uring_send_zero_null(void) {
    int sv[2]; pair(sv);
    int64_t id = V->submit_send(D, sv[0], NULL, 0);           /* send(0, NULL) OK */
    CHECK(id > 0);
    spl_completion c = {0};
    CHECK(one(&c, 1000) == 1);
    CHECK(c.id == id && c.result == 0 && c.data == NULL);
    close(sv[0]); close(sv[1]);
}

static void t_uring_ring_full(void) {
    spl_driver* r = make_driver(16);   /* clamps to 16 SQEs */
    CHECK(r != NULL);
    if (!r) return;
    int sv[2]; pair(sv);
    int fd = tmpfile_with("abcdef");
    int64_t last = 0; int ok = 1;
    for (int i = 0; i < 16; i++) {
        int64_t id = r->vtable->submit_recv(r, sv[0], 8);
        if (id != last + 1) ok = 0;
        last = id;
    }
    CHECK(ok);
    CHECK(r->vtable->submit_recv(r, sv[0], 8) == -EAGAIN);
    CHECK(r->vtable->submit_read(r, fd, 8, 0) == -EAGAIN);
    CHECK(r->vtable->submit_send(r, sv[0], "x", 1) == -EAGAIN);
    CHECK(r->vtable->submit_write(r, fd, "x", 1, 0) == -EAGAIN);
    CHECK(r->vtable->submit_timeout(r, 10) == -EAGAIN);
    CHECK(!r->vtable->cancel(r, last));
    CHECK(r->vtable->flush(r) == 16);
    /* An -EAGAIN submit consumed no id. */
    CHECK(r->vtable->submit_read(r, fd, 3, 0) == last + 1);
    spl_completion c = {0};
    CHECK(gather(r, &c, 1, 1000) == 1);
    CHECK(c.id == last + 1 && c.result == 3 && c.data && memcmp(c.data, "abc", 3) == 0);
    free(c.data);
    r->vtable->destroy(r);  /* 16 pending recvs: LSan proves buffers reclaimed */
    close(sv[0]); close(sv[1]); close(fd);
}
#endif

int main(void) {
    signal(SIGPIPE, SIG_IGN);
    D = make_driver(256);
    CHECK(D != NULL);
    if (!D) DONE("async_" BACKEND "_characterization");
    CHECK(strcmp(V->backend_name(D), BACKEND) == 0 ||
          strcmp(V->backend_name(D), "io_uring") == 0);

    t_recv_data();
    t_recv_short();
    t_recv_eof();
    t_recv_rearm_same_fd();
    t_send();
    t_send_epipe();
    t_send_short_write();
    t_accept();
    t_accept_emfile();
    t_connect_ok();
    t_connect_refused();
    t_timeout();
    t_multi_and_max();
    t_multi_one_poll();
    t_same_fd_recv_send();
    t_cancel();
    t_poll_eintr();
    t_file_read();
    t_file_read_ebadf();
    t_file_write();
    t_open_emfile();
    t_sendfile();
    t_many_ids_monotonic();
#ifdef CHAR_URING
    t_uring_einval();
    t_uring_send_zero_null();
    t_uring_ring_full();
#endif
    V->destroy(D);
    DONE("async_" BACKEND "_characterization");
}
