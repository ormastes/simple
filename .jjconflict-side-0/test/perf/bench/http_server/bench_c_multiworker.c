#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/epoll.h>
#include <sys/wait.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#include <fcntl.h>
#include <errno.h>
#include <signal.h>

static const char RESP[] =
    "HTTP/1.1 200 OK\r\n"
    "Content-Length: 13\r\n"
    "Connection: keep-alive\r\n"
    "\r\n"
    "Hello, World!";
static const int RESP_LEN = sizeof(RESP) - 1;

static void set_nonblocking(int fd) {
    fcntl(fd, F_SETFL, fcntl(fd, F_GETFL, 0) | O_NONBLOCK);
}

static void worker_loop(int worker_id) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    int val = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &val, sizeof(val));
    setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &val, sizeof(val));

    struct sockaddr_in sa = {0};
    sa.sin_family = AF_INET;
    sa.sin_port = htons(9090);
    sa.sin_addr.s_addr = INADDR_ANY;
    bind(fd, (struct sockaddr*)&sa, sizeof(sa));
    set_nonblocking(fd);
    listen(fd, 1024);

    int epfd = epoll_create1(0);
    struct epoll_event ev = {.events = EPOLLIN, .data.fd = fd};
    epoll_ctl(epfd, EPOLL_CTL_ADD, fd, &ev);

    struct epoll_event events[256];
    char buf[4096];

    for (;;) {
        int n = epoll_wait(epfd, events, 256, 1000);
        for (int i = 0; i < n; i++) {
            int efd = events[i].data.fd;
            if (efd == fd) {
                for (int j = 0; j < 64; j++) {
                    int cfd = accept(fd, NULL, NULL);
                    if (cfd < 0) break;
                    set_nonblocking(cfd);
                    val = 1;
                    setsockopt(cfd, IPPROTO_TCP, TCP_NODELAY, &val, sizeof(val));
                    ev.events = EPOLLIN;
                    ev.data.fd = cfd;
                    epoll_ctl(epfd, EPOLL_CTL_ADD, cfd, &ev);
                }
            } else {
                ssize_t nr = read(efd, buf, sizeof(buf));
                if (nr > 0) {
                    write(efd, RESP, RESP_LEN);
                } else {
                    close(efd);
                }
            }
        }
    }
}

int main(int argc, char** argv) {
    int nworkers = 32;
    if (argc > 1) nworkers = atoi(argv[1]);

    signal(SIGCHLD, SIG_IGN);
    printf("Multi-worker C server: %d workers, SO_REUSEPORT, port 9090\n", nworkers);

    for (int i = 1; i < nworkers; i++) {
        if (fork() == 0) {
            worker_loop(i);
            _exit(0);
        }
    }
    worker_loop(0);
    return 0;
}
