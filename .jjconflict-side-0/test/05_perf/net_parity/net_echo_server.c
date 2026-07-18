#include <arpa/inet.h>
#include <errno.h>
#include <netinet/tcp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

static void die(const char *message) {
    perror(message);
    exit(1);
}

int main(int argc, char **argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s <port> <ready-file>\n", argv[0]);
        return 2;
    }

    signal(SIGPIPE, SIG_IGN);

    int port = atoi(argv[1]);
    const char *ready_file = argv[2];
    int listener = socket(AF_INET, SOCK_STREAM, 0);
    if (listener < 0) die("socket");

    int enabled = 1;
    setsockopt(listener, SOL_SOCKET, SO_REUSEADDR, &enabled, sizeof(enabled));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons((uint16_t)port);

    if (bind(listener, (struct sockaddr *)&addr, sizeof(addr)) != 0) die("bind");
    if (listen(listener, 16) != 0) die("listen");

    FILE *ready = fopen(ready_file, "w");
    if (ready != NULL) {
        fputs("ready\n", ready);
        fclose(ready);
    }

    for (;;) {
        int client = accept(listener, NULL, NULL);
        if (client < 0) {
            if (errno == EINTR) continue;
            die("accept");
        }
        setsockopt(client, IPPROTO_TCP, TCP_NODELAY, &enabled, sizeof(enabled));

        char buffer[65536];
        for (;;) {
            ssize_t got = read(client, buffer, sizeof(buffer));
            if (got == 0) break;
            if (got < 0) {
                if (errno == EINTR) continue;
                break;
            }
            ssize_t offset = 0;
            while (offset < got) {
                ssize_t sent = write(client, buffer + offset, (size_t)(got - offset));
                if (sent <= 0) break;
                offset += sent;
            }
        }
        close(client);
    }
}
