/*
 * SimpleOS <sys/epoll.h>
 */

#ifndef _SIMPLEOS_SYS_EPOLL_H
#define _SIMPLEOS_SYS_EPOLL_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>

#define EPOLLIN       0x00000001u
#define EPOLLPRI      0x00000002u
#define EPOLLOUT      0x00000004u
#define EPOLLERR      0x00000008u
#define EPOLLHUP      0x00000010u
#define EPOLLET       0x80000000u
#define EPOLLONESHOT  0x40000000u
#define EPOLL_CLOEXEC 0x80000

#define EPOLL_CTL_ADD 1
#define EPOLL_CTL_DEL 2
#define EPOLL_CTL_MOD 3

typedef union epoll_data {
    void    *ptr;
    int      fd;
    uint32_t u32;
    uint64_t u64;
} epoll_data_t;

struct epoll_event {
    uint32_t events;
    epoll_data_t data;
};

int epoll_create(int size);
int epoll_create1(int flags);
int epoll_ctl(int epfd, int op, int fd, struct epoll_event *event);
int epoll_wait(int epfd, struct epoll_event *events, int maxevents, int timeout);
int epoll_pwait(int epfd, struct epoll_event *events, int maxevents, int timeout, const void *sigmask);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_SYS_EPOLL_H */
