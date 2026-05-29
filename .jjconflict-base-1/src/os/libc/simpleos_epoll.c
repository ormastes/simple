/*
 * SimpleOS epoll shim.
 *
 * Kernel fd readiness lives behind poll(2) for now. epoll instances are
 * process-local libc tables that translate watched fds into pollfd batches.
 */

#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stdint.h>
#include <string.h>
#include <sys/epoll.h>

#define SIMPLEOS_EPOLL_BASE 10000
#define SIMPLEOS_EPOLL_MAX_INSTANCES 16
#define SIMPLEOS_EPOLL_MAX_WATCHES 64
#define SIMPLEOS_EPOLL_FD_SCAN_LIMIT 256

struct simpleos_epoll_watch {
    int used;
    int fd;
    uint64_t ofd_token;
    short last_revents;
    struct epoll_event event;
};

struct simpleos_epoll_instance {
    int used;
    struct simpleos_epoll_watch watches[SIMPLEOS_EPOLL_MAX_WATCHES];
};

static struct simpleos_epoll_instance g_epoll[SIMPLEOS_EPOLL_MAX_INSTANCES];

static int epoll_index(int epfd) {
    int idx = epfd - SIMPLEOS_EPOLL_BASE;
    if (idx < 0 || idx >= SIMPLEOS_EPOLL_MAX_INSTANCES || !g_epoll[idx].used) {
        errno = EBADF;
        return -1;
    }
    return idx;
}

static int epoll_index_noerrno(int epfd) {
    int idx = epfd - SIMPLEOS_EPOLL_BASE;
    if (idx < 0 || idx >= SIMPLEOS_EPOLL_MAX_INSTANCES || !g_epoll[idx].used) {
        return -1;
    }
    return idx;
}

static short epoll_to_poll(uint32_t events) {
    short out = 0;
    if (events & EPOLLIN) out |= POLLIN;
    if (events & EPOLLOUT) out |= POLLOUT;
    if (events & EPOLLPRI) out |= POLLPRI;
    return out;
}

static uint32_t poll_to_epoll(short revents) {
    uint32_t out = 0;
    if (revents & POLLIN) out |= EPOLLIN;
    if (revents & POLLOUT) out |= EPOLLOUT;
    if (revents & POLLPRI) out |= EPOLLPRI;
    if (revents & POLLERR) out |= EPOLLERR;
    if (revents & POLLHUP) out |= EPOLLHUP;
    if (revents & POLLNVAL) out |= EPOLLERR;
    return out;
}

static uint64_t simpleos_fd_ofd_token(int fd) {
    int saved_errno = errno;
    int token = fcntl(fd, F_SIMPLEOS_GET_OFD, 0);
    if (token < 0) {
        errno = saved_errno;
        return 0;
    }
    errno = saved_errno;
    return (uint64_t)(uint32_t)token;
}

static int simpleos_find_fd_for_ofd(uint64_t ofd_token, int exclude_fd) {
    if (ofd_token == 0) return -1;
    int saved_errno = errno;
    for (int fd = 0; fd < SIMPLEOS_EPOLL_FD_SCAN_LIMIT; fd++) {
        if (fd == exclude_fd) continue;
        if (simpleos_fd_ofd_token(fd) == ofd_token) {
            errno = saved_errno;
            return fd;
        }
    }
    errno = saved_errno;
    return -1;
}

int epoll_create1(int flags) {
    if (flags != 0 && flags != EPOLL_CLOEXEC) {
        errno = EINVAL;
        return -1;
    }
    for (int i = 0; i < SIMPLEOS_EPOLL_MAX_INSTANCES; i++) {
        if (!g_epoll[i].used) {
            memset(&g_epoll[i], 0, sizeof(g_epoll[i]));
            g_epoll[i].used = 1;
            return SIMPLEOS_EPOLL_BASE + i;
        }
    }
    errno = EMFILE;
    return -1;
}

int epoll_create(int size) {
    if (size <= 0) {
        errno = EINVAL;
        return -1;
    }
    return epoll_create1(0);
}

int epoll_ctl(int epfd, int op, int fd, struct epoll_event *event) {
    int idx = epoll_index(epfd);
    if (idx < 0) return -1;
    if (fd == epfd) {
        errno = EINVAL;
        return -1;
    }

    struct simpleos_epoll_instance *inst = &g_epoll[idx];
    int found = -1;
    int free_slot = -1;
    for (int i = 0; i < SIMPLEOS_EPOLL_MAX_WATCHES; i++) {
        if (inst->watches[i].used && inst->watches[i].fd == fd) found = i;
        if (!inst->watches[i].used && free_slot < 0) free_slot = i;
    }

    if (op == EPOLL_CTL_DEL) {
        if (found < 0) {
            errno = ENOENT;
            return -1;
        }
        memset(&inst->watches[found], 0, sizeof(inst->watches[found]));
        return 0;
    }

    if (!event) {
        errno = EFAULT;
        return -1;
    }
    uint64_t ofd_token = simpleos_fd_ofd_token(fd);
    if (ofd_token == 0) {
        errno = EBADF;
        return -1;
    }

    if (op == EPOLL_CTL_ADD) {
        if (found >= 0) {
            errno = EEXIST;
            return -1;
        }
        if (free_slot < 0) {
            errno = ENOMEM;
            return -1;
        }
        inst->watches[free_slot].used = 1;
        inst->watches[free_slot].fd = fd;
        inst->watches[free_slot].ofd_token = ofd_token;
        inst->watches[free_slot].last_revents = 0;
        inst->watches[free_slot].event = *event;
        return 0;
    }

    if (op == EPOLL_CTL_MOD) {
        if (found < 0) {
            errno = ENOENT;
            return -1;
        }
        inst->watches[found].fd = fd;
        inst->watches[found].ofd_token = ofd_token;
        inst->watches[found].last_revents = 0;
        inst->watches[found].event = *event;
        return 0;
    }

    errno = EINVAL;
    return -1;
}

int epoll_wait(int epfd, struct epoll_event *events, int maxevents, int timeout) {
    int idx = epoll_index(epfd);
    if (idx < 0) return -1;
    if (!events || maxevents <= 0) {
        errno = EINVAL;
        return -1;
    }

    struct pollfd pfds[SIMPLEOS_EPOLL_MAX_WATCHES];
    int watch_slots[SIMPLEOS_EPOLL_MAX_WATCHES];
    int nfds = 0;
    struct simpleos_epoll_instance *inst = &g_epoll[idx];

    for (int i = 0; i < SIMPLEOS_EPOLL_MAX_WATCHES; i++) {
        if (inst->watches[i].used && inst->watches[i].event.events != 0) {
            pfds[nfds].fd = inst->watches[i].fd;
            pfds[nfds].events = epoll_to_poll(inst->watches[i].event.events);
            pfds[nfds].revents = 0;
            watch_slots[nfds] = i;
            nfds++;
        }
    }

    if (nfds == 0) return 0;
    int ready = poll(pfds, (nfds_t)nfds, timeout);
    if (ready <= 0) return ready;

    int out = 0;
    for (int i = 0; i < nfds && out < maxevents; i++) {
        int slot = watch_slots[i];
        short revents = pfds[i].revents;
        if (revents != 0) {
            if ((inst->watches[slot].event.events & EPOLLET) &&
                (short)(revents & ~inst->watches[slot].last_revents) == 0) {
                inst->watches[slot].last_revents = revents;
                continue;
            }
            events[out] = inst->watches[slot].event;
            events[out].events = poll_to_epoll(revents);
            inst->watches[slot].last_revents = revents;
            if (inst->watches[slot].event.events & EPOLLONESHOT) {
                inst->watches[slot].event.events = 0;
                inst->watches[slot].last_revents = 0;
            }
            out++;
        } else {
            inst->watches[slot].last_revents = 0;
        }
    }
    return out;
}

int epoll_pwait(int epfd, struct epoll_event *events, int maxevents, int timeout, const void *sigmask) {
    (void)sigmask;
    return epoll_wait(epfd, events, maxevents, timeout);
}

int simpleos_epoll_close_if_epoll(int fd) {
    int idx = epoll_index_noerrno(fd);
    if (idx < 0) return -1;
    memset(&g_epoll[idx], 0, sizeof(g_epoll[idx]));
    return 0;
}

void simpleos_epoll_on_fd_close(int fd) {
    for (int i = 0; i < SIMPLEOS_EPOLL_MAX_INSTANCES; i++) {
        if (!g_epoll[i].used) continue;
        for (int j = 0; j < SIMPLEOS_EPOLL_MAX_WATCHES; j++) {
            if (g_epoll[i].watches[j].used && g_epoll[i].watches[j].fd == fd) {
                memset(&g_epoll[i].watches[j], 0, sizeof(g_epoll[i].watches[j]));
            }
        }
    }
}

void simpleos_epoll_on_fd_close_token(int fd, uint64_t ofd_token) {
    if (ofd_token == 0) {
        simpleos_epoll_on_fd_close(fd);
        return;
    }
    for (int i = 0; i < SIMPLEOS_EPOLL_MAX_INSTANCES; i++) {
        if (!g_epoll[i].used) continue;
        for (int j = 0; j < SIMPLEOS_EPOLL_MAX_WATCHES; j++) {
            struct simpleos_epoll_watch *watch = &g_epoll[i].watches[j];
            if (!watch->used || watch->ofd_token != ofd_token || watch->fd != fd) {
                continue;
            }
            int replacement = simpleos_find_fd_for_ofd(ofd_token, fd);
            if (replacement >= 0) {
                watch->fd = replacement;
            } else {
                memset(watch, 0, sizeof(*watch));
            }
        }
    }
}
