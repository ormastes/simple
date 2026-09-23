#include <assert.h>
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

static int mock_enter(int, unsigned, unsigned, unsigned, sigset_t *);
static int mock_ppoll(struct pollfd *, nfds_t, const struct timespec *, const sigset_t *);

#define __sys_io_uring_enter mock_enter
#define ppoll mock_ppoll
#include "../../../src/runtime/vendor/liburing/src/queue.c"
#undef ppoll
#undef __sys_io_uring_enter

enum mock_mode {
    MOCK_EINTR_THEN_PARTIAL,
    MOCK_PARTIAL_THEN_ERROR,
    MOCK_TIMEOUT,
};

static enum mock_mode mode;
static unsigned *kernel_head;
static unsigned enter_calls;
static unsigned enter_submit[8];
static unsigned poll_calls;

static int mock_enter(int fd, unsigned to_submit, unsigned min_complete,
                      unsigned flags, sigset_t *sig)
{
    (void)fd; (void)min_complete; (void)flags; (void)sig;
    enter_submit[enter_calls++] = to_submit;
    if (mode == MOCK_EINTR_THEN_PARTIAL && enter_calls == 1) {
        errno = EINTR;
        return -1;
    }
    if (mode == MOCK_PARTIAL_THEN_ERROR && enter_calls == 2) {
        errno = EIO;
        return -1;
    }
    assert(to_submit > 0);
    (*kernel_head)++;
    return 1;
}

static int mock_ppoll(struct pollfd *fds, nfds_t count,
                      const struct timespec *timeout, const sigset_t *mask)
{
    (void)mask;
    assert(mode == MOCK_TIMEOUT);
    assert(count == 1);
    assert(fds[0].events == POLLIN);
    assert(timeout != NULL);
    assert(timeout->tv_sec == 0);
    assert(timeout->tv_nsec == 25000000L);
    poll_calls++;
    return 0;
}

static void init_ring(struct io_uring *ring, unsigned *sq_head,
                      unsigned *sq_tail, unsigned *cq_head,
                      unsigned *cq_tail, unsigned *sq_array,
                      struct io_uring_sqe *sqes,
                      struct io_uring_cqe *cqes)
{
    memset(ring, 0, sizeof(*ring));
    *sq_head = 0;
    *sq_tail = 0;
    *cq_head = 0;
    *cq_tail = 0;
    ring->enter_ring_fd = 7;
    ring->sq.khead = sq_head;
    ring->sq.ktail = sq_tail;
    ring->sq.array = sq_array;
    ring->sq.sqes = sqes;
    ring->sq.ring_mask = 7;
    ring->sq.ring_entries = 8;
    ring->cq.khead = cq_head;
    ring->cq.ktail = cq_tail;
    ring->cq.cqes = cqes;
    ring->cq.ring_mask = 7;
    ring->cq.ring_entries = 8;
    kernel_head = sq_head;
    enter_calls = 0;
    poll_calls = 0;
    memset(enter_submit, 0, sizeof(enter_submit));
}

int main(void)
{
    struct io_uring ring;
    unsigned sq_head = 0, sq_tail = 0, cq_head = 0, cq_tail = 0;
    unsigned sq_array[8] = {0};
    struct io_uring_sqe sqes[8] = {{0}};
    struct io_uring_cqe cqes[8] = {{0}};

    init_ring(&ring, &sq_head, &sq_tail, &cq_head, &cq_tail,
              sq_array, sqes, cqes);
    assert(io_uring_get_sqe(&ring) != NULL);
    assert(io_uring_get_sqe(&ring) != NULL);
    mode = MOCK_EINTR_THEN_PARTIAL;
    assert(io_uring_submit(&ring) == 2);
    assert(enter_calls == 3);
    assert(enter_submit[0] == 2 && enter_submit[1] == 2 && enter_submit[2] == 1);
    assert(sq_head == 2 && sq_tail == 2);

    init_ring(&ring, &sq_head, &sq_tail, &cq_head, &cq_tail,
              sq_array, sqes, cqes);
    assert(io_uring_get_sqe(&ring) != NULL);
    assert(io_uring_get_sqe(&ring) != NULL);
    mode = MOCK_PARTIAL_THEN_ERROR;
    assert(io_uring_submit(&ring) == 1);
    assert(sq_head == 1 && sq_tail == 2);
    assert(io_uring_submit(&ring) == 1);
    assert(sq_head == 2 && sq_tail == 2);

    init_ring(&ring, &sq_head, &sq_tail, &cq_head, &cq_tail,
              sq_array, sqes, cqes);
    mode = MOCK_TIMEOUT;
    struct __kernel_timespec timeout = { .tv_sec = 0, .tv_nsec = 25000000L };
    struct io_uring_cqe *cqe = NULL;
    assert(io_uring_wait_cqe_timeout(&ring, &cqe, &timeout) == -ETIME);
    assert(poll_calls == 1);
    assert(enter_calls == 0);

    puts("io_uring queue contract: PASS");
    return 0;
}
