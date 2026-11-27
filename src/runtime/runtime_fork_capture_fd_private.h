/* Private synchronous descriptor boundary. Only writer setup/fork/parent-close
 * is coordinated; no mutex spans child exec, capture or wait. */
#ifndef SIMPLE_FORK_CAPTURE_FD_PRIVATE_H
#define SIMPLE_FORK_CAPTURE_FD_PRIVATE_H
#include <pthread.h>
#if defined(__linux__)
#include <sys/syscall.h>
static pthread_mutex_t capture_setup_mutex_v1 = PTHREAD_MUTEX_INITIALIZER;
#endif

/* Short writer-inheritance transaction only. Never hold this during capture
 * or wait. Acquisition is capped at250ms; OS fork/user atfork callbacks retain
 * their own scheduling limits. Capture is not async-signal/atfork reentrant.
 * Cancellation is disabled only AFTER acquisition, restored before return. */
static int capture_setup_acquire_v1(int* cancellation_state) {
    *cancellation_state = -1;
#if defined(__linux__)
    struct timespec started;
    if (clock_gettime(CLOCK_MONOTONIC, &started) != 0) return -1;
    for (;;) {
        int result = pthread_mutex_trylock(&capture_setup_mutex_v1);
        if (result == 0) {
            if (pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, cancellation_state) != 0) {
                (void)pthread_mutex_unlock(&capture_setup_mutex_v1); return -1;
            }
            return 0;
        }
        if (result != EBUSY) return -1;
        struct timespec now;
        if (clock_gettime(CLOCK_MONOTONIC, &now) != 0) return -1;
        int64_t elapsed = (int64_t)(now.tv_sec - started.tv_sec) * 1000000000LL + now.tv_nsec - started.tv_nsec;
        if (elapsed < 0 || elapsed >= 250000000LL) return -1;
        const struct timespec pause = {0, 1000000}; (void)nanosleep(&pause, NULL);
    }
#else
    return 0; /* preserve non-Linux raw legacy setup */
#endif
}
static void capture_setup_release_v1(int cancellation_state) {
#if defined(__linux__)
    (void)pthread_mutex_unlock(&capture_setup_mutex_v1);
    if (cancellation_state >= 0) (void)pthread_setcancelstate(cancellation_state, NULL);
#else
    (void)cancellation_state;
#endif
}

/* Atomic CLOEXEC from creation, including duplicates used to keep stdio slots
 * separate. A pipe()+fcntl() sequence leaves a concurrent-fork race. */
int simple_fork_capture_pipe_v1(int fds[2]) {
#if defined(__linux__)
    if (pipe2(fds, O_CLOEXEC) != 0) return -1;
    for (int index = 0; index < 2; index++) {
        if (fds[index] < 3) {
            int moved = fcntl(fds[index], F_DUPFD_CLOEXEC, 3);
            if (moved < 0) {
                close(fds[0]); close(fds[1]); fds[0] = fds[1] = -1; return -1;
            }
            close(fds[index]); fds[index] = moved;
        }
    }
    return 0;
#else
    (void)fds;
    errno = ENOTSUP;
    return -1; /* no non-atomic fallback in captured-process mode */
#endif
}

/* On failure report through the still-owned status channel and exit. Only
 * the parent, after confirmed reap, may turn this into a no-entry receipt. */
static void capture_child_descriptor_reject_v1(int status_fd) {
    const unsigned char rejected = 4;
    ssize_t written;
    do { written = write(status_fd, &rejected, 1); } while (written < 0 && errno == EINTR);
    _exit(126);
}

static void capture_child_descriptors_v1(int status_fd) {
#if defined(__linux__) && defined(SYS_close_range)
    if (status_fd != 3) {
        if (dup3(status_fd, 3, O_CLOEXEC) < 0) capture_child_descriptor_reject_v1(status_fd);
    } else {
        int flags = fcntl(3, F_GETFD);
        if (flags < 0 || (flags & FD_CLOEXEC) == 0) capture_child_descriptor_reject_v1(status_fd);
    }
    /* CLOEXEC alone is insufficient for a child delayed before exec. Close
     * unrelated inherited writers now; retain only stdio and status FD3. */
    if (syscall(SYS_close_range, 4U, ~0U, 0U) != 0) capture_child_descriptor_reject_v1(3);
#else
    capture_child_descriptor_reject_v1(status_fd);
#endif
}
#endif
