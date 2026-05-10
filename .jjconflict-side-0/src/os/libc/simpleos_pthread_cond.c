/*
 * SimpleOS pthread_cond_* stubs — single-threaded exokernel.
 *
 * pthread_cond_timedwait returns ETIMEDOUT immediately so callers drop
 * through their wait loop rather than deadlocking. pthread_cond_wait
 * returns 0 (the non-timed variant); callers that use it as a loop guard
 * will spin — intentional tradeoff: CPU burn over deadlock, detectable
 * in profiling.
 */

#ifndef ETIMEDOUT
#define ETIMEDOUT 110
#endif

typedef struct { int _opaque; } pthread_cond_t;
typedef struct { int _opaque; } pthread_mutex_t;
typedef int pthread_condattr_t;
struct timespec;

int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t *attr) {
    (void)cond; (void)attr;
    return 0;
}

int pthread_cond_destroy(pthread_cond_t *cond) {
    (void)cond;
    return 0;
}

int pthread_cond_signal(pthread_cond_t *cond) {
    (void)cond;
    return 0;
}

int pthread_cond_broadcast(pthread_cond_t *cond) {
    (void)cond;
    return 0;
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex) {
    (void)cond; (void)mutex;
    return 0;
}

int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex,
                           const struct timespec *abstime) {
    (void)cond; (void)mutex; (void)abstime;
    return ETIMEDOUT;
}

int pthread_condattr_init(pthread_condattr_t *attr) {
    (void)attr;
    return 0;
}

int pthread_condattr_destroy(pthread_condattr_t *attr) {
    (void)attr;
    return 0;
}
