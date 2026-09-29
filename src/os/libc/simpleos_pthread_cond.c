/*
 * SimpleOS pthread_cond_* stubs — single-threaded exokernel.
 *
 * SimpleOS has no atomic mutex-release-and-park primitive yet. A successful
 * condition-variable wait would therefore be a lie: predicate loops spin at
 * full CPU while believing they waited. All wait/wake operations fail closed
 * until the kernel owns that transition.
 */

#include "include/errno.h"   /* ENOSYS/EINVAL/... were used undeclared: this file never compiled */

#ifndef ETIMEDOUT
#define ETIMEDOUT 110
#endif

typedef struct { int _opaque; } pthread_cond_t;
typedef struct { int _opaque; } pthread_mutex_t;
typedef int pthread_condattr_t;
struct timespec;

int pthread_cond_init(pthread_cond_t *cond, const pthread_condattr_t *attr) {
    (void)attr;
    return cond ? ENOSYS : EINVAL;
}

int pthread_cond_destroy(pthread_cond_t *cond) {
    return cond ? ENOSYS : EINVAL;
}

int pthread_cond_signal(pthread_cond_t *cond) {
    return cond ? ENOSYS : EINVAL;
}

int pthread_cond_broadcast(pthread_cond_t *cond) {
    return cond ? ENOSYS : EINVAL;
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex) {
    return (cond && mutex) ? ENOSYS : EINVAL;
}

int pthread_cond_timedwait(pthread_cond_t *cond, pthread_mutex_t *mutex,
                           const struct timespec *abstime) {
    return (cond && mutex && abstime) ? ENOSYS : EINVAL;
}

int pthread_condattr_init(pthread_condattr_t *attr) {
    return attr ? ENOSYS : EINVAL;
}

int pthread_condattr_destroy(pthread_condattr_t *attr) {
    return attr ? ENOSYS : EINVAL;
}
