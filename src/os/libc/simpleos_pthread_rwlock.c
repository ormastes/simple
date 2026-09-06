/*
 * SimpleOS pthread_rwlock_* stubs. Report unsupported until a kernel-owned
 * atomic rwlock/futex handoff exists; success without serialization is unsafe.
 *
 * This file had NO includes at all while using ENOSYS and EINVAL in every
 * function body, so clang rejected it outright ("use of undeclared identifier
 * 'ENOSYS'" x9, "'EINVAL'" x9) and it HAS NEVER COMPILED — the same defect
 * class as the sibling never-compiled libc files fixed alongside it
 * (simpleos_process.c's duplicate getgid/geteuid/getegid, simpleos_dlmalloc.c's
 * undefined _checked_add/_checked_round_up). errno.h is present in this libc's
 * own include/ directory and defines both macros; nothing else was missing.
 */

#include "include/errno.h"
/* The typedefs that used to sit here now live in pthread.h, so there is exactly
 * one definition and this file's implementations are checked against the
 * declarations every caller sees. */
#include "include/pthread.h"

int pthread_rwlock_init(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr) {
    (void)attr;
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_destroy(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlock_unlock(pthread_rwlock_t *rwlock) {
    return rwlock ? ENOSYS : EINVAL;
}

int pthread_rwlockattr_init(pthread_rwlockattr_t *attr) {
    return attr ? ENOSYS : EINVAL;
}

int pthread_rwlockattr_destroy(pthread_rwlockattr_t *attr) {
    return attr ? ENOSYS : EINVAL;
}
