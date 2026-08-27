/*
 * SimpleOS pthread_rwlock_* stubs. Report unsupported until a kernel-owned
 * atomic rwlock/futex handoff exists; success without serialization is unsafe.
 */

typedef struct { int _opaque; } pthread_rwlock_t;
typedef int pthread_rwlockattr_t;

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
