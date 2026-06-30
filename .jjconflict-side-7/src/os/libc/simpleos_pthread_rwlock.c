/*
 * SimpleOS pthread_rwlock_* stubs — noop rwlocks for the single-threaded
 * exokernel. All operations return 0 (success); there is nothing to lock.
 */

typedef struct { int _opaque; } pthread_rwlock_t;
typedef int pthread_rwlockattr_t;

int pthread_rwlock_init(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr) {
    (void)rwlock; (void)attr;
    return 0;
}

int pthread_rwlock_destroy(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlock_unlock(pthread_rwlock_t *rwlock) {
    (void)rwlock;
    return 0;
}

int pthread_rwlockattr_init(pthread_rwlockattr_t *attr) {
    (void)attr;
    return 0;
}

int pthread_rwlockattr_destroy(pthread_rwlockattr_t *attr) {
    (void)attr;
    return 0;
}
