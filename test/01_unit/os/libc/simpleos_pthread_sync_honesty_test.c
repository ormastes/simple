#include "src/os/libc/include/pthread.h"
#include "src/os/libc/include/errno.h"

#include "src/os/libc/simpleos_pthread.c"
#include "src/os/libc/simpleos_pthread_rwlock.c"
#include "src/os/libc/simpleos_pthread_cond.c"

int main(void) {
    pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
    pthread_rwlock_t rwlock = PTHREAD_RWLOCK_INITIALIZER;
    pthread_mutex_t saved_mutex = mutex;
    pthread_rwlock_t saved_rwlock = rwlock;

    if (pthread_mutex_init(NULL, NULL) != EINVAL) return 1;
    if (pthread_mutex_init(&mutex, NULL) != ENOSYS) return 2;
    if (memcmp(&mutex, &saved_mutex, sizeof(mutex)) != 0) return 3;
    if (pthread_mutex_lock(&mutex) != ENOSYS || pthread_mutex_trylock(&mutex) != ENOSYS ||
        pthread_mutex_unlock(&mutex) != ENOSYS || pthread_mutex_destroy(&mutex) != ENOSYS) return 4;
    if (pthread_mutex_lock(NULL) != EINVAL) return 5;

    if (pthread_rwlock_init(NULL, NULL) != EINVAL) return 6;
    if (pthread_rwlock_init(&rwlock, NULL) != ENOSYS) return 7;
    if (memcmp(&rwlock, &saved_rwlock, sizeof(rwlock)) != 0) return 8;
    if (pthread_rwlock_rdlock(&rwlock) != ENOSYS || pthread_rwlock_wrlock(&rwlock) != ENOSYS ||
        pthread_rwlock_tryrdlock(&rwlock) != ENOSYS || pthread_rwlock_trywrlock(&rwlock) != ENOSYS ||
        pthread_rwlock_unlock(&rwlock) != ENOSYS || pthread_rwlock_destroy(&rwlock) != ENOSYS) return 9;
    if (pthread_rwlock_rdlock(NULL) != EINVAL) return 10;

    pthread_attr_t attr;
    int detach_state = -1;
    if (pthread_attr_init(NULL) != EINVAL || pthread_attr_init(&attr) != ENOSYS) return 11;
    if (pthread_attr_destroy(NULL) != EINVAL || pthread_attr_destroy(&attr) != ENOSYS) return 12;
    if (pthread_attr_setdetachstate(NULL, PTHREAD_CREATE_JOINABLE) != EINVAL ||
        pthread_attr_setdetachstate(&attr, PTHREAD_CREATE_DETACHED) != ENOSYS) return 13;
    if (pthread_attr_getdetachstate(NULL, &detach_state) != EINVAL ||
        pthread_attr_getdetachstate(&attr, NULL) != EINVAL ||
        pthread_attr_getdetachstate(&attr, &detach_state) != ENOSYS || detach_state != -1) return 14;
    if (pthread_attr_setstacksize(NULL, 4096U) != EINVAL ||
        pthread_attr_setstacksize(&attr, 4096U) != ENOSYS) return 15;

    pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
    pthread_cond_t saved_cond = cond;
    pthread_condattr_t cond_attr;
    if (pthread_cond_init(NULL, NULL) != EINVAL || pthread_cond_init(&cond, NULL) != ENOSYS) return 16;
    if (memcmp(&cond, &saved_cond, sizeof(cond)) != 0) return 17;
    if (pthread_cond_destroy(NULL) != EINVAL || pthread_cond_destroy(&cond) != ENOSYS) return 18;
    if (pthread_cond_signal(NULL) != EINVAL || pthread_cond_broadcast(NULL) != EINVAL ||
        pthread_cond_wait(NULL, NULL) != EINVAL || pthread_cond_timedwait(NULL, NULL, NULL) != EINVAL) return 19;
    if (pthread_condattr_init(NULL) != EINVAL || pthread_condattr_init(&cond_attr) != ENOSYS ||
        pthread_condattr_destroy(NULL) != EINVAL || pthread_condattr_destroy(&cond_attr) != ENOSYS) return 20;
    return 0;
}
