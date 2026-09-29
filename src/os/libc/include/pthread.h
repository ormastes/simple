/*
 * SimpleOS <pthread.h> — POSIX threads
 */

#ifndef _SIMPLEOS_PTHREAD_H
#define _SIMPLEOS_PTHREAD_H

#ifdef __cplusplus
extern "C" {
#endif

#include <sys/types.h>

#ifndef NULL
#define NULL ((void *)0)
#endif

#define PTHREAD_MUTEX_INITIALIZER { { 0 } }
#define PTHREAD_COND_INITIALIZER  { { 0 } }
#define PTHREAD_ONCE_INIT         0

/* pthread_rwlock_* was implemented in src/os/libc/simpleos_pthread_rwlock.c but
 * NEVER DECLARED here, while src/runtime/runtime_native.c:5611+ uses
 * pthread_rwlock_t, PTHREAD_RWLOCK_INITIALIZER and the rd/wr/unlock calls —
 * "unknown type name 'pthread_rwlock_t'" plus implicit-declaration errors, which
 * blocked the SimpleOS runtime cross-compile.
 *
 * The type is declared HERE and the .c file includes this header, so there is
 * exactly one definition; it previously carried a private copy of the typedef,
 * which would have become a conflicting redefinition the moment anything
 * included both. The layout is the same opaque single-int placeholder that file
 * already used, so the ABI is unchanged.
 *
 * Note the implementation returns ENOSYS by design: SimpleOS has no kernel-owned
 * atomic rwlock/futex handoff yet, and that file's header states that reporting
 * unsupported is deliberate because "success without serialization is unsafe".
 * Declaring these does not claim they work — it only makes the tree compile and
 * lets callers see the honest ENOSYS instead of an implicit-declaration guess. */
#define PTHREAD_RWLOCK_INITIALIZER { 0 }

typedef struct { int _opaque; } pthread_rwlock_t;
typedef int pthread_rwlockattr_t;

int pthread_rwlock_init(pthread_rwlock_t *rwlock, const pthread_rwlockattr_t *attr);
int pthread_rwlock_destroy(pthread_rwlock_t *rwlock);
int pthread_rwlock_rdlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_tryrdlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_wrlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_trywrlock(pthread_rwlock_t *rwlock);
int pthread_rwlock_unlock(pthread_rwlock_t *rwlock);

/* Thread management */
int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg);
int pthread_join(pthread_t thread, void **retval);
int pthread_detach(pthread_t thread);
pthread_t pthread_self(void);
int pthread_equal(pthread_t t1, pthread_t t2);

/* Thread attributes */
int pthread_attr_init(pthread_attr_t *attr);
int pthread_attr_destroy(pthread_attr_t *attr);

#define PTHREAD_CREATE_JOINABLE 0
#define PTHREAD_CREATE_DETACHED 1
int pthread_attr_setdetachstate(pthread_attr_t *attr, int detachstate);
int pthread_attr_getdetachstate(const pthread_attr_t *attr, int *detachstate);

/* Mutex */
int pthread_mutex_init(pthread_mutex_t *mutex,
                       const pthread_mutexattr_t *attr);
int pthread_mutex_destroy(pthread_mutex_t *mutex);
int pthread_mutex_lock(pthread_mutex_t *mutex);
int pthread_mutex_trylock(pthread_mutex_t *mutex);
int pthread_mutex_unlock(pthread_mutex_t *mutex);

/* Mutex attributes */
int pthread_mutexattr_init(pthread_mutexattr_t *attr);
int pthread_mutexattr_destroy(pthread_mutexattr_t *attr);

/* Condition variables */
int pthread_cond_init(pthread_cond_t *cond,
                      const pthread_condattr_t *attr);
int pthread_cond_destroy(pthread_cond_t *cond);
int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex);
int pthread_cond_signal(pthread_cond_t *cond);
int pthread_cond_broadcast(pthread_cond_t *cond);

/* Condition attributes */
int pthread_condattr_init(pthread_condattr_t *attr);
int pthread_condattr_destroy(pthread_condattr_t *attr);

/* Once */
int pthread_once(pthread_once_t *once_control,
                 void (*init_routine)(void));

/* Thread-specific data */
int   pthread_key_create(pthread_key_t *key, void (*destructor)(void *));
int   pthread_key_delete(pthread_key_t key);
void *pthread_getspecific(pthread_key_t key);
int   pthread_setspecific(pthread_key_t key, const void *value);

#ifdef __cplusplus
}
#endif

#endif /* _SIMPLEOS_PTHREAD_H */
