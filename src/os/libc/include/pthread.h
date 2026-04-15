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
