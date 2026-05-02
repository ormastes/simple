/*
 * SimpleOS Libc Shim — POSIX threads (single-threaded stubs)
 *
 * LLVM links against pthread symbols even when built with
 * LLVM_ENABLE_THREADS=OFF.  In single-threaded mode all mutex and
 * condition-variable operations are harmless no-ops.  Thread creation
 * returns ENOSYS (no kernel thread support yet).
 *
 * Thread-local storage uses a simple static array — sufficient for a
 * single-threaded environment where only one "thread" exists.
 */

#include "include/pthread.h"
#include "include/errno.h"
#include "include/stdlib.h"
#include "include/string.h"

extern int64_t simpleos_syscall(int64_t, int64_t, int64_t, int64_t,
                                 int64_t, int64_t);

/* ====================================================================
 * 1. Thread creation — not supported yet
 * ==================================================================== */

int pthread_create(pthread_t *thread, const pthread_attr_t *attr,
                   void *(*start_routine)(void *), void *arg) {
    (void)thread; (void)attr; (void)start_routine; (void)arg;
    return ENOSYS;
}

int pthread_join(pthread_t thread, void **retval) {
    (void)thread; (void)retval;
    return ENOSYS;
}

int pthread_detach(pthread_t thread) {
    (void)thread;
    return ENOSYS;
}

pthread_t pthread_self(void) { return 1; }

int pthread_equal(pthread_t t1, pthread_t t2) { return t1 == t2; }

/* ====================================================================
 * 2. Mutexes — no-ops in single-threaded mode
 * ==================================================================== */

int pthread_mutex_init(pthread_mutex_t *mutex,
                       const pthread_mutexattr_t *attr) {
    (void)attr;
    if (mutex) memset(mutex, 0, sizeof(*mutex));
    return 0;
}

int pthread_mutex_lock(pthread_mutex_t *mutex)    { (void)mutex; return 0; }
int pthread_mutex_trylock(pthread_mutex_t *mutex)  { (void)mutex; return 0; }
int pthread_mutex_unlock(pthread_mutex_t *mutex)   { (void)mutex; return 0; }
int pthread_mutex_destroy(pthread_mutex_t *mutex)  { (void)mutex; return 0; }

/* ====================================================================
 * 3. Condition variables — no-ops
 * ==================================================================== */

int pthread_cond_init(pthread_cond_t *cond,
                      const pthread_condattr_t *attr) {
    (void)attr;
    if (cond) memset(cond, 0, sizeof(*cond));
    return 0;
}

int pthread_cond_wait(pthread_cond_t *cond, pthread_mutex_t *mutex) {
    (void)cond; (void)mutex;
    return 0;
}

int pthread_cond_signal(pthread_cond_t *cond)    { (void)cond; return 0; }
int pthread_cond_broadcast(pthread_cond_t *cond) { (void)cond; return 0; }
int pthread_cond_destroy(pthread_cond_t *cond)   { (void)cond; return 0; }

/* ====================================================================
 * 4. Mutex and condition attributes — stubs
 * ==================================================================== */

int pthread_mutexattr_init(pthread_mutexattr_t *attr)    { (void)attr; return 0; }
int pthread_mutexattr_destroy(pthread_mutexattr_t *attr) { (void)attr; return 0; }

int pthread_condattr_init(pthread_condattr_t *attr)    { (void)attr; return 0; }
int pthread_condattr_destroy(pthread_condattr_t *attr) { (void)attr; return 0; }

/* ====================================================================
 * 5. Once — simple flag-based implementation
 * ==================================================================== */

int pthread_once(pthread_once_t *once_control, void (*init_routine)(void)) {
    if (once_control && *once_control == 0) {
        *once_control = 1;
        init_routine();
    }
    return 0;
}

/* ====================================================================
 * 6. Thread-local storage — static array (single-threaded)
 * ==================================================================== */

#define MAX_KEYS 64

static void *_tls_values[MAX_KEYS];
static void (*_tls_destructors[MAX_KEYS])(void *);
static int _tls_next_key = 0;

int pthread_key_create(pthread_key_t *key, void (*destructor)(void *)) {
    if (_tls_next_key >= MAX_KEYS) return EAGAIN;
    *key = _tls_next_key;
    _tls_destructors[_tls_next_key] = destructor;
    _tls_values[_tls_next_key] = NULL;
    _tls_next_key++;
    return 0;
}

int pthread_key_delete(pthread_key_t key) {
    if (key >= MAX_KEYS) return EINVAL;
    _tls_values[key] = NULL;
    _tls_destructors[key] = NULL;
    return 0;
}

void *pthread_getspecific(pthread_key_t key) {
    if (key >= MAX_KEYS) return NULL;
    return _tls_values[key];
}

int pthread_setspecific(pthread_key_t key, const void *value) {
    if (key >= MAX_KEYS) return EINVAL;
    _tls_values[key] = (void *)value;
    return 0;
}

/* ====================================================================
 * 7. Thread attributes — stubs
 * ==================================================================== */

int pthread_attr_init(pthread_attr_t *attr)    { (void)attr; return 0; }
int pthread_attr_destroy(pthread_attr_t *attr) { (void)attr; return 0; }

int pthread_attr_setdetachstate(pthread_attr_t *attr, int state) {
    (void)attr; (void)state;
    return 0;
}

int pthread_attr_setstacksize(pthread_attr_t *attr, size_t size) {
    (void)attr; (void)size;
    return 0;
}
