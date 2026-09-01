#define _XOPEN_SOURCE 700

#include <pthread.h>
#include <errno.h>
#include <stdio.h>
#include <stdint.h>

/* ---------------------------------------------------------------------------
 * POSIX barriers on Darwin.
 *
 * pthread_barrier_* is an OPTIONAL part of POSIX (_POSIX_BARRIERS) and Apple
 * does not implement it, so this translation unit did not compile on macOS at
 * all -- the guard's "117 compiled" green was only ever measured on Linux.
 *
 * The two-phase rendezvous below IS the property under test: a second thread
 * must observe the receiver as valid strictly BEFORE the owner frees it, and
 * must observe it as invalid strictly AFTER the owner has freed it. Removing
 * or loosening the rendezvous would change the interleaving and stop testing
 * the concurrent unregister window, so the barriers are not removed here --
 * they are PROVIDED, with identical semantics for this use:
 *   - no waiter returns until `count` waiters have arrived (generation guard,
 *     so a fast thread cannot fall through into the next generation),
 *   - exactly one waiter per generation receives PTHREAD_BARRIER_SERIAL_THREAD
 *     and the rest receive 0 (barrier_wait_ok() below accepts both).
 * Every assertion in this file is unchanged.
 * ------------------------------------------------------------------------ */
#if defined(__APPLE__) && !defined(PTHREAD_BARRIER_SERIAL_THREAD)
#define PTHREAD_BARRIER_SERIAL_THREAD (-1)

typedef struct { int spl_unused; } pthread_barrierattr_t;

typedef struct {
    pthread_mutex_t mutex;
    pthread_cond_t  cond;
    unsigned        count;
    unsigned        waiting;
    unsigned        generation;
} pthread_barrier_t;

static int pthread_barrier_init(pthread_barrier_t* barrier,
                                const pthread_barrierattr_t* attr,
                                unsigned count) {
    (void)attr;
    if (count == 0) return EINVAL;
    if (pthread_mutex_init(&barrier->mutex, NULL) != 0) return EAGAIN;
    if (pthread_cond_init(&barrier->cond, NULL) != 0) {
        pthread_mutex_destroy(&barrier->mutex);
        return EAGAIN;
    }
    barrier->count = count;
    barrier->waiting = 0;
    barrier->generation = 0;
    return 0;
}

static int pthread_barrier_destroy(pthread_barrier_t* barrier) {
    int rc = pthread_cond_destroy(&barrier->cond);
    int rc2 = pthread_mutex_destroy(&barrier->mutex);
    return rc != 0 ? rc : rc2;
}

static int pthread_barrier_wait(pthread_barrier_t* barrier) {
    int serial = 0;
    unsigned generation;
    if (pthread_mutex_lock(&barrier->mutex) != 0) return EINVAL;
    generation = barrier->generation;
    if (++barrier->waiting == barrier->count) {
        barrier->waiting = 0;
        barrier->generation++;
        serial = 1;
        pthread_cond_broadcast(&barrier->cond);
    } else {
        while (generation == barrier->generation) {
            pthread_cond_wait(&barrier->cond, &barrier->mutex);
        }
    }
    pthread_mutex_unlock(&barrier->mutex);
    return serial ? PTHREAD_BARRIER_SERIAL_THREAD : 0;
}
#endif /* __APPLE__ && !PTHREAD_BARRIER_SERIAL_THREAD */

extern uint8_t* rt_alloc(int64_t size);
extern uint8_t* rt_struct_alloc(int64_t size);
extern int8_t rt_struct_receiver_valid(
    int64_t receiver, int64_t byte_offset, int64_t access_width);
extern void rt_free(uint8_t* ptr);

enum { POST_FREE_VALIDATIONS = 1024 };

typedef struct ConcurrentGuardCheck {
    pthread_barrier_t validated_before_free;
    pthread_barrier_t unregistered;
    uintptr_t receiver;
    int assertions;
    int failure;
} ConcurrentGuardCheck;

static int barrier_wait_ok(pthread_barrier_t* barrier) {
    int result = pthread_barrier_wait(barrier);
    return result == 0 || result == PTHREAD_BARRIER_SERIAL_THREAD;
}

static void* validate_around_unregister(void* opaque) {
    ConcurrentGuardCheck* check = (ConcurrentGuardCheck*)opaque;
    if (!rt_struct_receiver_valid((int64_t)check->receiver, 0, 8)) {
        check->failure = 1;
    } else {
        check->assertions++;
    }
    if (!barrier_wait_ok(&check->validated_before_free)) {
        check->failure = 2;
        return NULL;
    }
    if (!barrier_wait_ok(&check->unregistered)) {
        check->failure = 3;
        return NULL;
    }
    for (int i = 0; i < POST_FREE_VALIDATIONS; i++) {
        if (rt_struct_receiver_valid((int64_t)check->receiver, 0, 8)) {
            check->failure = 4;
            return NULL;
        }
        check->assertions++;
    }
    return NULL;
}

int main(void) {
    int assertions = 0;
    uint8_t* raw = rt_alloc(16);
    uint8_t* structure = rt_struct_alloc(16);
    if (!raw || !structure) return 1;
    assertions++;

    /* Only the dedicated struct allocator establishes field ownership. */
    if (rt_struct_receiver_valid((int64_t)(uintptr_t)raw, 0, 8)) return 2;
    if (!rt_struct_receiver_valid((int64_t)(uintptr_t)structure, 0, 8)) return 3;
    if (!rt_struct_receiver_valid((int64_t)(uintptr_t)structure, 8, 8)) return 4;
    if (rt_struct_receiver_valid((int64_t)(uintptr_t)structure, 9, 8)) return 5;
    if (rt_struct_receiver_valid((int64_t)(uintptr_t)structure, -1, 1)) return 6;
    assertions += 5;

    rt_free(structure);
    if (rt_struct_receiver_valid((int64_t)(uintptr_t)structure, 0, 1)) return 7;
    assertions++;
    rt_free(raw);

    uint8_t* concurrent = rt_struct_alloc(16);
    if (!concurrent) return 8;
    assertions++;
    ConcurrentGuardCheck check = {
        .receiver = (uintptr_t)concurrent,
        .assertions = 0,
        .failure = 0,
    };
    if (pthread_barrier_init(&check.validated_before_free, NULL, 2) != 0) return 9;
    if (pthread_barrier_init(&check.unregistered, NULL, 2) != 0) return 10;
    pthread_t validator;
    if (pthread_create(&validator, NULL, validate_around_unregister, &check) != 0) return 11;
    if (!barrier_wait_ok(&check.validated_before_free)) return 12;
    rt_free(concurrent);
    if (!barrier_wait_ok(&check.unregistered)) return 13;
    if (pthread_join(validator, NULL) != 0) return 14;
    if (check.failure != 0) return 20 + check.failure;
    if (pthread_barrier_destroy(&check.unregistered) != 0) return 15;
    if (pthread_barrier_destroy(&check.validated_before_free) != 0) return 16;
    assertions += check.assertions;

    printf("PASS assertions=%d concurrent_post_free_rejections=%d\n",
        assertions, POST_FREE_VALIDATIONS);
    return 0;
}
