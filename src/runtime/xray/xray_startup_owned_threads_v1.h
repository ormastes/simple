#ifndef SIMPLE_XRAY_STARTUP_OWNED_THREADS_V1_H
#define SIMPLE_XRAY_STARTUP_OWNED_THREADS_V1_H
/* Private core-C spawn boundary. This records owned attempts, not arbitrary
 * foreign/constructor threads, and never grants observer/profile authority. */
#if defined(SIMPLE_XRAY_CONTEXT_HOOKS_V1)
#if !defined(__linux__)
#error "XRay startup owned-thread ledger requires the admitted Linux source runtime"
#endif
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
extern int64_t simple_xray_startup_owned_spawn_admit_v1(void);
extern int64_t simple_xray_startup_no_owned_threads_begin_v1(void);
extern int64_t simple_xray_startup_no_owned_threads_end_v1(void);
extern void simple_xray_startup_window_seal_v1(void);
static inline int simple_xray_startup_pthread_create_v1(pthread_t *thread,
        const pthread_attr_t *attributes, void *(*entry)(void *), void *argument) {
    if (simple_xray_startup_owned_spawn_admit_v1() != 1) return EAGAIN;
    return pthread_create(thread, attributes, entry, argument);
}
#define SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1 simple_xray_startup_pthread_create_v1
#else
/* Off preprocessing preserves the original pthread call and dependencies. */
#define SIMPLE_XRAY_STARTUP_PTHREAD_CREATE_V1 pthread_create
#endif
#endif
