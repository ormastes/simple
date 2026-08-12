#define _XOPEN_SOURCE 700

#include <pthread.h>
#include <stdio.h>
#include <stdint.h>

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
