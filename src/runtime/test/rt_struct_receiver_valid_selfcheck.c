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
    pthread_mutex_t rendezvous_mutex;
    pthread_cond_t rendezvous_cond;
    int rendezvous_count;
    int rendezvous_generation;
    uintptr_t receiver;
    int assertions;
    int failure;
} ConcurrentGuardCheck;

/* pthread_barrier_t is optional POSIX and is absent on macOS.  This two-party
 * reusable rendezvous has the same ordering needed by the selfcheck. */
static int rendezvous_wait(ConcurrentGuardCheck* check) {
    if (pthread_mutex_lock(&check->rendezvous_mutex) != 0) return 0;
    int generation = check->rendezvous_generation;
    check->rendezvous_count++;
    if (check->rendezvous_count == 2) {
        check->rendezvous_count = 0;
        check->rendezvous_generation++;
        pthread_cond_broadcast(&check->rendezvous_cond);
    } else {
        while (generation == check->rendezvous_generation) {
            if (pthread_cond_wait(&check->rendezvous_cond,
                                  &check->rendezvous_mutex) != 0) {
                pthread_mutex_unlock(&check->rendezvous_mutex);
                return 0;
            }
        }
    }
    return pthread_mutex_unlock(&check->rendezvous_mutex) == 0;
}

static void* validate_around_unregister(void* opaque) {
    ConcurrentGuardCheck* check = (ConcurrentGuardCheck*)opaque;
    if (!rt_struct_receiver_valid((int64_t)check->receiver, 0, 8)) {
        check->failure = 1;
    } else {
        check->assertions++;
    }
    if (!rendezvous_wait(check)) {
        check->failure = 2;
        return NULL;
    }
    if (!rendezvous_wait(check)) {
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
        .rendezvous_count = 0,
        .rendezvous_generation = 0,
    };
    if (pthread_mutex_init(&check.rendezvous_mutex, NULL) != 0) return 9;
    if (pthread_cond_init(&check.rendezvous_cond, NULL) != 0) return 10;
    pthread_t validator;
    if (pthread_create(&validator, NULL, validate_around_unregister, &check) != 0) return 11;
    if (!rendezvous_wait(&check)) return 12;
    rt_free(concurrent);
    if (!rendezvous_wait(&check)) return 13;
    if (pthread_join(validator, NULL) != 0) return 14;
    if (check.failure != 0) return 20 + check.failure;
    if (pthread_cond_destroy(&check.rendezvous_cond) != 0) return 15;
    if (pthread_mutex_destroy(&check.rendezvous_mutex) != 0) return 16;
    assertions += check.assertions;

    printf("PASS assertions=%d concurrent_post_free_rejections=%d\n",
        assertions, POST_FREE_VALIDATIONS);
    return 0;
}
