/* Host execution of the x86 bare-metal atomic SFFI with real contention.
 * Link against rt_extras.c with function-section dead stripping. */
#include <pthread.h>
#include <stdint.h>

typedef int64_t RuntimeValue;
extern RuntimeValue rt_atomic_int_new(RuntimeValue initial);
extern RuntimeValue rt_atomic_int_load(RuntimeValue handle);
extern RuntimeValue rt_atomic_int_compare_exchange(RuntimeValue handle,
                                                    RuntimeValue expected,
                                                    RuntimeValue desired);
extern RuntimeValue rt_atomic_int_fetch_add(RuntimeValue handle, RuntimeValue value);

enum { THREADS = 4, ITERATIONS = 50000 };
static RuntimeValue fetch_handle;
static RuntimeValue cas_handle;

static void *worker(void *ignored) {
    (void)ignored;
    for (int i = 0; i < ITERATIONS; ++i) {
        rt_atomic_int_fetch_add(fetch_handle, 1);
        for (;;) {
            RuntimeValue before = rt_atomic_int_load(cas_handle);
            if (rt_atomic_int_compare_exchange(cas_handle, before, before + 1))
                break;
        }
    }
    return 0;
}

int main(void) {
    pthread_t threads[THREADS];
    fetch_handle = rt_atomic_int_new(0);
    cas_handle = rt_atomic_int_new(0);
    if (!fetch_handle || !cas_handle) return 1;
    for (int i = 0; i < THREADS; ++i)
        if (pthread_create(&threads[i], 0, worker, 0)) return 2;
    for (int i = 0; i < THREADS; ++i)
        if (pthread_join(threads[i], 0)) return 3;
    if (rt_atomic_int_load(fetch_handle) != THREADS * ITERATIONS) return 4;
    if (rt_atomic_int_load(cas_handle) != THREADS * ITERATIONS) return 5;
    return 0;
}
