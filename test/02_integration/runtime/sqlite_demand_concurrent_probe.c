#include <pthread.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>

extern int64_t rt_sqlite_open_memory(void);
extern int64_t rt_sqlite_close(int64_t);
extern int64_t rt_sqlite_demand_state(void);

static atomic_int sqlite_probe_start = ATOMIC_VAR_INIT(0);

static void *sqlite_probe_worker(void *unused) {
    (void)unused;
    while (atomic_load_explicit(&sqlite_probe_start, memory_order_acquire) == 0)
        sched_yield();
    int64_t handle = rt_sqlite_open_memory();
    if (handle <= 0 || handle == 3 || rt_sqlite_close(handle) != 1)
        return (void *)0;
    return (void *)1;
}

int64_t rt_sqlite_demand_concurrent_probe(void) {
    pthread_t threads[4];
    int started = 0;
    int success = 1;
    if (rt_sqlite_demand_state() != 0) return 0;
    for (; started < 4; started++) {
        if (pthread_create(&threads[started], NULL,
                sqlite_probe_worker, NULL) != 0) break;
    }
    atomic_store_explicit(&sqlite_probe_start, 1, memory_order_release);
    for (int i = 0; i < started; i++) {
        void *result = NULL;
        if (pthread_join(threads[i], &result) != 0 || result != (void *)1)
            success = 0;
    }
    return started == 4 && success && rt_sqlite_demand_state() == 2;
}
