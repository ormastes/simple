/* Linked with the production runtime_thread.c, never an extracted substitute. */
#include "runtime_thread.h"
#include <stdio.h>
#if defined(TEST_EMPTY_WORKER_PROVIDER)
void worker_loop_entry(int64_t pool_id) { (void)pool_id; }
#elif defined(TEST_WORKER_PROVIDER)
static int64_t observed_pool_id;
void worker_loop_entry(int64_t pool_id) { observed_pool_id = pool_id; }
#endif
int main(void) {
    spl_thread_init();
    spl_thread_handle worker = spl_thread_pool_spawn_worker(37);
#if defined(TEST_EMPTY_WORKER_PROVIDER)
    if (!worker || !spl_thread_join(worker)) {
        fputs("linked empty worker did not spawn and join\n", stderr);
        return 1;
    }
#elif defined(TEST_WORKER_PROVIDER)
    if (!worker || !spl_thread_join(worker) || observed_pool_id != 37) {
        fputs("linked worker did not execute with its pool ID\n", stderr);
        return 1;
    }
#else
    if (worker != 0) {
        spl_thread_join(worker);
        fputs("absent provider spawned a no-op worker\n", stderr);
        return 1;
    }
#endif
    return 0;
}
