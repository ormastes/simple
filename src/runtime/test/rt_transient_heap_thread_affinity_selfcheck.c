#include <assert.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>

#include "../runtime.h"

typedef struct ForeignAttempt {
    int64_t* ptr;
    void* realloc_result;
} ForeignAttempt;

static void* reject_foreign_mutation(void* opaque) {
    ForeignAttempt* attempt = (ForeignAttempt*)opaque;
    attempt->realloc_result = rt_realloc(attempt->ptr, 32);
    rt_free(attempt->ptr);
    return NULL;
}

static void* free_after_transfer(void* opaque) {
    rt_free(opaque);
    return NULL;
}

int main(void) {
    assert(rt_transient_array_scope_begin() == 1);
    int64_t* same_thread = (int64_t*)rt_alloc(16);
    assert(same_thread != NULL);
    same_thread[0] = 0x1234;
    same_thread = (int64_t*)rt_realloc(same_thread, 32);
    assert(same_thread != NULL && same_thread[0] == 0x1234);
    assert(rt_transient_array_scope_pause() == 1);
    assert(rt_transient_heap_promote((int64_t)((uintptr_t)same_thread | 1)) == 1);
    assert(rt_transient_array_scope_end() == 1);
    assert(same_thread[0] == 0x1234);
    rt_free(same_thread);

    assert(rt_transient_array_scope_begin() == 1);
    int64_t* transferred = (int64_t*)rt_alloc(16);
    assert(transferred != NULL);
    transferred[0] = 0x5678;
    ForeignAttempt attempt = {transferred, (void*)(uintptr_t)1};
    pthread_t worker;
    assert(pthread_create(&worker, NULL, reject_foreign_mutation, &attempt) == 0);
    assert(pthread_join(worker, NULL) == 0);
    assert(attempt.realloc_result == NULL);
    assert(transferred[0] == 0x5678);
    assert(rt_transient_array_scope_pause() == 1);
    assert(rt_transient_heap_promote((int64_t)((uintptr_t)transferred | 1)) == 1);
    assert(rt_transient_array_scope_end() == 1);

    assert(pthread_create(&worker, NULL, free_after_transfer, transferred) == 0);
    assert(pthread_join(worker, NULL) == 0);
    puts("SELFCHECK PASSED (0 failures)");
    return 0;
}
