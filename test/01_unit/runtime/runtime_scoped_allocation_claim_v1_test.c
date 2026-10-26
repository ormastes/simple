/* Private canonical-owner regression. Compile this TU (runtime_native included)
 * with runtime_memory.c, function/data sections and --gc-sections. Deliberately
 * tiny: this is C owner evidence, never full compiler/capsule qualification. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <assert.h>
#include <pthread.h>
#include "../../../src/runtime/runtime_native.c"

static RtCoreScopedAllocationKey identity(void* ptr) {
    rt_core_immortal_registry_acquire();
    RtCoreScopedAllocationKey* live = core_scoped_find_locked(ptr);
    assert(live);
    RtCoreScopedAllocationKey result = *live;
    rt_core_immortal_registry_release();
    return result;
}
static RtCoreString* controlled_string(void* storage) {
    RtCoreString* string = storage;
    string->kind = RT_VALUE_HEAP_STRING;
    string->reserved = 0;
    string->len = 4;
    memcpy(string->data, "live", 5);
    assert(rt_core_register_string(string));
    return string;
}
static int64_t tagged(void* ptr) { return (int64_t)((uintptr_t)ptr | RT_VALUE_TAG_HEAP); }
static RtCoreString* fresh_string(void) {
    void* storage = malloc(sizeof(RtCoreString) + 5);
    assert(storage);
    return controlled_string(storage);
}
static pthread_barrier_t rendezvous;
static void* reused_storage;
static RtCoreScopedAllocationKey foreign_key;
static void* foreign_session(void* unused) {
    (void)unused;
    uint32_t session = rt_session_heap_begin(); assert(session);
    controlled_string(reused_storage);
    foreign_key = identity(reused_storage);
    pthread_barrier_wait(&rendezvous);
    pthread_barrier_wait(&rendezvous);
    assert(rt_core_is_registered_immortal_ptr(reused_storage));
    assert(!memcmp(((RtCoreString*)reused_storage)->data, "live", 5));
    assert(rt_session_heap_end(session));
    return NULL;
}
static void same_address_foreign_session(void) {
    uint32_t session = rt_session_heap_begin(); assert(session);
    RtCoreString* old = fresh_string();
    RtCoreScopedAllocationKey stale = identity(old);
    /* Controlled allocator: canonically retire A, then reuse that exact storage
     * for B. Delaying libc disposal makes the ABA schedule deterministic. */
    RtCoreClaimedAllocation captured;
    rt_core_heap_lifecycle_acquire();
    assert(core_claim_registered_free_locked(old, &captured));
    rt_core_heap_lifecycle_release();
    assert(captured.ptr == old && !captured.backing);
    reused_storage = captured.ptr;
    assert(!pthread_barrier_init(&rendezvous, NULL, 2));
    pthread_t worker; assert(!pthread_create(&worker, NULL, foreign_session, NULL));
    pthread_barrier_wait(&rendezvous);
    assert(foreign_key.ptr == stale.ptr && foreign_key.birth != stale.birth);
    assert(foreign_key.owner != stale.owner);
    rt_core_heap_lifecycle_acquire();
    assert(core_claim_scoped_free_locked(stale, &captured) == RT_CORE_CLAIM_NOT_OWNED);
    /* Matching owner alone is insufficient when a ledger birth is stale. */
    RtCoreScopedAllocationKey wrong_birth = foreign_key;
    wrong_birth.birth = stale.birth;
    assert(core_claim_scoped_free_locked(wrong_birth, &captured) == RT_CORE_CLAIM_NOT_OWNED);
    rt_core_heap_lifecycle_release();
    assert(rt_session_heap_end(session));
    assert(rt_core_is_registered_immortal_ptr(reused_storage));
    pthread_barrier_wait(&rendezvous);
    assert(!pthread_join(worker, NULL));
    assert(!rt_core_is_registered_immortal_ptr(reused_storage));
    pthread_barrier_destroy(&rendezvous);
}
static void transfer_and_pins(void) {
    uint32_t session = rt_session_heap_begin(); assert(session);
    assert(rt_transient_array_scope_begin());
    RtCoreString* retained = fresh_string();
    RtCoreScopedAllocationKey module = identity(retained);
    assert(rt_transient_array_scope_pause());
    assert(rt_transient_heap_adopt(tagged(retained)));
    RtCoreScopedAllocationKey adopted = identity(retained);
    assert(adopted.birth == module.birth && adopted.owner == session);
    RtCoreClaimedAllocation captured;
    rt_core_heap_lifecycle_acquire();
    assert(core_claim_scoped_free_locked(module, &captured) == RT_CORE_CLAIM_NOT_OWNED);
    rt_core_heap_lifecycle_release();
    assert(rt_transient_array_scope_end());
    assert(rt_core_is_registered_immortal_ptr(retained));
    assert(rt_string_free(tagged(retained)) == 1);
    assert(rt_string_free(tagged(retained)) == 0);
    int64_t closure = rt_closure_new(1, 0);
    assert(rt_closure_retain(closure));
    void* closure_ptr = (void*)(uintptr_t)(closure & ~INT64_C(7));
    RtCoreScopedAllocationKey pinned = identity(closure_ptr);
    assert(rt_session_heap_end(session));
    assert(identity(closure_ptr).birth == pinned.birth);
    assert(rt_closure_release(closure) == 1);
    assert(rt_closure_release(closure) == 0);
    assert(!rt_core_is_registered_immortal_ptr(closure_ptr));
}
static void native_and_deep_free(void) {
    uint32_t session = rt_session_heap_begin(); assert(session);
    assert(rt_transient_array_scope_begin());
    RtCoreString* module_only = fresh_string();
    RtCoreString* promoted = fresh_string();
    SplArray* shallow = rt_array_new(1); assert(shallow);
    void* shallow_ptr = rt_core_as_registered_array((int64_t)(uintptr_t)shallow);
    rt_array_free(shallow);
    assert(!rt_core_is_registered_immortal_ptr(shallow_ptr));
    SplArray* deep = rt_array_new(1); assert(deep);
    RtCoreString* child = fresh_string();
    assert(rt_array_push(deep, tagged(child)));
    void* deep_ptr = rt_core_as_registered_array((int64_t)(uintptr_t)deep);
    assert(rt_array_free_deep(tagged(deep_ptr)) == 1);
    assert(!rt_core_is_registered_immortal_ptr(child));
    assert(rt_transient_array_scope_pause());
    assert(rt_transient_heap_promote(tagged(promoted)));
    assert(identity(promoted).owner == session);
    assert(rt_transient_array_scope_end());
    assert(!rt_core_is_registered_immortal_ptr(module_only));
    assert(rt_core_is_registered_immortal_ptr(promoted));
    assert(rt_session_heap_end(session));
    assert(!rt_core_is_registered_immortal_ptr(promoted));
    assert(rt_transient_array_scope_begin());
    RtCoreString* permanent = fresh_string();
    assert(rt_transient_array_scope_pause());
    assert(rt_transient_heap_promote(tagged(permanent)));
    rt_core_immortal_registry_acquire();
    assert(!core_scoped_find_locked(permanent));
    rt_core_immortal_registry_release();
    assert(rt_transient_array_scope_end());
    assert(rt_string_free(tagged(permanent)) == 1);
}
static void rollback_and_exhaustion(void) {
    uint32_t session = rt_session_heap_begin(); assert(session);
    assert(rt_transient_array_scope_begin());
    assert(rt_session_alloc_begin());
    void* storage = malloc(32); assert(storage);
    RtCoreScopedAllocationKey key;
    rt_core_immortal_registry_acquire();
    size_t before = rt_core_transient_heap_scope_object_len;
    size_t session_before = rt_core_session_heap_object_len;
    assert(rt_core_track_module_immortal_locked(storage, &key));
    assert(key.owner == rt_core_transient_array_scope_id && key.owner != session);
    RtCoreScopedAllocationKey wrong = key; ++wrong.birth;
    rt_core_rollback_module_immortal_locked(wrong);
    assert(core_scoped_find_locked(storage));
    assert(rt_core_transient_heap_scope_object_len == before + 1);
    rt_core_rollback_module_immortal_locked(key);
    assert(!core_scoped_find_locked(storage));
    assert(rt_core_transient_heap_scope_object_len == before);
    assert(rt_core_session_heap_object_len == session_before);
    rt_core_scoped_next_birth = UINT64_MAX;
    assert(rt_core_track_module_immortal_locked(storage, &key));
    assert(key.birth == UINT64_MAX && !rt_core_scoped_next_birth);
    rt_core_rollback_module_immortal_locked(key);
    assert(!rt_core_track_module_immortal_locked(storage, &key));
    assert(rt_core_transient_heap_scope_object_len == before);
    rt_core_immortal_registry_release();
    free(storage);
    assert(rt_session_alloc_end());
    assert(rt_transient_array_scope_end());
    assert(rt_session_heap_end(session));
}
int main(void) {
    _Static_assert(sizeof(RtCoreString) == 16, "string ABI must remain 16 bytes");
    size_t baseline = atomic_load(&rt_core_heap_registry_count);
    same_address_foreign_session();
    transfer_and_pins();
    native_and_deep_free();
    rollback_and_exhaustion();
    assert(atomic_load(&rt_core_heap_registry_count) == baseline);
    assert(rt_core_scoped_len == 0);
    puts("C scoped identity: address reuse, foreign session, transfer, pin, rollback, exhaustion PASS");
    return 0;
}
