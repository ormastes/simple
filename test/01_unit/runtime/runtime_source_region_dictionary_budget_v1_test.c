/* Targeted SOURCE budget controls. Includes actual native owner to inspect
 * private capacities; link actual runtime_memory.c, never stub its exports.
 * Duplicate-insertion rollback is a canonical transaction unit control, not
 * a claim of injected allocator failure inside rt_source_region_dict_new_v1. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <assert.h>
#include "../../../src/runtime/runtime_native.c"
static const uint64_t budget_rows[] = {0,8,1,0,8,8,2,1};
static const uint64_t budget_descriptor[] = {1,4,64,2,(uintptr_t)budget_rows,1};
static int64_t fixed_work(int op) {
    int64_t n=rt_source_region_bound_v1(op,0,0,0); assert(n>0); return n;
}
static int64_t dict_work(int metric) {
    int64_t n=rt_source_region_bound_v1(13,(int64_t)(uintptr_t)budget_descriptor,0,metric);
    assert(n>0); return n;
}
static int64_t stamp(int64_t c,int64_t g) {
    int64_t n=rt_source_region_stamp_v1(c,g,fixed_work(4)); assert(n>0); return n;
}
static int64_t create_dict(int64_t c,int64_t g,int64_t work) {
    return rt_source_region_dict_new_v1(c,g,stamp(c,g),
        (int64_t)(uintptr_t)budget_descriptor,0,work);
}
static void capacity_boundary(int64_t control,int64_t generation,int expect_existing) {
    rt_core_immortal_registry_acquire();
    size_t next=core_scoped_next_capacity_locked();
    size_t old_cap=rt_core_scoped_cap, old_len=rt_core_scoped_len;
    size_t module_len=rt_core_transient_heap_scope_object_len;
    size_t session_len=rt_core_session_heap_object_len;
    uint64_t birth=rt_core_scoped_next_birth;
    assert(next>0 && (!expect_existing || old_cap>0));
    rt_core_immortal_registry_release();
    int64_t bytes=dict_work(2), work=dict_work(0);
    assert((uint64_t)bytes>=next*sizeof(RtCoreScopedAllocationKey));
    assert(create_dict(control,generation,work-1)==SD_CAPACITY);
    rt_core_immortal_registry_acquire();
    assert(rt_core_scoped_cap==old_cap && rt_core_scoped_len==old_len);
    assert(rt_core_scoped_next_birth==birth);
    assert(rt_core_transient_heap_scope_object_len==module_len);
    assert(rt_core_session_heap_object_len==session_len);
    rt_core_immortal_registry_release();
    assert(create_dict(control,generation,work)>0);
    rt_core_immortal_registry_acquire();
    assert(rt_core_scoped_cap==next && rt_core_scoped_len==old_len+1);
    assert(rt_core_transient_heap_scope_object_len==module_len+1);
    assert(rt_core_session_heap_object_len==session_len);
    rt_core_immortal_registry_release();
    assert(dict_work(2)<bytes); /* paid growth really occurred, not a constant bound */
}
static void failed_insert_rollback(void* persistent) {
    rt_core_immortal_registry_acquire();
    size_t module_len=rt_core_transient_heap_scope_object_len;
    size_t session_len=rt_core_session_heap_object_len;
    size_t scoped_len=rt_core_scoped_len;
    RtCoreScopedAllocationKey key;
    assert(!core_scoped_find_locked(persistent));
    assert(rt_core_track_module_immortal_locked(persistent,&key));
    assert(key.owner==rt_core_transient_array_scope_id);
    /* This is a real failed canonical registry insertion: the persistent
     * allocation is already present. Roll back only the new MODULE ticket. */
    assert(!rt_core_immortal_registry_insert_raw((uintptr_t)persistent));
    rt_core_rollback_module_immortal_locked(key);
    assert(rt_core_transient_heap_scope_object_len==module_len);
    assert(rt_core_session_heap_object_len==session_len);
    assert(rt_core_scoped_len==scoped_len);
    assert(!core_scoped_find_locked(persistent));
    assert(core_scoped_registered_locked(persistent));
    rt_core_immortal_registry_release();
}
int main(void) {
    int64_t persistent=rt_dict_new(0); assert(persistent>0);
    void* persistent_ptr=(void*)(uintptr_t)(persistent&~INT64_C(7));
    uint32_t session=rt_session_heap_begin(); assert(session);
    assert(rt_transient_array_scope_begin());
    int64_t control=rt_source_region_create_v1(fixed_work(1)); assert(control>0);
    int64_t generation=rt_source_region_created_generation_v1(control); assert(generation>0);
    assert(rt_session_alloc_begin());
    capacity_boundary(control,generation,0); /* initial 64-key allocation */
    assert(rt_session_alloc_end());
    size_t filled=0;
    while (filled<128) {
        rt_core_immortal_registry_acquire();
        int growth=core_scoped_next_capacity_locked()!=0;
        rt_core_immortal_registry_release();
        if (growth) break;
        assert(rt_dict_new(0)>0); ++filled;
    }
    assert(filled<128);
    assert(rt_session_alloc_begin());
    capacity_boundary(control,generation,1); /* actual load threshold growth */
    failed_insert_rollback(persistent_ptr);
    assert(rt_session_alloc_end());
    assert(rt_source_region_revoke_live_v1(control,generation,16)==0);
    assert(rt_transient_array_scope_end());
    assert(rt_session_heap_end(session));
    assert(rt_source_region_release_live_v1(control,generation,64)==0);
    assert(rt_dict_free_deep(persistent)>0);
    puts("SOURCE budget initial/growth threshold, one-under refusal, canonical insertion rollback: PASS");
    return 0;
}
