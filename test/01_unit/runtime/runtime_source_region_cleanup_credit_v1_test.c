/* Separate native cleanup integration regression. This never executes the
 * exhausted general primitive test, and supplies no safe compiler-pin proof.
 * Every direct live operand below is an actually born, retained C controller. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"

typedef struct CleanupController {
    int64_t control, generation, revoke, read_end, release_first, release_second;
} CleanupController;

static int64_t work(int op) {
    int64_t result=rt_source_region_bound_v1(op,0,0,0);
    assert(result>0); return result;
}

static CleanupController born_controller(void) {
    /* Fixed allowances are recorded before any producer activity. Actual
     * shared-Simple-account escrow remains a separate compiler integration. */
    CleanupController c={0};
    c.revoke=rt_source_region_live_cleanup_bound_v1(1,0);
    c.read_end=rt_source_region_live_cleanup_bound_v1(2,0);
    c.release_first=rt_source_region_live_cleanup_bound_v1(3,0);
    c.release_second=c.release_first;
    assert(c.revoke>0 && c.read_end>0 && c.release_first>0);
    c.control=rt_source_region_create_v1(work(1));
    assert(c.control>0);
    c.generation=rt_source_region_created_generation_v1(c.control);
    assert(c.generation>0);
    return c;
}

static int64_t consume(int64_t* credit) {
    int64_t amount=*credit;
    assert(amount>0);
    *credit=0;
    return amount;
}

int main(void) {
    _Static_assert(sizeof(RtStructAllocation)==2*sizeof(uintptr_t),"ordinary footprint");
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    extern int8_t rt_transient_array_scope_begin(void);
    extern int8_t rt_transient_array_scope_end(void);
    assert(rt_transient_array_scope_begin());
#endif
    CleanupController c=born_controller();
    int64_t lease=rt_source_region_read_begin_v1(c.control,c.generation,1,work(5));
    assert(lease>0);
    size_t prior_capacity=rt_struct_alloc_cap;
    uint8_t* unrelated[800];
    for(int i=0;i<800;++i) { unrelated[i]=rt_struct_alloc(8); assert(unrelated[i]); }
    assert(rt_struct_alloc_cap>prior_capacity);
    /* Credits survive genuine unrelated owner rehash. No bound recomputation
     * or account access is needed by any operation below. */
    assert(rt_source_region_live_cleanup_bound_v1(1,0)==c.revoke);
    assert(rt_source_region_live_cleanup_bound_v1(2,0)==c.read_end);
    assert(rt_source_region_live_cleanup_bound_v1(3,0)==c.release_first);
    assert(rt_source_region_revoke_live_v1(c.control,c.generation,c.revoke-1)==SR_CAPACITY);
    assert(rt_source_region_stamp_v1(c.control,c.generation,work(4))==1);

    rt_struct_alloc_lock_acquire();
    /* Revocation and the owner-thread lease end do not wait on, or probe,
     * the global registry even when its existing lock is already held. */
    assert(rt_source_region_revoke_live_v1(c.control,c.generation,consume(&c.revoke))==0);
    assert(rt_source_region_read_end_live_v1(c.control,c.generation,lease,consume(&c.read_end))==0);
    assert(rt_source_region_release_live_v1(c.control,c.generation,consume(&c.release_first))==SR_INCOMPLETE);
    assert(c.control>0 && !c.release_first);
    rt_struct_alloc_lock_release();
    assert(rt_source_region_stamp_v1(c.control,c.generation,work(4))==SR_CLOSED);
    /* A different, separately retained attempt credit enables explicit retry. */
    assert(rt_source_region_release_live_v1(c.control,c.generation,consume(&c.release_second))==0);
    c.control=0;

    CleanupController leased=born_controller();
    lease=rt_source_region_read_begin_v1(leased.control,leased.generation,1,work(5));
    assert(lease>0);
    assert(rt_source_region_revoke_live_v1(leased.control,leased.generation,consume(&leased.revoke))==0);
    assert(rt_source_region_release_live_v1(leased.control,leased.generation,consume(&leased.release_first))==SR_CONFLICT);
    assert(leased.control>0);
    assert(rt_source_region_read_end_live_v1(leased.control,leased.generation,lease,consume(&leased.read_end))==0);
    assert(rt_source_region_release_live_v1(leased.control,leased.generation,consume(&leased.release_second))==0);
    leased.control=0;

    /* A failed producer can leave a ticket. Atomic revoke invalidates it but
     * does not race by touching plain writer fields; final locked release can
     * discard it after the actual allocation owner retires the member. */
    CleanupController writing=born_controller();
    static const uint64_t slots[]={0,8,1,0};
    const uint64_t descriptor[]={1,1,8,1,(uintptr_t)slots,1};
    int64_t prep_work=rt_source_region_bound_v1(12,(int64_t)(uintptr_t)descriptor,1,0);
    int64_t prep=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)descriptor,1,prep_work);
    assert(prep>0);
    int64_t alloc_work=rt_source_region_bound_v1(2,(int64_t)(uintptr_t)descriptor,1,0);
    int64_t member=rt_source_region_alloc_v1(writing.control,writing.generation,1,
        (int64_t)(uintptr_t)descriptor,1,prep,alloc_work);
    assert(member>0);
    int64_t ticket=rt_source_region_write_begin_v1(writing.control,writing.generation,1,member,0,work(7));
    assert(ticket>0);
    assert(rt_source_region_revoke_live_v1(writing.control,writing.generation,consume(&writing.revoke))==0);
    assert(rt_source_region_write_commit_v1(writing.control,writing.generation,ticket,9,work(8))==SR_CLOSED);
    assert(rt_source_region_release_live_v1(writing.control,writing.generation,consume(&writing.release_first))==SR_CONFLICT);
    rt_free((uint8_t*)(uintptr_t)member);
    assert(rt_source_region_release_live_v1(writing.control,writing.generation,consume(&writing.release_second))==0);
    writing.control=0;

    for(int i=0;i<800;++i) rt_free(unrelated[i]);
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    assert(rt_transient_array_scope_end());
#endif
    puts("C4 private live cleanup integration: PASS (safe pin/account admission UNRUN)");
    return 0;
}
