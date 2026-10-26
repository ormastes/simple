/* Native-only prerequisite, authored UNRUN. Compile with runtime_native.c and
 * SIMPLE_RUNTIME_MEMORY_OWNER. Real allocator failure injection affects only
 * this included memory owner TU, never substitutes any owner implementation. */
#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
static int fail_next_calloc;
static void* copy_fixture_calloc(size_t count,size_t size) {
    if (fail_next_calloc) { fail_next_calloc=0; return NULL; }
    return calloc(count,size);
}
#define calloc copy_fixture_calloc
#include "../../../src/runtime/runtime_memory.c"
#undef calloc
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_pause(void);
extern int8_t rt_transient_array_scope_end(void);
extern int8_t rt_transient_heap_promote_share_begin(void);
extern int8_t rt_transient_heap_promote_share_end(void);
static int64_t control,generation;
static RtSourceRegionV1* region;
static int64_t fee(int operation) {
    int64_t result=rt_source_region_bound_v1(operation,0,0,0);
    assert(result>0); return result;
}
static void prepare(void) {
    int64_t w=rt_source_region_copy_bound_v1(1,0);
    int64_t f=rt_source_region_copy_bound_v1(1,1);
    int64_t b=rt_source_region_copy_bound_v1(1,2);
    assert(w>0 && f>0 && b>=8);
    assert(rt_source_region_copy_prepare_v1(control,generation,1,w-1,f,b)==SR_CAPACITY);
    assert(region->copy.state==SR_COPY_EMPTY && !rt_transient_raw_copy_scope_pinned_v1());
    assert(rt_source_region_copy_prepare_v1(control,generation,1,w,f-1,b)==SR_CAPACITY);
    assert(rt_source_region_copy_prepare_v1(control,generation,1,w,f,b-1)==SR_CAPACITY);
    assert(rt_source_region_copy_prepare_v1(control,generation,1,w,f,b)==0);
    assert(region->copy.state==SR_COPY_PREPARED && region->copy.raw==0);
    assert(rt_transient_raw_copy_scope_pinned_v1());
}
static int64_t begin(void) {
    int64_t lease=rt_source_region_read_begin_v1(control,generation,(int64_t)region->epoch,fee(5));
    assert(lease>0 && region->copy.lease==(uint64_t)lease);
    return lease;
}
static void end(int64_t lease) {
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,lease)==0);
    assert(region->copy.state==SR_COPY_CLEANED && !region->copy.raw);
    assert(rt_source_region_revoke_live_v1(control,generation,16)==SR_CONFLICT);
    assert(rt_source_region_read_end_live_v1(control,generation,lease,24)==0);
    assert(region->copy.state==SR_COPY_EMPTY && !region->lease);
    assert(!rt_transient_raw_copy_scope_pinned_v1());
}
static void* foreign_alloc(void* arg) {
    int64_t lease=*(int64_t*)arg;
    assert(rt_source_region_copy_alloc_live_v1(control,generation,lease)<0);
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,lease)<0);
    return NULL;
}
int main(void) {
    assert(rt_source_region_copy_bound_v1(1,0)<0); /* no module owner */
    assert(rt_transient_array_scope_begin());
    control=rt_source_region_create_v1(fee(1)); assert(control>0);
    generation=rt_source_region_created_generation_v1(control);
    region=sr_control(control); assert(region && generation>0);
    int64_t create_bytes=rt_source_region_bound_v1(1,0,0,2);
    assert(create_bytes>=(int64_t)(sizeof(RtSourceRegionV1)+sizeof(RtSourceControlMetadataV1)));
    prepare();
    assert(rt_source_region_read_end_live_v1(control,generation,1,24)==SR_CONSUMED);
    assert(rt_source_region_revoke_live_v1(control,generation,16)==SR_CONFLICT);
    assert(rt_source_region_close_v1(control,generation,fee(10))==SR_CONFLICT);
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,0)==0);
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,0)==SR_CONSUMED);

    prepare(); int64_t lease=begin();
    uint64_t epoch=region->epoch;
    assert(rt_source_region_copy_alloc_live_v1(control,generation+1,lease)==SR_FOREIGN);
    assert(rt_source_region_copy_alloc_live_v1(control,generation,lease+1)==SR_CONSUMED);
    int64_t ptr=rt_source_region_copy_alloc_live_v1(control,generation,lease); assert(ptr>0);
    assert(region->copy.raw==(uintptr_t)ptr && region->copy.state==SR_COPY_LIVE);
    /* Distinct ordinary heap copy, never a SOURCE member or parent alias. */
    int64_t original=37; *(int64_t*)(uintptr_t)ptr=original;
    assert((uintptr_t)&original!=(uintptr_t)ptr && *(int64_t*)(uintptr_t)ptr==37);
    assert(!region->members && region->epoch==epoch);
    assert(rt_transient_raw_copy_is_pinned_v1((void*)(uintptr_t)ptr));
    rt_free((uint8_t*)(uintptr_t)ptr);
    assert(*(int64_t*)(uintptr_t)ptr==37);
    assert(rt_realloc((void*)(uintptr_t)ptr,16)==NULL);
    assert(rt_transient_raw_promote((uintptr_t)ptr)==0);
    assert(rt_transient_array_scope_end()==0 && rt_transient_array_scope_pause()==0);
    assert(rt_transient_raw_scope_end()==0 && rt_transient_raw_scope_pause()==0);
    assert(rt_transient_heap_promote_share_begin()==0);
    assert(rt_source_region_read_end_v1(control,generation,lease,fee(6))==SR_CONFLICT);
    assert(rt_source_region_read_end_live_v1(control,generation,lease,24)==SR_CONFLICT);
    assert(rt_source_region_release_live_v1(control,generation,64)==SR_CONFLICT);
    pthread_t thread; assert(!pthread_create(&thread,NULL,foreign_alloc,&lease));
    assert(!pthread_join(thread,NULL));
    rt_struct_alloc_lock_acquire();
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,lease)==SR_INCOMPLETE);
    rt_struct_alloc_lock_release();
    assert(region->copy.raw==(uintptr_t)ptr && region->lease==(uint64_t)lease);
    uint64_t saved_words=region->copy.words; ++region->copy.words;
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,lease)==SR_STALE);
    assert(region->copy.raw==(uintptr_t)ptr && *(int64_t*)(uintptr_t)ptr==37);
    region->copy.words=saved_words;
    /* Frozen raw capacity: actual allocations reach the growth refusal. */
    void* others[256]; size_t count=0;
    int64_t cap=rt_transient_raw_copy_capacity_v1();
    while(count<256) {
        void* next=rt_alloc(8); if(!next) break;
        others[count++]=next;
    }
    assert(count>0 && count<256 && rt_transient_raw_copy_capacity_v1()==cap);
    for(size_t i=0;i<count;++i) rt_free(others[i]);
    assert(rt_transient_raw_source_prepare_v1(INT64_MAX)<0); /* compaction refused */
    end(lease);
    assert(!rt_transient_raw_owner_query((void*)(uintptr_t)ptr,NULL,NULL));
    assert(rt_source_region_copy_cleanup_live_v1(control,generation,lease)==SR_CONSUMED);

    prepare(); lease=begin();
    void* unrelated=rt_alloc(8); assert(unrelated);
    assert(rt_source_region_copy_alloc_live_v1(control,generation,lease)==SR_STALE);
    assert(!region->copy.raw && region->lease==(uint64_t)lease);
    rt_free(unrelated); end(lease);

    prepare(); lease=begin();
    fail_next_calloc=1;
    assert(rt_source_region_copy_alloc_live_v1(control,generation,lease)==SR_CAPACITY);
    assert(!fail_next_calloc && region->copy.state==SR_COPY_READY && !region->copy.raw);
    end(lease); /* allocation-error edge cleanup; no generated store occurred */
    prepare(); lease=begin(); end(lease); /* nil/null ordinary no-copy branch */
    assert(rt_source_region_revoke_live_v1(control,generation,16)==0);
    assert(rt_source_region_release_live_v1(control,generation,64)==0);
    assert(rt_transient_array_scope_end());
    assert(rt_transient_array_scope_begin()); assert(rt_transient_array_scope_pause());
    assert(rt_source_region_copy_bound_v1(1,0)<0); /* paused owner inadmissible */
    assert(rt_transient_array_scope_end());
    puts("native SOURCE parameter-copy frame: PASS; compiler/facade/backend integration UNRUN");
    return 0;
}
