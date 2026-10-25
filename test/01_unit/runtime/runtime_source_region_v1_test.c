/* Actual existing-owner primitive regression, not compiler/SOURCE admission. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"

static const uint64_t node_slots[] = {0,8,1,0, 8,8,2,1};
static const uint64_t node_descriptor[] = {1,1,16,2,(uintptr_t)node_slots,1};
static const uint64_t tagged_slots[] = {0,8,1,0, 8,8,2,2};
static const uint64_t tagged_descriptor[] = {1,1,16,2,(uintptr_t)tagged_slots,1};
static int64_t fuel(int operation) {
    int64_t result = rt_source_region_bound_v1(operation,
        operation == 2 || operation == 12 ? (int64_t)(uintptr_t)node_descriptor : 0,
        operation == 2 || operation == 12 ? 1 : 0, 0);
    assert(result > 0); return result;
}
static int64_t make_region(int64_t* generation) {
    int64_t result = rt_source_region_create_v1(fuel(1));
    assert(result > 0);
    *generation = rt_source_region_created_generation_v1(result);
    assert(rt_source_region_generation_v1(result, fuel(3)) == *generation);
    assert(*generation > 0); return result;
}
static int64_t make_node(int64_t region, int64_t generation, int64_t epoch) {
    int64_t prep = rt_source_region_allocation_prepare_v1(
        (int64_t)(uintptr_t)node_descriptor, 1, fuel(12));
    assert(prep > 0);
    int64_t result = rt_source_region_alloc_v1(region, generation, epoch,
        (int64_t)(uintptr_t)node_descriptor, 1, prep, fuel(2));
    assert(result > 0); return result;
}
#if !defined(_WIN32)
static void* foreign_thread(void* opaque) {
    const int64_t* context=(const int64_t*)opaque;
    assert(rt_source_region_stamp_v1(context[0],context[1],fuel(4)) == SR_INCOMPLETE);
    return NULL;
}
#endif

int main(void) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    extern int8_t rt_transient_array_scope_begin(void);
    extern int8_t rt_transient_array_scope_end(void);
    assert(rt_transient_array_scope_begin());
#endif
    _Static_assert(sizeof(RtStructAllocation)==2*sizeof(uintptr_t),"ordinary registry footprint");
    assert(rt_source_region_abi_v1() == 1);
    assert(rt_source_region_capabilities_v1() == 1);
    /* Bound observations inspect only six header words; this intentionally
     * inaccessible slot table must never be touched before reservation. */
    const uint64_t huge[]={1,1,(uint64_t)INT64_MAX-7,((uint64_t)INT64_MAX-7)/8,1,1};
    assert(rt_source_region_bound_v1(12,(int64_t)(uintptr_t)huge,1,0) == SR_CAPACITY);
    size_t initial_allocations=rt_struct_alloc_len;
    int64_t create_work=fuel(1);
    assert(rt_source_region_create_v1(create_work-1) == SR_CAPACITY);
    assert(rt_struct_alloc_len == initial_allocations);
    int64_t g, other_g;
    int64_t region = make_region(&g), other = make_region(&other_g);
#if !defined(_WIN32)
    pthread_t thread;
    int64_t context[]={region,g};
    assert(!pthread_create(&thread,NULL,foreign_thread,context));
    assert(!pthread_join(thread,NULL));
#endif
    int64_t root = make_node(region,g,1), child = make_node(region,g,1);
    int64_t foreign = make_node(other,other_g,1);
    int64_t preexisting = (int64_t)(uintptr_t)rt_struct_alloc(16);
    assert(preexisting > 0);
    int64_t old_epoch=rt_source_region_stamp_v1(region,g,fuel(4));
    assert(rt_source_region_alias_write_v1(region,g,root,0,99,fuel(9)-1) == SR_CAPACITY);
    assert(((int64_t*)(uintptr_t)root)[0] == 0);
    assert(rt_source_region_stamp_v1(region,g,fuel(4)) == old_epoch);
    int64_t fields=rt_source_region_bound_v1(12,(int64_t)(uintptr_t)node_descriptor,1,1);
    int64_t bytes=rt_source_region_bound_v1(12,(int64_t)(uintptr_t)node_descriptor,1,2);
    assert(fields >= 0 && bytes >= 0);
    assert(rt_source_region_bound_v1(2,(int64_t)(uintptr_t)node_descriptor,1,1) > 2);
    assert(rt_source_region_bound_v1(2,(int64_t)(uintptr_t)node_descriptor,1,2) > 16);
    int64_t ticket = rt_source_region_write_begin_v1(region,g,1,root,1,fuel(7));
    assert(ticket > 0);
    assert(rt_source_region_write_commit_v1(region,g,ticket,child,fuel(8)) == 2);
    assert(((int64_t*)(uintptr_t)root)[1] == child);
    assert(rt_source_region_write_commit_v1(region,g,ticket,child,fuel(8)) == SR_CONSUMED);
    /* Alias acquired before first read; descendant write invalidates region. */
    int64_t alias = child;
    int64_t lease = rt_source_region_read_begin_v1(region,g,2,fuel(5));
    assert(lease > 0);
    assert(rt_source_region_alias_write_v1(region,g,alias,0,7,fuel(9)) == SR_CONFLICT);
    assert(rt_source_region_read_end_v1(region,g,lease,fuel(6)) == 0);
    assert(rt_source_region_read_end_v1(region,g,lease,fuel(6)) == SR_CONSUMED);
    assert(rt_source_region_alias_write_v1(region,g,alias,0,7,fuel(9)) == 3);
    assert(((int64_t*)(uintptr_t)child)[0] == 7);
    assert(rt_source_region_read_begin_v1(region,g,2,fuel(5)) == SR_STALE);
    assert(rt_source_region_alias_write_v1(region,g,alias,0,7,fuel(9)) == 4);
    /* Foreign and preexisting children reject before the edge changes. */
    assert(rt_source_region_alias_write_v1(region,g,root,1,foreign,fuel(9)) == SR_FOREIGN);
    assert(rt_source_region_alias_write_v1(region,g,root,1,preexisting,fuel(9)) == SR_FOREIGN);
    assert(((int64_t*)(uintptr_t)root)[1] == child);
    assert(rt_source_region_stamp_v1(region,g,fuel(4)) == 4);
    assert(rt_source_region_alias_write_v1(other,other_g,root,0,8,fuel(9)) == SR_FOREIGN);
    /* Rehash actual owner entries, then retain transitive authority. */
    uint8_t* unrelated[200];
    for (int i=0;i<200;++i) { unrelated[i]=rt_struct_alloc(8); assert(unrelated[i]); }
    assert(rt_source_region_alias_write_v1(region,g,child,0,9,fuel(9)) == 5);
    assert(rt_source_region_read_begin_v1(region,g,4,fuel(5)) == SR_STALE);
    /* Preparation token is invalidated by an ordinary allocation event. */
    int64_t prep=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)node_descriptor,1,fuel(12));
    uint8_t* extra=rt_struct_alloc(8); assert(extra);
    assert(rt_source_region_alloc_v1(region,g,5,(int64_t)(uintptr_t)node_descriptor,1,prep,fuel(2)) == SR_STALE);
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    prep=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)node_descriptor,1,fuel(12));
    uint8_t* raw=rt_alloc(8); assert(raw);
    assert(rt_source_region_alloc_v1(region,g,5,(int64_t)(uintptr_t)node_descriptor,1,prep,fuel(2)) == SR_STALE);
    rt_free(raw);
#endif
    /* Descriptor-qualified Struct tags normalize only the owner lookup;
     * the actual committed word retains its ordinary tagged representation. */
    int64_t tagged_g, tagged_region=make_region(&tagged_g);
    int64_t tagged_prep=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)tagged_descriptor,1,fuel(12));
    assert(tagged_prep>0);
    int64_t tagged_root=rt_source_region_alloc_v1(tagged_region,tagged_g,1,
        (int64_t)(uintptr_t)tagged_descriptor,1,tagged_prep,fuel(2));
    assert(tagged_root>0);
    int64_t tagged_child=make_node(tagged_region,tagged_g,1);
    assert(rt_source_region_alias_write_v1(tagged_region,tagged_g,tagged_root,1,tagged_child|1,fuel(9))==2);
    assert(((int64_t*)(uintptr_t)tagged_root)[1]==(tagged_child|1));
    assert(rt_source_region_alias_write_v1(tagged_region,tagged_g,tagged_root,1,tagged_child|2,fuel(9))==SR_FOREIGN);
    assert(rt_source_region_alias_write_v1(tagged_region,tagged_g,tagged_root,1,0,fuel(9))==SR_FOREIGN);
    assert(rt_source_region_alias_write_v1(tagged_region,tagged_g,tagged_root,1,foreign|1,fuel(9))==SR_FOREIGN);
    assert(rt_source_region_stamp_v1(tagged_region,tagged_g,fuel(4))==2);
    assert(rt_source_region_close_v1(tagged_region,tagged_g,fuel(10))==0);
    rt_free((uint8_t*)(uintptr_t)tagged_root); rt_free((uint8_t*)(uintptr_t)tagged_child);
    assert(rt_source_region_release_v1(tagged_region,tagged_g,fuel(11))==0);
    assert(rt_source_region_close_v1(region,g,fuel(10)) == 0);
    assert(rt_source_region_stamp_v1(region,g,fuel(4)) == SR_CLOSED);
    assert(rt_source_region_release_v1(region,g,fuel(11)) == SR_CONFLICT);
    rt_free((uint8_t*)(uintptr_t)root); rt_free((uint8_t*)(uintptr_t)child);
    assert(rt_source_region_release_v1(region,g,fuel(11)) == 0);
    assert(rt_source_region_stamp_v1(region,g,fuel(4)) == SR_INCOMPLETE);
    int64_t next_g, next=make_region(&next_g);
    assert(next_g != g);
    assert(rt_source_region_stamp_v1(next,g,fuel(4)) == SR_FOREIGN);
    int64_t realloc_g,realloc_region=make_region(&realloc_g);
    int64_t realloc_node=make_node(realloc_region,realloc_g,1);
    assert(rt_struct_receiver_valid(realloc_node,8,8));
    assert(!rt_struct_receiver_valid(realloc_node,16,8));
    uint8_t* copied=rt_realloc((uint8_t*)(uintptr_t)realloc_node,32);
    assert(copied);
    assert(rt_source_region_stamp_v1(realloc_region,realloc_g,fuel(4))==SR_CLOSED);
    assert(rt_source_region_release_v1(realloc_region,realloc_g,fuel(11))==0);
    rt_free(copied);
    /* Generation/epoch exhaustion is exercised through actual writer path. */
    int64_t exhausted=make_node(next,next_g,1);
    sr_control(next)->epoch=INT64_MAX;
    assert(rt_source_region_alias_write_v1(next,next_g,exhausted,0,1,fuel(9)) == SR_CAPACITY);
    assert(rt_source_region_stamp_v1(next,next_g,fuel(4)) == SR_CAPACITY);
    assert(rt_source_region_close_v1(next,next_g,fuel(10)) == 0);
    rt_free((uint8_t*)(uintptr_t)exhausted);
    assert(rt_source_region_release_v1(next,next_g,fuel(11)) == 0);
    rt_source_region_close_v1(other,other_g,fuel(10));
    rt_free((uint8_t*)(uintptr_t)foreign);
    assert(rt_source_region_release_v1(other,other_g,fuel(11)) == 0);
    rt_free((uint8_t*)(uintptr_t)preexisting); rt_free(extra);
    for(int i=0;i<200;++i) rt_free(unrelated[i]);
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    assert(rt_transient_array_scope_end());
#endif
    puts("C4 raw struct primitive: PASS (full SOURCE UNRUN)");
    return 0;
}
