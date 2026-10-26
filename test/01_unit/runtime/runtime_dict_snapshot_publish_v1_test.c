/* NEW wrapper-specific acceptance controls; no old aggregate fixture rerun.
 * Unsafe C-owner fixture, not proof of compiler confinement or typed lowering. */
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include "../../../src/runtime/runtime_memory.c"
#include "../../../src/runtime/runtime_dict_snapshot_v1.h"
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int64_t rt_dict_new(int64_t);
extern int8_t rt_dict_set(int64_t,int64_t,int64_t);
extern int64_t rt_value_int(int64_t);
typedef struct PublishArrayHeader {
    uint8_t kind,flags; uint16_t reserved; uint32_t scope;
    int64_t len,cap; void* data;
} PublishArrayHeader;
static RtDictSnapshotV1 observation(int64_t d) {
    RtDictSnapshotV1 result;
    int64_t w=rt_dict_snapshot_observation_bound_v1(); assert(w>0);
    assert(rt_dict_snapshot_observe_v1(d,w,&result)==0); return result;
}
static RtArraySnapshotV1 allocation(int64_t n) {
    RtArraySnapshotV1 result={0};
    int64_t w=rt_array_snapshot_bound_v1(n,0),f=rt_array_snapshot_bound_v1(n,1),b=rt_array_snapshot_bound_v1(n,2);
    assert(w>0 && f>0 && b>0);
    assert(rt_array_snapshot_new_v1(n,w,f,b,&result)==0); return result;
}
static int64_t bound(RtDictSnapshotV1* s) {
    int64_t w=rt_dict_snapshot_fill_bound_v1(s->capacity,s->length); assert(w>0); return w;
}
static void release(RtArraySnapshotV1* a) {
    int64_t w=rt_dict_snapshot_fill_bound_v1(0,0); assert(w>0);
    assert(rt_array_snapshot_dispose_v1(a,w)==0);
}
int main(void) {
#if UINTPTR_MAX != UINT64_MAX
    assert(rt_dict_snapshot_fill_publish_v1(0,NULL,NULL,0)==-1);
    puts("private snapshot publication unsupported on non64 ABI: PASS");
#else
    assert(rt_transient_array_scope_begin());
    int64_t d=rt_dict_new(0); assert(d>0);
    RtDictSnapshotV1 empty=observation(d);
    RtArraySnapshotV1 zero=allocation(0), copied_zero=zero;
    int64_t published=rt_dict_snapshot_fill_publish_v1(d,&empty,&zero,bound(&empty));
    assert(published==zero.array && published>0 && zero.consumed);
    PublishArrayHeader* header=(PublishArrayHeader*)(uintptr_t)(published&~INT64_C(7));
    assert(header->len==0 && !header->flags);
    assert(rt_dict_snapshot_fill_publish_v1(d,&empty,&copied_zero,bound(&empty))==-1);
    assert(rt_array_snapshot_dispose_v1(&copied_zero,rt_dict_snapshot_fill_bound_v1(0,0))==-1);

    assert(rt_dict_set(d,rt_value_int(11),rt_value_int(301)));
    RtDictSnapshotV1 one=observation(d);
    RtArraySnapshotV1 full=allocation(1), copied_full=full;
    published=rt_dict_snapshot_fill_publish_v1(d,&one,&full,bound(&one));
    assert(published==full.array && full.consumed);
    header=(PublishArrayHeader*)(uintptr_t)(published&~INT64_C(7));
    assert(header->len==1 && !header->flags && ((int64_t*)header->data)[0]==rt_value_int(301));
    assert(rt_dict_snapshot_fill_publish_v1(d,&one,&copied_full,bound(&one))==-1);

    RtArraySnapshotV1 short_a=allocation(1), short_b=allocation(1);
    int64_t work=bound(&one);
    assert(rt_dict_snapshot_fill_v1(d,&one,&short_a,work-1)==-4);
    assert(rt_dict_snapshot_fill_publish_v1(d,&one,&short_b,work-1)==-4);
    assert(!short_b.consumed);
    header=(PublishArrayHeader*)(uintptr_t)(short_b.array&~INT64_C(7));
    assert(header->len==0 && header->flags==0x40);
    release(&short_a); release(&short_b);

    RtArraySnapshotV1 stale_a=allocation(1), stale_b=allocation(1);
    assert(rt_dict_set(d,rt_value_int(11),rt_value_int(302)));
    assert(rt_dict_snapshot_fill_v1(d,&one,&stale_a,bound(&one))==-3);
    assert(rt_dict_snapshot_fill_publish_v1(d,&one,&stale_b,bound(&one))==-3);
    assert(!stale_b.consumed);
    release(&stale_a); release(&stale_b);

    RtDictSnapshotV1 current=observation(d);
    assert(rt_dict_snapshot_fill_publish_v1(d,&current,NULL,bound(&current))==-1);
    RtArraySnapshotV1 null_expected=allocation(1);
    assert(rt_dict_snapshot_fill_publish_v1(d,NULL,&null_expected,bound(&current))==-1);
    release(&null_expected);
    RtArraySnapshotV1 disposed=allocation(1), copied_disposed=disposed;
    release(&disposed);
    assert(rt_dict_snapshot_fill_publish_v1(d,&current,&disposed,bound(&current))==-1);
    assert(rt_dict_snapshot_fill_publish_v1(d,&current,&copied_disposed,bound(&current))==-1);

    /* Underfunded fill must reject before output header dereference, even
     * when a corrupted witness contains an unmapped tagged address. */
    RtArraySnapshotV1 forged={0}; forged.array=4097; forged.birth=1; forged.owner=1;
    RtArraySnapshotV1 saved=forged;
    assert(rt_dict_snapshot_fill_publish_v1(d,&current,&forged,0)==-4);
    assert(memcmp(&forged,&saved,sizeof(forged))==0);
    assert(rt_transient_array_scope_end());
    puts("snapshot actual-fill publication wrapper: PASS (typed compiler bridge UNRUN)");
#endif
    return 0;
}
