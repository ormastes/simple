/* Authored UNRUN: private C-owner protocol, NOT compiler confinement proof. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"
#include "../../../src/runtime/runtime_dict_snapshot_v1.h"
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int64_t rt_dict_new(int64_t);
extern int8_t rt_dict_set(int64_t,int64_t,int64_t);
extern int8_t rt_dict_remove(int64_t,int64_t);
extern int64_t rt_value_int(int64_t);
extern int64_t rt_array_at(int64_t,int64_t);
typedef struct SnapshotDictHeader {
    uint8_t kind,flags; uint16_t reserved; uint32_t scope;
    int64_t cap,len,tombs; void* entries; int64_t owner,epoch,backing;
} SnapshotDictHeader;
typedef struct SnapshotArrayHeader {
    uint8_t kind,flags; uint16_t reserved; uint32_t scope;
    int64_t len,cap; void* data;
} SnapshotArrayHeader;
static RtDictSnapshotV1 observe(int64_t d) {
    RtDictSnapshotV1 value;
    int64_t q=rt_dict_snapshot_observation_bound_v1(); assert(q>0);
    assert(rt_dict_snapshot_observe_v1(d,q,&value)==0); return value;
}
static RtArraySnapshotV1 output(int64_t n) {
    RtArraySnapshotV1 value={0};
    int64_t w=rt_array_snapshot_bound_v1(n,0),f=rt_array_snapshot_bound_v1(n,1),b=rt_array_snapshot_bound_v1(n,2);
    assert(w>0 && f>0 && b>0);
    assert(rt_array_snapshot_new_v1(n,w-1,f,b,&value)<0 && !value.array);
    assert(rt_array_snapshot_new_v1(n,w,f,b,&value)==0); return value;
}
static int64_t fill(int64_t d,RtDictSnapshotV1* s,RtArraySnapshotV1* a) {
    int64_t w=rt_dict_snapshot_fill_bound_v1(s->capacity,s->length); assert(w>0);
    return rt_dict_snapshot_fill_v1(d,s,a,w);
}
static void dispose(RtArraySnapshotV1* a) {
    int64_t w=rt_dict_snapshot_fill_bound_v1(0,0); assert(w>0);
    assert(rt_array_snapshot_dispose_v1(a,w)==0);
    assert(rt_array_snapshot_dispose_v1(a,w)<0); /* exactly one disposal */
}
int main(void) {
    assert(rt_transient_array_scope_begin());
    int64_t d=rt_dict_new(0); assert(d>0);
    RtDictSnapshotV1 untouched={0};
    int64_t q=rt_dict_snapshot_observation_bound_v1(); assert(q>0);
    assert(rt_dict_snapshot_observe_v1(4097,q,&untouched)<0 && !untouched.dictionary);
    assert(rt_dict_snapshot_observe_v1(d,q-1,&untouched)<0 && !untouched.dictionary);
    RtDictSnapshotV1 empty=observe(d); RtArraySnapshotV1 zero=output(0);
    RtArraySnapshotV1 copied_zero=zero;
    assert(fill(d,&empty,&zero)==0 && zero.consumed);
    assert(rt_array_snapshot_dispose_v1(&copied_zero,rt_dict_snapshot_fill_bound_v1(0,0))<0);
    for(int64_t i=0;i<64;++i) assert(rt_dict_set(d,rt_value_int(i),rt_value_int(i+100)));
    for(int64_t i=0;i<63;++i) assert(rt_dict_remove(d,rt_value_int(i)));
    RtDictSnapshotV1 sparse=observe(d);
    assert(sparse.capacity>sparse.length && sparse.length==1 && sparse.tombstones>0);
    RtArraySnapshotV1 a=output(1);
    int64_t w=rt_dict_snapshot_fill_bound_v1(sparse.capacity,sparse.length); assert(w>0);
    assert(rt_dict_snapshot_fill_v1(d,&sparse,&a,w-1)<0 && !a.consumed);
    assert(((SnapshotArrayHeader*)(uintptr_t)(a.array&~INT64_C(7)))->len==0);
    RtArraySnapshotV1 copied_nonzero=a;
    assert(fill(d,&sparse,&a)==0 && a.consumed);
    assert(rt_array_snapshot_dispose_v1(&copied_nonzero,rt_dict_snapshot_fill_bound_v1(0,0))<0);
    SnapshotArrayHeader* actual=(SnapshotArrayHeader*)(uintptr_t)(a.array&~INT64_C(7));
    assert(actual->len==1 && ((int64_t*)actual->data)[0]==rt_value_int(163));
    RtDictSnapshotV1 before=observe(d); RtArraySnapshotV1 failed=output(1);
    assert(rt_dict_set(d,rt_value_int(63),rt_value_int(99)));
    assert(fill(d,&before,&failed)<0 && !failed.consumed);
    dispose(&failed);
    /* Deterministic corruption controls isolate every observation dimension;
     * restored before ordinary teardown. No forged address is dereferenced. */
    SnapshotDictHeader* header=(SnapshotDictHeader*)(uintptr_t)(d&~INT64_C(7));
    for(int field=0;field<5;++field) {
        RtDictSnapshotV1 s=observe(d); RtArraySnapshotV1 out=output(s.length);
        int64_t* slot=field==0 ? &header->owner : field==1 ? &header->backing :
            field==2 ? &header->cap : field==3 ? &header->tombs : &header->epoch;
        int64_t old=*slot; *slot=field==2 ? old*2 : old+1;
        assert(fill(d,&s,&out)<0 && !out.consumed);
        assert(((SnapshotArrayHeader*)(uintptr_t)(out.array&~INT64_C(7)))->len==0);
        *slot=old; dispose(&out);
    }
    /* Deterministic registration-growth boundary: retain real ordinary
     * dictionaries until the allocator owner observes a larger state fee.
     * Stale observed fields must refuse before publishing the next array. */
    int transition=0;
    int64_t old_fields=rt_array_snapshot_bound_v1(0,1); assert(old_fields>0);
    for(int i=0;i<512 && !transition;++i) {
        assert(rt_dict_new(0)>0);
        int64_t now=rt_array_snapshot_bound_v1(0,1); assert(now>0);
        if(now>old_fields) {
            RtArraySnapshotV1 rejected={0};
            int64_t current_work=rt_array_snapshot_bound_v1(0,0);
            int64_t current_bytes=rt_array_snapshot_bound_v1(0,2);
            assert(rt_array_snapshot_new_v1(0,current_work,now-1,current_bytes,&rejected)<0);
            assert(!rejected.array);
            assert(rt_array_snapshot_new_v1(0,current_work,old_fields,current_bytes,&rejected)<0);
            assert(!rejected.array);
            assert(rt_array_snapshot_new_v1(0,current_work,now,current_bytes,&rejected)==0);
            dispose(&rejected); transition=1;
        }
        old_fields=now;
    }
    assert(transition);
    /* Delete-heavy output lifecycle exercises scoped tombstone compaction
     * costs as well as growth. Every current state metric is checked one-short
     * before exact fees, independent of which resize policy is selected. */
    for(int cycle=0;cycle<3;++cycle) {
        RtArraySnapshotV1 churn[48];
        for(int i=0;i<48;++i) churn[i]=output(0);
        for(int i=0;i<48;++i) dispose(&churn[i]);
        int64_t cw=rt_array_snapshot_bound_v1(0,0),cf=rt_array_snapshot_bound_v1(0,1),cb=rt_array_snapshot_bound_v1(0,2);
        RtArraySnapshotV1 next={0};
        assert(rt_array_snapshot_new_v1(0,cw,cf-1,cb,&next)<0 && !next.array);
        assert(rt_array_snapshot_new_v1(0,cw,cf,cb-1,&next)<0 && !next.array);
        assert(rt_array_snapshot_new_v1(0,cw,cf,cb,&next)==0);
        dispose(&next);
    }
    header->flags|=0x80;
    q=rt_dict_snapshot_observation_bound_v1();
    assert(rt_dict_snapshot_observe_v1(d,q,&untouched)<0);
    header->flags&=(uint8_t)~0x80;
    assert(rt_transient_array_scope_end());
    puts("bounded ordinary dictionary snapshot: PASS (compiler owner/typed ABI UNRUN)");
    return 0;
}
