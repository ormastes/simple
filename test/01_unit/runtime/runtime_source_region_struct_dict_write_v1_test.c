/* Authored UNRUN during Phase3. Actual native owner fixture, not SOURCE admission. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int64_t rt_dict_new(int64_t);
typedef struct BridgeDictHeaderV1 {
    uint8_t kind,flags; uint16_t reserved; uint32_t scope;
    int64_t capacity,length,tombstones; void* entries;
    int64_t reader,epoch,backing;
} BridgeDictHeaderV1;
static const uint64_t scalar_rows[]={0,8,1,0};
static const uint64_t scalar_desc[]={1,1,8,1,(uintptr_t)scalar_rows,1};
static const uint64_t root_rows[]={0,8,2,4};
static const uint64_t root_desc[]={1,1,8,1,(uintptr_t)root_rows,1};
static const uint64_t dict_rows[]={0,8,1,0,8,8,2,1};
static const uint64_t dict_desc[]={1,4,64,2,(uintptr_t)dict_rows,1};
static const uint64_t tagged_rows[]={0,8,1,0,8,8,2,2};
static const uint64_t tagged_desc[]={1,4,64,2,(uintptr_t)tagged_rows,1};
static int64_t fixed(int op) {
    int64_t w=rt_source_region_bound_v1(op,0,0,0); assert(w>0); return w;
}
static int64_t stamp(int64_t c,int64_t g) {
    int64_t e=rt_source_region_stamp_v1(c,g,fixed(4)); assert(e>0); return e;
}
static int64_t work(int op,int64_t d) {
    int64_t allowance=op==13 ? 0 : rt_source_region_dict_observation_bound_v1();
    assert(op==13 || allowance>0);
    int64_t fields=rt_source_region_bound_v1(op,d,allowance,1);
    int64_t bytes=rt_source_region_bound_v1(op,d,allowance,2);
    assert(fields>=0 && bytes>=0);
    if(op==17) assert(fields==0 && bytes==0);
    int64_t result=rt_source_region_bound_v1(op,d,allowance,0); assert(result>0); return result;
}
static int64_t region(int64_t* g) {
    int64_t c=rt_source_region_create_v1(fixed(1)); assert(c>0);
    *g=rt_source_region_created_generation_v1(c); assert(*g>0); return c;
}
static int64_t object(int64_t c,int64_t g,const uint64_t* descriptor) {
    int64_t p=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)descriptor,1,
        rt_source_region_bound_v1(12,(int64_t)(uintptr_t)descriptor,1,0)); assert(p>0);
    int64_t result=rt_source_region_alloc_v1(c,g,stamp(c,g),(int64_t)(uintptr_t)descriptor,1,p,
        rt_source_region_bound_v1(2,(int64_t)(uintptr_t)descriptor,1,0)); assert(result>0); return result;
}
static int64_t dictionary(int64_t c,int64_t g,const uint64_t* descriptor) {
    int64_t result=rt_source_region_dict_new_v1(c,g,stamp(c,g),(int64_t)(uintptr_t)descriptor,0,
        work(13,(int64_t)(uintptr_t)descriptor)); assert(result>0); return result;
}
static int64_t field(int64_t root) { int64_t d; memcpy(&d,(void*)(uintptr_t)root,8); return d; }
int main(void) {
    _Static_assert(sizeof(BridgeDictHeaderV1)==64,"ordinary dictionary header unchanged");
    assert(rt_transient_array_scope_begin());
    int64_t g,c=region(&g), fg,fc=region(&fg);
    int64_t root=object(c,g,root_desc), child=object(c,g,scalar_desc);
    int64_t d=dictionary(c,g,dict_desc), replacement=dictionary(c,g,tagged_desc);
    assert(rt_source_region_dict_put_v1(c,g,stamp(c,g),d,INT64_MIN,child,work(14,d))==1);
    int64_t w=work(17,d), before=stamp(c,g);
    uint64_t members=sr_control(c)->members, records=rt_struct_alloc_len;
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,w-1)==SR_CAPACITY);
    assert(field(root)==0 && stamp(c,g)==before && sr_control(c)->members==members);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,w)==before+1);
    assert(field(root)==d && rt_struct_alloc_len==records && sr_control(c)->members==members);
    int64_t saved=stamp(c,g), lease=rt_source_region_read_begin_v1(c,g,saved,fixed(5)); assert(lease>0);
    int64_t alias=rt_source_region_dict_get_v1(c,g,saved,field(root),INT64_MIN,work(16,d)); assert(alias==child);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,work(17,d))==SR_CONFLICT);
    assert(rt_source_region_read_end_v1(c,g,lease,fixed(6))==0);
    assert(rt_source_region_alias_write_v1(c,g,alias,0,2,fixed(9))>saved);
    assert(rt_source_region_dict_get_v1(c,g,saved,field(root),INT64_MIN,work(16,d))==SR_STALE);
    before=stamp(c,g);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,work(17,d))==before+1); /* same value */
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,replacement,work(17,replacement))>0);
    assert(field(root)==replacement);
    assert(rt_source_region_dict_put_v1(c,g,stamp(c,g),replacement,INT64_MAX,child|1,work(14,replacement))==1);
    assert(rt_source_region_dict_get_v1(c,g,stamp(c,g),replacement,INT64_MAX,work(16,replacement))==(child|1));
    for(int64_t i=0;i<40;++i) assert(rt_source_region_dict_put_v1(c,g,stamp(c,g),d,i,child,work(14,d))==1);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,work(17,d))>0); /* current rehashed backing */
    BridgeDictHeaderV1* header=(BridgeDictHeaderV1*)(uintptr_t)(d&~INT64_C(7));
    int64_t capacity=header->capacity; void* entries=header->entries; before=stamp(c,g);
    header->capacity*=2;
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,INT64_MAX)==SR_INCOMPLETE);
    header->capacity=capacity; header->entries=(void*)(uintptr_t)1;
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,INT64_MAX)==SR_INCOMPLETE);
    header->entries=entries; assert(stamp(c,g)==before && field(root)==d);
    int64_t foreign=dictionary(fc,fg,dict_desc), ordinary=rt_dict_new(0);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,foreign,work(17,foreign))==SR_FOREIGN);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,ordinary,INT64_MAX)==SR_INCOMPLETE);
    assert(rt_source_region_struct_dict_write_v1(c,g+1,root,0,d,work(17,d))==SR_FOREIGN);
    assert(rt_source_region_struct_dict_write_v1(c,g,child,0,d,work(17,d))==SR_INCOMPLETE);
    assert(rt_source_region_struct_dict_write_v1(c,g,root,1,d,work(17,d))==SR_INCOMPLETE);
    assert(rt_source_region_write_begin_v1(c,g,before,root,0,fixed(7))==SR_INCOMPLETE);
    assert(rt_source_region_alias_write_v1(c,g,root,0,d,fixed(9))==SR_INCOMPLETE);
    assert(stamp(c,g)==before && field(root)==d);
    w=work(17,d);
    assert(rt_source_region_revoke_live_v1(c,g,16)==0);
    assert(rt_source_region_revoke_live_v1(fc,fg,16)==0);
    assert(rt_transient_array_scope_end());
    assert(rt_source_region_struct_dict_write_v1(c,g,root,0,d,w)<0); /* no stale prefix/header dereference */
    assert(sr_control(c)->members==0 && sr_control(fc)->members==0);
    assert(rt_source_region_release_live_v1(c,g,64)==0);
    assert(rt_source_region_release_live_v1(fc,fg,64)==0);
    puts("op17 native fixture PASS; compiler/HIR/SOURCE admission remains separate");
    return 0;
}
