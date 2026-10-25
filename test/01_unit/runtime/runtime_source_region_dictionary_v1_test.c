/* NEW dictionary dependency fixture, not the exhausted general primitive test.
 * Actual native owners are exercised; shared Simple account/final HIR admission
 * remain separate gates. Bound observations carry their explicit allowance. */
#include <assert.h>
#include <stdio.h>
#include "../../../src/runtime/runtime_memory.c"

extern int64_t rt_source_region_dict_observation_bound_v1(void);
extern int64_t rt_source_region_dict_new_v1(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_source_region_dict_put_v1(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_source_region_dict_remove_v1(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int64_t rt_source_region_dict_get_v1(int64_t,int64_t,int64_t,int64_t,int64_t,int64_t);
extern int8_t rt_transient_array_scope_begin(void);
extern int8_t rt_transient_array_scope_end(void);
extern int8_t rt_dict_set(int64_t,int64_t,int64_t);

static const uint64_t child_rows[]={0,8,1,0};
static const uint64_t child_desc[]={1,1,8,1,(uintptr_t)child_rows,1};
static const uint64_t dict_rows[]={0,8,1,0,8,8,2,1};
static const uint64_t dict_desc[]={1,4,64,2,(uintptr_t)dict_rows,1};
static const uint64_t tagged_rows[]={0,8,1,0,8,8,2,2};
static const uint64_t tagged_desc[]={1,4,64,2,(uintptr_t)tagged_rows,1};

static int64_t fixed_work(int operation) {
    int64_t result=rt_source_region_bound_v1(operation,0,0,0);
    assert(result>0); return result;
}
static int64_t epoch(int64_t c,int64_t g) {
    int64_t result=rt_source_region_stamp_v1(c,g,fixed_work(4));
    assert(result>0); return result;
}
static int64_t dict_work(int operation,int64_t operand) {
    int64_t allowance=operation==13 ? 0 : rt_source_region_dict_observation_bound_v1();
    assert(operation==13 || allowance>0);
    /* A real compiler facade reserves three observation allowances on its
     * actual shared account before these native metric requests. */
    for(int metric=1;metric<3;++metric)
        assert(rt_source_region_bound_v1(operation,operand,allowance,metric)>=0);
    int64_t result=rt_source_region_bound_v1(operation,operand,allowance,0);
    assert(result>0); return result;
}
static int64_t born_region(int64_t* g) {
    int64_t c=rt_source_region_create_v1(fixed_work(1)); assert(c>0);
    *g=rt_source_region_created_generation_v1(c); assert(*g>0); return c;
}
static int64_t born_child(int64_t c,int64_t g) {
    int64_t w=rt_source_region_bound_v1(12,(int64_t)(uintptr_t)child_desc,1,0);
    int64_t prep=rt_source_region_allocation_prepare_v1((int64_t)(uintptr_t)child_desc,1,w);
    assert(prep>0);
    w=rt_source_region_bound_v1(2,(int64_t)(uintptr_t)child_desc,1,0);
    int64_t child=rt_source_region_alloc_v1(c,g,epoch(c,g),(int64_t)(uintptr_t)child_desc,1,prep,w);
    assert(child>0); return child;
}
static int64_t get(int64_t c,int64_t g,int64_t d,int64_t k) {
    return rt_source_region_dict_get_v1(c,g,epoch(c,g),d,k,dict_work(16,d));
}
static int64_t put(int64_t c,int64_t g,int64_t d,int64_t k,int64_t v) {
    return rt_source_region_dict_put_v1(c,g,epoch(c,g),d,k,v,dict_work(14,d));
}

int main(void) {
    assert(rt_transient_array_scope_begin());
    int64_t g,c=born_region(&g);
    int64_t child=born_child(c,g);
    int64_t new_work=dict_work(13,(int64_t)(uintptr_t)dict_desc);
    uint64_t members_before=sr_control(c)->members;
    assert(rt_source_region_dict_new_v1(c,g,epoch(c,g),(int64_t)(uintptr_t)dict_desc,0,new_work-1)==SR_CAPACITY);
    assert(sr_control(c)->members==members_before);
    int64_t d=rt_source_region_dict_new_v1(c,g,epoch(c,g),(int64_t)(uintptr_t)dict_desc,0,new_work);
    assert(d>0 && (d&7)==1);
    assert(put(c,g,d,INT64_MAX,child)==1);
    int64_t alias=get(c,g,d,INT64_MAX); assert(alias==child);
    assert(get(c,g,d,INT64_MIN)==0);
    int64_t saved=epoch(c,g);
    assert(rt_source_region_alias_write_v1(c,g,alias,0,7,fixed_work(9))==saved+1);
    assert(rt_source_region_dict_get_v1(c,g,saved,d,INT64_MAX,dict_work(16,d))==SR_STALE);
    assert(rt_source_region_dict_put_v1(c,g,saved,d,INT64_MAX,child,dict_work(14,d))==SR_STALE);
    int64_t current=epoch(c,g);
    assert(put(c,g,d,INT64_MAX,child)==1);
    assert(epoch(c,g)==current+1); /* same-value store is observable */
    current=epoch(c,g);
    assert(rt_source_region_dict_remove_v1(c,g,current,d,INT64_MAX,dict_work(15,d))==1);
    assert(get(c,g,d,INT64_MAX)==0);
    current=epoch(c,g);
    assert(rt_source_region_dict_remove_v1(c,g,current,d,INT64_MAX,dict_work(15,d))==0);
    assert(epoch(c,g)==current);
    assert(put(c,g,d,INT64_MIN,child)==1);
    assert(get(c,g,d,INT64_MIN)==child);

    int64_t foreign_g,foreign_c=born_region(&foreign_g);
    int64_t foreign=born_child(foreign_c,foreign_g);
    uint8_t* preexisting=rt_struct_alloc(8); assert(preexisting);
    current=epoch(c,g);
    assert(put(c,g,d,4,foreign)==SR_FOREIGN);
    assert(put(c,g,d,4,(int64_t)(uintptr_t)preexisting)==SR_FOREIGN);
    assert(put(c,g,d,4,0)==SR_FOREIGN);
    assert(get(c,g,d,4)==0 && epoch(c,g)==current);
    int64_t allowance=rt_source_region_dict_observation_bound_v1(); assert(allowance>0);
    assert(rt_source_region_bound_v1(14,d,allowance-1,0)==SR_CAPACITY);
    int64_t short_work=dict_work(14,d);
    assert(rt_source_region_dict_put_v1(c,g,current,d,4,child,short_work-1)==SR_CAPACITY);
    assert(get(c,g,d,4)==0 && epoch(c,g)==current);
    /* An unclassified ordinary alias path cannot mutate SOURCE storage. */
    assert(!rt_dict_set(d,4,child));
    assert(get(c,g,d,4)==0 && epoch(c,g)==current);
    for(int64_t k=0;k<22;++k) assert(put(c,g,d,k,child)==1);
    assert(get(c,g,d,INT64_MIN)==child); /* actual backing rehash retained owner */
    assert(get(c,g,d,21)==child);

    int64_t tagged=rt_source_region_dict_new_v1(c,g,epoch(c,g),(int64_t)(uintptr_t)tagged_desc,0,
        dict_work(13,(int64_t)(uintptr_t)tagged_desc));
    assert(tagged>0);
    assert(put(c,g,tagged,-7,child|1)==1);
    assert(get(c,g,tagged,-7)==(child|1));
    current=epoch(c,g);
    assert(put(c,g,tagged,-7,child|2)==SR_FOREIGN);
    assert(epoch(c,g)==current);

    /* Actual native scope retirement owns dictionaries/backings and children;
     * private retained controls survive until all member counts reach zero. */
    assert(rt_source_region_revoke_live_v1(c,g,16)==0);
    assert(rt_source_region_revoke_live_v1(foreign_c,foreign_g,16)==0);
    assert(rt_transient_array_scope_end());
    assert(sr_control(c)->members==0 && sr_control(foreign_c)->members==0);
    assert(rt_source_region_release_live_v1(c,g,64)==0);
    assert(rt_source_region_release_live_v1(foreign_c,foreign_g,64)==0);
    puts("C4 typed i64/Struct dictionary dependency: PASS (full HIR/SOURCE UNRUN)");
    return 0;
}
