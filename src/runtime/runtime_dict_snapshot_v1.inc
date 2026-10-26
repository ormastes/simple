/* Ordinary dictionary snapshot; actual compiler confinement is a SEPARATE
 * prerequisite. Locks protect lifecycle/registry, not ordinary alias writes. */
#include "runtime_dict_snapshot_v1.h"
#define DS_INVALID (-1)
#define DS_CAPACITY (-4)
#define DS_STALE (-3)
/* Private unpublished array state, removed before user publication. */
#define DS_ARRAY_UNPUBLISHED UINT8_C(0x40)
static int ds_lock(void) {
    if (atomic_flag_test_and_set_explicit(&rt_core_heap_lifecycle_lock,memory_order_acquire)) return 0;
    if (atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock,memory_order_acquire)) {
        rt_core_heap_lifecycle_release(); return 0;
    }
    return 1;
}
static void ds_unlock(void) {
    rt_core_immortal_registry_release(); rt_core_heap_lifecycle_release();
}
static int ds_add(uint64_t* value,uint64_t add) {
    if (add>(uint64_t)INT64_MAX-*value) return 0;
    *value+=add; return 1;
}
static int ds_product(uint64_t a,uint64_t b,uint64_t* out) {
    if (b && a>(uint64_t)INT64_MAX/b) return 0;
    *out=a*b; return 1;
}
static int64_t ds_qualification_locked(void) {
    uint64_t n;
    if (!ds_product(rt_core_immortal_registry_cap,16,&n) || !ds_add(&n,256)) return DS_CAPACITY;
    return (int64_t)n;
}
int64_t rt_dict_snapshot_observation_bound_v1(void) {
    if (!ds_lock()) return DS_INVALID;
    int64_t result=ds_qualification_locked(); ds_unlock(); return result;
}
/* Only after current Q has been prepaid. No header access before membership. */
static void* ds_heap_locked(int64_t value,uint8_t kind) {
    uintptr_t bits=(uintptr_t)value;
    if (bits<4096 || (bits&RT_VALUE_TAG_MASK)!=RT_VALUE_TAG_HEAP) return NULL;
    void* ptr=(void*)(bits&~RT_VALUE_TAG_MASK);
    if (!core_scoped_registered_locked(ptr)) return NULL;
    return *(uint8_t*)ptr==kind ? ptr : NULL;
}
static int ds_record_locked(int64_t dictionary,RtDictSnapshotV1* out) {
    RtCoreDict* d=(RtCoreDict*)ds_heap_locked(dictionary,RT_VALUE_HEAP_DICT);
    if (!d || (d->flags&RT_CORE_DICT_SOURCE_REGION_V1) || d->read_owner<=0 ||
        d->read_epoch<=0 || d->read_backing<=0 || !d->entries || d->cap<8 ||
        (d->cap&(d->cap-1)) || d->len<0 || d->len>d->cap || d->tombstones<0 ||
        d->tombstones>d->cap-d->len || (uint64_t)d->cap>INT64_MAX/sizeof(RtCoreDictEntry)) return 0;
    *out=(RtDictSnapshotV1){dictionary,d->read_owner,d->read_epoch,d->read_backing,
        d->cap,d->len,d->tombstones,(uintptr_t)d->entries};
    return 1;
}
int64_t rt_dict_snapshot_observe_v1(int64_t dictionary,int64_t work,RtDictSnapshotV1* out) {
    if (!out || !ds_lock()) return DS_INVALID;
    int64_t bound=ds_qualification_locked(), result=DS_CAPACITY;
    RtDictSnapshotV1 value;
    if (bound>=0 && work>=bound) result=ds_record_locked(dictionary,&value) ? 0 : DS_INVALID;
    if (!result) *out=value;
    ds_unlock(); return result;
}
/* Canonical owner allocation costs. All arithmetic precedes allocation or
 * registry/scoped lookup. Existing registration malloc-under-lock semantics
 * are retained: logical accounting is not a wall-clock or RSS guarantee. */
static int64_t ds_array_cost_locked(int64_t length,int64_t metric) {
    if (length<0 || length>RT_CORE_ARRAY_MAX_CAP || metric<0 || metric>2) return DS_INVALID;
    uint64_t cap=length>4 ? (uint64_t)length : 4, work=512,fields=128,bytes=sizeof(RtCoreArray),n;
    if (!ds_product(cap,8,&n) || !ds_add(&bytes,n) || !ds_add(&fields,cap) || !ds_add(&work,cap)) return DS_CAPACITY;
    uint64_t r=rt_core_immortal_registry_cap, next=r;
    /* Overflow-safe equivalent of canonical occupancy thresholds. */
    if (r>INT64_MAX/10 || rt_core_immortal_registry_len>INT64_MAX/10 || rt_core_immortal_registry_tombs>INT64_MAX/10 ||
        rt_core_immortal_registry_len>(uint64_t)INT64_MAX-rt_core_immortal_registry_tombs-1) return DS_CAPACITY;
    if ((rt_core_immortal_registry_len+rt_core_immortal_registry_tombs+1)*10>=r*7) {
        next=r ? r*2 : 256;
        if (r && rt_core_immortal_registry_tombs>rt_core_immortal_registry_len &&
            (rt_core_immortal_registry_len+1)*10<r*5) next=r;
        if (!ds_product(next,8,&n) || !ds_add(&bytes,n) || !ds_add(&fields,next) || !ds_add(&fields,r) ||
            !ds_product(r,next,&n) || !ds_product(n,16,&n) || !ds_add(&work,n) || !ds_add(&work,r)) return DS_CAPACITY;
    }
    /* Retained insert/rollback/counter writes are separate from fresh-table
     * zeroing and old-table rehash writes. */
    if (!ds_add(&fields,16)) return DS_CAPACITY;
    if (!ds_product(next+1,32,&n) || !ds_add(&work,n)) return DS_CAPACITY;
    uint32_t owner=rt_core_transient_scope_for_new_object();
    if (owner) {
        uint64_t s=rt_core_scoped_cap;
        if (s>INT64_MAX/10 || rt_core_scoped_len>INT64_MAX/10 || rt_core_scoped_tombs>INT64_MAX/10 ||
            rt_core_scoped_len>(uint64_t)INT64_MAX-rt_core_scoped_tombs-1) return DS_CAPACITY;
        uint64_t sn=core_scoped_next_capacity_locked();
        if (sn) {
            if (sn<s || !ds_product(sn,sizeof(RtCoreScopedAllocationKey),&n) || !ds_add(&bytes,n) ||
                !ds_product(sn,3,&n) || !ds_add(&fields,n) ||
                !ds_product(s,3,&n) || !ds_add(&fields,n) || !ds_product(s,sn,&n) ||
                !ds_product(n,32,&n) || !ds_add(&work,n) || !ds_add(&work,s)) return DS_CAPACITY;
        }
        if (!ds_add(&fields,32)) return DS_CAPACITY;
        if (!ds_product(s+(sn ? sn : s)+1,64,&n) || !ds_add(&work,n)) return DS_CAPACITY;
        uint64_t used=owner==rt_core_session_heap_live_id ? rt_core_session_heap_object_len : rt_core_transient_heap_scope_object_len;
        uint64_t slots=owner==rt_core_session_heap_live_id ? rt_core_session_heap_object_cap : rt_core_transient_heap_scope_object_cap;
        if (used>slots || used>=RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS || !rt_core_scoped_next_birth) return DS_CAPACITY;
        if (used==slots) {
            uint64_t fresh=slots ? slots*2 : 64;
            if (fresh>RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS || !ds_product(fresh,sizeof(RtCoreScopedAllocationKey),&n) ||
                !ds_add(&bytes,n) || !ds_product(fresh,3,&n) || !ds_add(&fields,n) ||
                !ds_product(used,3,&n) || !ds_add(&fields,n) ||
                !ds_product(slots,8,&n) || !ds_add(&work,n)) return DS_CAPACITY;
        }
    }
    if (!ds_add(&work,fields) || !ds_add(&work,bytes)) return DS_CAPACITY;
    return (int64_t)(metric==0 ? work : metric==1 ? fields : bytes);
}
int64_t rt_array_snapshot_bound_v1(int64_t length,int64_t metric) {
    if (!ds_lock()) return DS_INVALID;
    int64_t result=ds_array_cost_locked(length,metric); ds_unlock(); return result;
}
int64_t rt_array_snapshot_new_v1(int64_t length,int64_t work,int64_t fields,int64_t bytes,
    RtArraySnapshotV1* output) {
    if (!output || !ds_lock()) return DS_INVALID;
    int64_t w=ds_array_cost_locked(length,0),f=ds_array_cost_locked(length,1),b=ds_array_cost_locked(length,2);
    uint32_t owner=rt_core_transient_scope_for_new_object();
    if (w<0 || f<0 || b<0 || work<w || fields<f || bytes<b || !owner) {
        ds_unlock(); return DS_CAPACITY;
    }
    /* Same canonical header/data allocator and registration owners. No
     * blocking reacquisition: all registration helpers below are lock-aware. */
    RtCoreArray* a=(RtCoreArray*)rt_observed_calloc_v1(1,sizeof(*a));
    int64_t capacity=length>4 ? length : 4;
    if (a) a->data=rt_observed_calloc_v1((size_t)capacity,sizeof(int64_t));
    RtCoreScopedAllocationKey key={0};
    int tracked=0,session=owner==rt_core_session_heap_live_id;
    if (a && a->data) {
        a->kind=RT_VALUE_HEAP_ARRAY; a->flags=DS_ARRAY_UNPUBLISHED; a->cap=capacity; a->transient_scope_id=owner;
        if (session) {
            tracked=core_session_reserve(1) && core_scoped_insert_locked(a,owner,&key);
            if (tracked) rt_core_session_heap_objects[rt_core_session_heap_object_len++]=key;
        } else tracked=rt_core_track_module_immortal_locked(a,&key);
    }
    int ok=tracked && rt_core_register_immortal_ptr_locked_v1(a);
    if (!ok && tracked) {
        core_scoped_remove_locked(a);
        if (session) --rt_core_session_heap_object_len;
        else --rt_core_transient_heap_scope_object_len;
    }
    if (ok) *output=(RtArraySnapshotV1){(int64_t)((uintptr_t)a|RT_VALUE_TAG_HEAP),capacity,
        (uintptr_t)a->data,key.birth,key.owner,0};
    ds_unlock();
    if (!ok) { if(a) free(a->data); free(a); return DS_CAPACITY; }
    return 0;
}
/* Actual scoped birth witnesses fresh output even if its address is reused.
 * Only this C owner initializes output; no safe caller-authored DTO API. */
static RtCoreArray* ds_output_locked(RtArraySnapshotV1* output) {
    if (!output || output->consumed || !output->birth || !output->owner) return NULL;
    RtCoreArray* a=(RtCoreArray*)ds_heap_locked(output->array,RT_VALUE_HEAP_ARRAY);
    if (!a) return NULL;
    RtCoreScopedAllocationKey* key=core_scoped_find_locked(a);
    if (!key || key->birth!=output->birth || key->owner!=output->owner ||
        a->transient_scope_id!=output->owner || a->flags!=DS_ARRAY_UNPUBLISHED || a->len ||
        a->cap!=output->capacity || (uintptr_t)a->data!=output->data || !a->data) return NULL;
    return a;
}
static int64_t ds_fill_work_locked(int64_t capacity,int64_t length) {
    if (capacity<0 || length<0) return DS_INVALID;
    int64_t q=ds_qualification_locked(); uint64_t result=q>0 ? (uint64_t)q : 0,n;
    if (q<0 || !ds_product((uint64_t)q,2,&result) ||
        !ds_product(rt_core_scoped_cap,32,&n) || !ds_add(&result,n) ||
        !ds_product((uint64_t)capacity,16,&n) || !ds_add(&result,n) ||
        !ds_product((uint64_t)length,8,&n) || !ds_add(&result,n) || !ds_add(&result,256)) return DS_CAPACITY;
    return (int64_t)result;
}
int64_t rt_dict_snapshot_fill_v1(int64_t dictionary,const RtDictSnapshotV1* expected,
    RtArraySnapshotV1* output,int64_t work) {
    if (!expected || expected->dictionary!=dictionary || !ds_lock()) return DS_INVALID;
    int64_t bound=ds_fill_work_locked(expected->capacity,expected->length);
    if (bound<0 || work<bound) { ds_unlock(); return DS_CAPACITY; }
    RtDictSnapshotV1 actual;
    if (!ds_record_locked(dictionary,&actual)) { ds_unlock(); return DS_INVALID; }
    if (actual.owner!=expected->owner || actual.epoch!=expected->epoch || actual.backing!=expected->backing ||
        actual.entries!=expected->entries || actual.capacity!=expected->capacity ||
        actual.length!=expected->length || actual.tombstones!=expected->tombstones) {
        ds_unlock(); return DS_STALE;
    }
    RtCoreArray* array=ds_output_locked(output);
    if (!array || array->cap<actual.length || (uintptr_t)array==(uintptr_t)(dictionary&~INT64_C(7)) ||
        (uintptr_t)array->data==actual.entries || (uintptr_t)array==actual.entries ||
        (uintptr_t)array->data==(uintptr_t)(dictionary&~INT64_C(7))) { ds_unlock(); return DS_INVALID; }
    RtCoreDictEntry* rows=(RtCoreDictEntry*)actual.entries;
    int64_t count=0;
    for(int64_t i=0;i<actual.capacity;++i) if(rows[i].occupied==1) {
        if(count>=actual.length) { ds_unlock(); return DS_INVALID; }
        ((int64_t*)array->data)[count++]=rows[i].value;
    }
    if(count!=actual.length) { ds_unlock(); return DS_INVALID; }
    array->len=count; array->flags=0; output->consumed=1;
    ds_unlock(); return 0;
}
int64_t rt_array_snapshot_dispose_v1(RtArraySnapshotV1* output,int64_t work) {
    if (!ds_lock()) return DS_INVALID;
    int64_t bound=ds_fill_work_locked(0,0);
    if (bound<0 || work<bound) { ds_unlock(); return DS_CAPACITY; }
    RtCoreArray* array=ds_output_locked(output);
    if (!array) { ds_unlock(); return DS_INVALID; }
    void* data=array->data;
    if (!rt_core_immortal_registry_erase_raw((uintptr_t)array)) { ds_unlock(); return DS_INVALID; }
    atomic_fetch_sub_explicit(&rt_core_heap_registry_count,1,memory_order_relaxed);
    output->consumed=1; ds_unlock(); free(data); free(array); return 0;
}
/* Output registry/scoped growth is included at USE TIME, not inferred from
 * dictionary len. Reserve this after output creation, before fill/disposal. */
int64_t rt_dict_snapshot_fill_bound_v1(int64_t capacity,int64_t length) {
    if (!ds_lock()) return DS_INVALID;
    int64_t result=ds_fill_work_locked(capacity,length); ds_unlock(); return result;
}
