/* Typed SOURCE dictionary owner. Included beside the actual RtCoreDict owner;
 * no parallel registry, graph adoption, or ordinary dictionary layout change. */
#include <stddef.h>
#define SD_INCOMPLETE (-1)
#define SD_FOREIGN (-2)
#define SD_STALE (-3)
#define SD_CAPACITY (-4)

static RtCoreSourceDictBackingV1* sd_backing(RtCoreDict* d) {
    return (RtCoreSourceDictBackingV1*)((uint8_t*)d->entries-
        offsetof(RtCoreSourceDictBackingV1,entries));
}

static int sd_try_lock(void) {
    return !atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock,memory_order_acquire);
}

static int sd_add(uint64_t* total,uint64_t n) {
    if (n>(uint64_t)INT64_MAX-*total) return 0;
    *total+=n; return 1;
}
static int sd_mul(uint64_t a,uint64_t b,uint64_t* out) {
    if (b && a>(uint64_t)INT64_MAX/b) return 0;
    *out=a*b; return 1;
}

static int64_t sd_observation_locked(void) {
    if (rt_core_immortal_max_success_probe_v1>((uint64_t)INT64_MAX-64)/4)
        return SD_CAPACITY;
    return (int64_t)(rt_core_immortal_max_success_probe_v1*4+64);
}

int64_t rt_source_region_dict_observation_bound_v1(void) {
    if (!sd_try_lock()) return SD_INCOMPLETE;
    int64_t result=sd_observation_locked();
    rt_core_immortal_registry_release(); return result;
}

/* Only call after reserving/revalidating observation work. */
static RtCoreDict* sd_find_locked(int64_t value,int64_t allowance,int64_t* error,
    RtCoreSourceDictRegistrationV1** registration) {
    int64_t required=sd_observation_locked();
    if (required<0 || allowance<required) { *error=SD_CAPACITY; return NULL; }
    uintptr_t raw=(uintptr_t)value;
    if (raw<4096 || (raw&RT_VALUE_TAG_MASK)!=RT_VALUE_TAG_HEAP) {
        *error=SD_INCOMPLETE; return NULL;
    }
    uintptr_t ptr=raw&~RT_VALUE_TAG_MASK;
    int found=0;
    RtCoreSourceDictRegistrationV1* owner=NULL;
    if (rt_core_immortal_registry_cap) {
        size_t slot=rt_core_immortal_hash_ptr(ptr)&(rt_core_immortal_registry_cap-1);
        for(size_t probes=0;probes<rt_core_immortal_max_success_probe_v1;++probes) {
            uintptr_t entry=rt_core_immortal_registry[slot];
            if (!entry) break;
            if (rt_core_immortal_entry_pointer_v1(entry)==ptr) {
                found=1; owner=rt_core_source_dict_registration_v1(entry); break;
            }
            slot=(slot+1)&(rt_core_immortal_registry_cap-1);
        }
    }
    if (!found || !owner || owner->dictionary!=(RtCoreDict*)ptr || !owner->backing) {
        *error=SD_INCOMPLETE; return NULL;
    }
    RtCoreDict* d=(RtCoreDict*)ptr;
    if (d->kind!=RT_VALUE_HEAP_DICT || !(d->flags&RT_CORE_DICT_SOURCE_REGION_V1) ||
        d->cap!=owner->capacity ||
        !d->entries || d->cap<8 || (d->cap&(d->cap-1)) ||
        d->len<0 || d->tombstones<0 || d->len>d->cap || d->tombstones>d->cap-d->len ||
        (uint64_t)d->cap>((uint64_t)INT64_MAX-sizeof(RtCoreSourceDictBackingV1))/sizeof(RtCoreDictEntry)) {
        *error=SD_INCOMPLETE; return NULL;
    }
    RtCoreSourceDictBackingV1* b=owner->backing;
    if (d->entries!=b->entries) { *error=SD_INCOMPLETE; return NULL; }
    if (b->abi!=1 || b->dictionary!=ptr || b->control<=0 || b->generation<=0) {
        *error=SD_INCOMPLETE; return NULL;
    }
    if (registration) *registration=owner;
    return d;
}

static int sd_descriptor_header(const uint64_t* d) {
    return sizeof(RtCoreDict)==64 && sizeof(RtCoreDictEntry)==32 &&
        offsetof(RtCoreDictEntry,key)==0 && offsetof(RtCoreDictEntry,value)==8 &&
        d && d[0]==1 && d[1]==4 && d[2]==64 && d[3]==2 && d[4] && d[5]==1;
}
static int sd_descriptor(const uint64_t* d) {
    if (!sd_descriptor_header(d)) return 0;
    const uint64_t* r=(const uint64_t*)(uintptr_t)d[4];
    return r[0]==0 && r[1]==8 && r[2]==1 && r[3]==0 &&
        r[4]==8 && r[5]==8 && r[6]==2 && (r[7]==1 || r[7]==2);
}

static int64_t sd_growth_capacity(RtCoreDict* d) {
    if ((uint64_t)d->len+(uint64_t)d->tombstones+1<=(uint64_t)d->cap*7/10) return 0;
    if (d->cap>8 && d->tombstones>d->len &&
        (uint64_t)(d->len+1)<(uint64_t)d->cap/2) return d->cap;
    return d->cap>INT64_MAX/2 ? SD_CAPACITY : d->cap*2;
}

static int64_t sd_registry_next(void) {
    uint64_t cap=rt_core_immortal_registry_cap;
    if ((uint64_t)rt_core_immortal_registry_len+rt_core_immortal_registry_tombs+1<
        (cap*7+9)/10) return 0;
    if (cap && rt_core_immortal_registry_tombs>rt_core_immortal_registry_len &&
        (uint64_t)rt_core_immortal_registry_len+1<cap/2) return (int64_t)cap;
    if (cap>(uint64_t)INT64_MAX/2) return SD_CAPACITY;
    return cap ? (int64_t)(cap*2) : 256;
}

/* Return a complete native cost, excluding the separately revalidated region
 * critical-section bound. No lookup occurs here; d is already paid/validated. */
static int64_t sd_metrics_locked(int operation,const uint64_t* descriptor,
    RtCoreDict* d,int metric,uint64_t* native_work) {
    if (metric<0 || metric>2) return SD_INCOMPLETE;
    uint64_t work=1024,fields=0,bytes=0,n=0;
    if (operation==13) {
        if (!sd_descriptor_header(descriptor) || !rt_core_transient_array_scope_active ||
            rt_core_transient_array_scope_paused || !rt_transient_raw_owner_thread_allows())
            return SD_INCOMPLETE;
        fields=19+8*4;
        bytes=sizeof(RtCoreDict)+sizeof(RtCoreSourceDictRegistrationV1)+
            offsetof(RtCoreSourceDictBackingV1,entries)+8*sizeof(RtCoreDictEntry);
        int64_t next=sd_registry_next();
        if (next<0) return next;
        uint64_t insertion=next ? (uint64_t)next : rt_core_immortal_registry_cap;
        if (!sd_mul(insertion,4,&n) || !sd_add(&work,n)) return SD_CAPACITY;
        if (next) {
            if (!sd_mul((uint64_t)next,sizeof(uintptr_t),&n) || !sd_add(&bytes,n) ||
                !sd_add(&fields,(uint64_t)next) ||
                !sd_mul(rt_core_immortal_registry_cap,(uint64_t)next,&n) ||
                !sd_mul(n,4,&n) || !sd_add(&work,n) ||
                !sd_add(&work,rt_core_immortal_registry_cap)) return SD_CAPACITY;
        }
        if (rt_core_transient_heap_scope_object_len==rt_core_transient_heap_scope_object_cap) {
            uint64_t next_scope=rt_core_transient_heap_scope_object_cap ?
                rt_core_transient_heap_scope_object_cap*2 : 64;
            if (next_scope>RT_CORE_TRANSIENT_SCOPE_MAX_OBJECTS ||
                !sd_mul(next_scope,sizeof(RtCoreScopedAllocationKey),&n) || !sd_add(&bytes,n) ||
                !sd_mul(next_scope,3,&n) || !sd_add(&fields,n) ||
                !sd_mul(rt_core_transient_heap_scope_object_cap,3,&n) ||
                !sd_add(&work,n)) return SD_CAPACITY;
        }
        /* The MODULE ledger now stores ptr/birth/owner. Its scoped-only
         * registry index uses the existing lock, but still allocates, clears,
         * probes and rehashes real entries. Charge both success and exact-key
         * rollback (two lookups), rather than treating that index as free. */
        uint64_t old_scoped=rt_core_scoped_cap;
        uint64_t next_scoped=core_scoped_next_capacity_locked();
        if ((next_scoped && next_scoped<old_scoped) || next_scoped>INT64_MAX)
            return SD_CAPACITY;
        uint64_t scoped_capacity=next_scoped ? next_scoped : old_scoped;
        if (!sd_add(&fields,16) ||
            !sd_mul(scoped_capacity,3,&n) || !sd_add(&n,old_scoped) ||
            !sd_mul(n,8,&n) || !sd_add(&work,n)) return SD_CAPACITY;
        if (next_scoped) {
            if (!sd_mul(next_scoped,sizeof(RtCoreScopedAllocationKey),&n) ||
                !sd_add(&bytes,n) || !sd_mul(next_scoped,3,&n) ||
                !sd_add(&fields,n) || !sd_mul(old_scoped,3,&n) ||
                !sd_add(&fields,n) || !sd_mul(old_scoped,next_scoped,&n) ||
                !sd_mul(n,8,&n) || !sd_add(&work,n) ||
                !sd_add(&work,old_scoped)) return SD_CAPACITY;
        }
    } else {
        int64_t observation=sd_observation_locked();
        if (observation<0 || !sd_add(&work,(uint64_t)observation)) return SD_CAPACITY;
        int64_t next=operation==14 ? sd_growth_capacity(d) : 0;
        if (next<0) return next;
        uint64_t probes=next ? (uint64_t)next : (uint64_t)d->cap;
        if (!sd_mul(probes,8,&n) || !sd_add(&work,n)) return SD_CAPACITY;
        if (next) {
            if (!sd_mul((uint64_t)next,sizeof(RtCoreDictEntry),&n) ||
                !sd_add(&bytes,n) || !sd_add(&bytes,offsetof(RtCoreSourceDictBackingV1,entries)) ||
                !sd_mul((uint64_t)next,4,&n) || !sd_add(&fields,n) || !sd_add(&fields,5) ||
                !sd_mul((uint64_t)d->cap,(uint64_t)next,&n) || !sd_mul(n,8,&n) ||
                !sd_add(&work,n) || !sd_mul((uint64_t)d->cap,8,&n) || !sd_add(&work,n))
                return SD_CAPACITY;
        }
    }
    if (!sd_add(&work,fields) || !sd_add(&work,bytes)) return SD_CAPACITY;
    *native_work=work;
    return (int64_t)(metric==0 ? work : metric==1 ? fields : bytes);
}

int64_t rt_source_region_dict_bound_v1(int64_t operation,int64_t operand,
    int64_t observation,int64_t metric) {
#if !defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    (void)operation;(void)operand;(void)observation;(void)metric; return SD_INCOMPLETE;
#else
    if (operation<13 || operation>17 || metric<0 || metric>2 || !sd_try_lock()) return SD_INCOMPLETE;
    int64_t error=0;
    RtCoreDict* d=operation==13 ? NULL : sd_find_locked(operand,observation,&error,NULL);
    if (operation==17) {
        int64_t required=sd_observation_locked();
        uint64_t total=required>0 ? (uint64_t)required : 0;
        int64_t result=error ? error : required;
        if (!error && required>0 && !sd_descriptor(sd_backing(d)->descriptor)) result=SD_INCOMPLETE;
        else if (!error && required>0 && !sd_add(&total,256)) result=SD_CAPACITY;
        else if (!error && required>0) {
            int64_t region=rt_source_region_bound_v1(9,0,0,0);
            if (region<0) result=region;
            else if (!sd_add(&total,(uint64_t)region)) result=SD_CAPACITY;
            else result=metric==0 ? (int64_t)total : metric==1 || metric==2 ? 0 : SD_INCOMPLETE;
        }
        rt_core_immortal_registry_release(); return result;
    }
    uint64_t native_work=0;
    int64_t result=error ? error : sd_metrics_locked((int)operation,
        (const uint64_t*)(uintptr_t)operand,d,(int)metric,&native_work);
    if (result>=0 && metric==0) {
        int64_t region=rt_source_region_bound_v1(9,0,0,0);
        if (region<0) result=region;
        else if (!sd_add(&native_work,(uint64_t)region)) result=SD_CAPACITY;
        else if (operation==16) {
            int64_t projection=rt_source_region_native_projection_bound_v1();
            if (projection<0) result=projection;
            else if (!sd_add(&native_work,(uint64_t)projection)) result=SD_CAPACITY;
            else result=(int64_t)native_work;
        } else result=(int64_t)native_work;
    }
    rt_core_immortal_registry_release(); return result;
#endif
}

static uint64_t sd_hash(int64_t key) {
    uint64_t x=(uint64_t)key;
    x^=x>>33; x*=UINT64_C(0xff51afd7ed558ccd); x^=x>>33; return x;
}

static RtCoreSourceDictBackingV1* sd_allocate_backing(int64_t capacity,
    int64_t control,int64_t generation,const uint64_t* descriptor,RtCoreDict* d) {
    if (capacity<8 || (uint64_t)capacity>
        (SIZE_MAX-sizeof(RtCoreSourceDictBackingV1))/sizeof(RtCoreDictEntry)) return NULL;
    size_t bytes=offsetof(RtCoreSourceDictBackingV1,entries)+(size_t)capacity*sizeof(RtCoreDictEntry);
    RtCoreSourceDictBackingV1* b=(RtCoreSourceDictBackingV1*)rt_observed_calloc_v1(1,bytes);
    if (b) { b->control=control; b->generation=generation; b->descriptor=descriptor;
        b->dictionary=(uintptr_t)d; b->abi=1; }
    return b;
}

static int sd_insert(RtCoreDictEntry* entries,int64_t cap,int64_t key,int64_t value,uint64_t hash,
    int64_t* len,int64_t* tombstones) {
    int64_t slot=(int64_t)(hash&(uint64_t)(cap-1)),tomb=-1;
    for(int64_t probes=0;probes<cap;++probes) {
        RtCoreDictEntry* e=&entries[slot];
        if (!e->occupied) {
            if (tomb>=0) { e=&entries[tomb]; --*tombstones; }
            e->key=key; e->value=value; e->hash=hash; e->occupied=1; ++*len; return 1;
        }
        if (e->occupied==-1) { if(tomb<0) tomb=slot; }
        else if(e->hash==hash && e->key==key) { e->value=value; return 1; }
        slot=(slot+1)&(cap-1);
    }
    return 0;
}

static int sd_put_locked(RtCoreDict* d,RtCoreSourceDictRegistrationV1* owner,int64_t key,int64_t value) {
    int64_t next=sd_growth_capacity(d);
    if (next<0) return 0;
    if (next) {
        RtCoreSourceDictBackingV1* old=sd_backing(d);
        RtCoreSourceDictBackingV1* fresh=sd_allocate_backing(next,old->control,old->generation,old->descriptor,d);
        if (!fresh) return 0;
        int64_t len=0,tombs=0;
        for(int64_t i=0;i<d->cap;++i) if(d->entries[i].occupied==1 &&
            !sd_insert(fresh->entries,next,d->entries[i].key,d->entries[i].value,d->entries[i].hash,&len,&tombs)) {
                free(fresh); return 0;
            }
        if (!sd_insert(fresh->entries,next,key,value,sd_hash(key),&len,&tombs)) { free(fresh); return 0; }
        owner->backing=fresh; owner->capacity=next;
        d->entries=fresh->entries; d->cap=next; d->len=len; d->tombstones=tombs;
        if (d->read_backing==INT64_MAX) d->read_epoch=0; else ++d->read_backing;
        free(old);
    } else if (!sd_insert(d->entries,d->cap,key,value,sd_hash(key),&d->len,&d->tombstones)) return 0;
    rt_core_dict_read_advance(d); return 1;
}

static int64_t sd_project_locked(RtCoreDict* d,int64_t key,int remove,int* changed) {
    uint64_t h=sd_hash(key);
    int64_t slot=(int64_t)(h&(uint64_t)(d->cap-1));
    for(int64_t probes=0;probes<d->cap;++probes) {
        RtCoreDictEntry* e=&d->entries[slot];
        if (!e->occupied) return 0;
        if(e->occupied==1 && e->hash==h && e->key==key) {
            if (!remove) return e->value;
            e->occupied=-1; --d->len; ++d->tombstones;
            rt_core_dict_read_advance(d); *changed=1; return 1;
        }
        slot=(slot+1)&(d->cap-1);
    }
    return 0;
}

int64_t rt_source_region_dict_new_v1(int64_t control,int64_t generation,int64_t epoch,
    int64_t descriptor,int64_t capacity_hint,int64_t work) {
    (void)capacity_hint;
#if !defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    (void)control;(void)generation;(void)epoch;(void)descriptor;(void)work; return SD_INCOMPLETE;
#else
    if (!sd_try_lock()) return SD_INCOMPLETE;
    uint64_t native=0;
    int64_t cost=sd_metrics_locked(13,(const uint64_t*)(uintptr_t)descriptor,NULL,0,&native);
    int64_t result=cost<0 ? cost : work<cost ? SD_CAPACITY : 0;
    if (!result && !sd_descriptor((const uint64_t*)(uintptr_t)descriptor)) result=SD_INCOMPLETE;
    if (!result) result=rt_source_region_native_owner_enter_v1(control,generation,epoch,13,0,0,work-cost);
    if (result<=0) { rt_core_immortal_registry_release(); return result ? result : SD_INCOMPLETE; }
    /* Reserve one optional dictionary reader identity with one atomic attempt.
     * Contention is explicit; no unbounded CAS retry hides in provider fuel. */
    int64_t owner=atomic_load_explicit(&rt_core_dict_read_owner_counter,memory_order_relaxed);
    if (owner<0 || owner==INT64_MAX || !atomic_compare_exchange_strong_explicit(
        &rt_core_dict_read_owner_counter,&owner,owner+1,memory_order_relaxed,memory_order_relaxed)) {
        int64_t failure=owner==INT64_MAX ? SD_CAPACITY : SD_INCOMPLETE;
        rt_source_region_native_owner_exit_v1(control,13,0,0);
        rt_core_immortal_registry_release(); return failure;
    }
    RtCoreDict* d=(RtCoreDict*)rt_observed_calloc_v1(1,sizeof(*d));
    RtCoreSourceDictBackingV1* b=d ? sd_allocate_backing(8,control,generation,
        (const uint64_t*)(uintptr_t)descriptor,d) : NULL;
    RtCoreSourceDictRegistrationV1* registration=(RtCoreSourceDictRegistrationV1*)
        rt_observed_calloc_v1(1,sizeof(*registration));
    if (registration) { registration->dictionary=d; registration->backing=b; registration->capacity=8; }
    int64_t next=sd_registry_next();
    int ok=d && (uintptr_t)d<=INT64_MAX && !((uintptr_t)d&7) && b && registration &&
        !((uintptr_t)registration&7) && next>=0 &&
        (!next || rt_core_immortal_registry_resize((size_t)next));
    RtCoreScopedAllocationKey module_key = {0};
    if (ok) ok=rt_core_track_module_immortal_locked(d, &module_key);
    if (ok) {
        d->kind=RT_VALUE_HEAP_DICT; d->flags=RT_CORE_DICT_SOURCE_REGION_V1;
        d->transient_scope_id=module_key.owner;
        d->cap=8; d->entries=b->entries;
        ok=rt_core_immortal_registry_insert_raw((uintptr_t)registration|RT_CORE_SOURCE_DICT_REGISTRATION_TAG_V1);
        if (!ok) rt_core_rollback_module_immortal_locked(module_key);
    }
    if (ok) {
        atomic_fetch_add_explicit(&rt_core_heap_registry_count,1,memory_order_relaxed);
        d->read_owner=owner+1;
        d->read_epoch=1; d->read_backing=1;
        result=(int64_t)((uintptr_t)d|RT_VALUE_TAG_HEAP);
    } else { free(registration); free(b); free(d); result=SD_CAPACITY; }
    rt_source_region_native_owner_exit_v1(control,13,0,ok);
    rt_core_immortal_registry_release(); return result;
#endif
}

static int64_t sd_operation(int operation,int64_t control,int64_t generation,
    int64_t epoch,int64_t dictionary,int64_t key,int64_t value,int64_t work) {
#if !defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    (void)operation;(void)control;(void)generation;(void)epoch;(void)dictionary;
    (void)key;(void)value;(void)work; return SD_INCOMPLETE;
#else
    if (!sd_try_lock()) return SD_INCOMPLETE;
    int64_t error=0;
    RtCoreSourceDictRegistrationV1* registration=NULL;
    RtCoreDict* d=sd_find_locked(dictionary,work,&error,&registration);
    uint64_t native=0;
    int64_t cost=error ? error : sd_metrics_locked(operation,NULL,d,0,&native);
    if (!error && cost<0) error=cost;
    if (!error && work<cost) error=SD_CAPACITY;
    RtCoreSourceDictBackingV1* b=!error ? sd_backing(d) : NULL;
    if (!error && (b->control!=control || b->generation!=generation)) error=SD_FOREIGN;
    int64_t repr=!error ? ((const uint64_t*)(uintptr_t)b->descriptor[4])[7] : 0;
    if (!error) {
        int64_t entered=rt_source_region_native_owner_enter_v1(control,generation,epoch,
            operation,value,repr,work-cost);
        if (entered<0) error=entered;
    }
    int changed=0;
    int64_t result=error;
    if (!error) {
        if (operation==14) { changed=sd_put_locked(d,registration,key,value); result=changed ? 1 : SD_CAPACITY; }
        else result=sd_project_locked(d,key,operation==15,&changed);
        if (operation==16 && result>0)
            result=rt_source_region_native_project_struct_v1(control,generation,epoch,
                result,repr,work-cost);
        rt_source_region_native_owner_exit_v1(control,operation,changed,0);
    }
    rt_core_immortal_registry_release(); return result;
#endif
}
int64_t rt_source_region_dict_put_v1(int64_t c,int64_t g,int64_t e,int64_t d,int64_t k,int64_t v,int64_t w) {
    return sd_operation(14,c,g,e,d,k,v,w);
}
int64_t rt_source_region_dict_remove_v1(int64_t c,int64_t g,int64_t e,int64_t d,int64_t k,int64_t w) {
    return sd_operation(15,c,g,e,d,k,0,w);
}
int64_t rt_source_region_dict_get_v1(int64_t c,int64_t g,int64_t e,int64_t d,int64_t k,int64_t w) {
    return sd_operation(16,c,g,e,d,k,0,w);
}

int64_t rt_source_region_struct_dict_write_v1(int64_t c,int64_t g,int64_t destination,
    int64_t slot,int64_t dictionary,int64_t work) {
#if !defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    (void)c;(void)g;(void)destination;(void)slot;(void)dictionary;(void)work;
    return SD_INCOMPLETE;
#else
    /* Same order as dictionary mutation/retirement: native owner, then region
     * owner. The current backing cannot rehash/retire while this lock is held. */
    if (!sd_try_lock()) return SD_INCOMPLETE;
    int64_t error=0;
    RtCoreSourceDictRegistrationV1* owner=NULL;
    RtCoreDict* d=sd_find_locked(dictionary,work,&error,&owner);
    if (!error && !d) error=SD_INCOMPLETE;
    int64_t observation=sd_observation_locked();
    uint64_t native=observation>0 ? (uint64_t)observation : 0;
    if (!error && (observation<0 || !sd_add(&native,256) || (uint64_t)work<native)) error=SD_CAPACITY;
    RtCoreSourceDictBackingV1* b=!error ? owner->backing : NULL;
    if (!error && (b->control!=c || b->generation!=g)) error=SD_FOREIGN;
    if (!error && !sd_descriptor(b->descriptor)) error=SD_INCOMPLETE;
    int64_t result=error;
    if (!error) result=rt_source_region_native_struct_dict_write_v1(c,g,destination,
        slot,dictionary,work-(int64_t)native);
    rt_core_immortal_registry_release(); return result;
#endif
}

static void rt_core_source_dict_retire_locked_v1(RtCoreDict* d,
    RtCoreSourceDictRegistrationV1* owner) {
    /* The existing registry entry authenticates this exact header and its
     * current live backing BEFORE any prefix access. Copied ordinary headers
     * have no owner record and never enter this function. */
    if (owner->dictionary!=d || !owner->backing) return;
    RtCoreSourceDictBackingV1* b=owner->backing;
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (b->abi==1 && b->dictionary==(uintptr_t)d && b->control>0) {
        rt_source_region_native_owner_retire_v1(b->control,b->generation);
        b->control=0;
    }
#endif
    free(b); free(owner); d->entries=NULL;
}
