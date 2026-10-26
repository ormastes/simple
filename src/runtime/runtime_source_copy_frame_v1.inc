/* One private ordinary-heap copy per retained SOURCE control. This does not
 * allocate a SOURCE member, alter its mutation epoch, or authorize compiler
 * admission. The actual same-account facade/CFG/backend edges remain required. */
static int sr_copy_add_v1(uint64_t* target,uint64_t value) {
    if (*target > INT64_MAX || value > (uint64_t)INT64_MAX-*target) return 0;
    *target+=value; return 1;
}
static int sr_copy_mul_v1(uint64_t a,uint64_t b,uint64_t* out) {
    if (b && a > (uint64_t)INT64_MAX/b) return 0;
    *out=a*b; return 1;
}
/* Entire prepare -> allocation -> cleanup -> frame-end logical envelope.
 * Capacity is frozen from prepare until cancellation/successful ReadEnd. */
static int64_t sr_copy_bound_locked_v1(int64_t words,int64_t metric) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (!sr_allocator_ready() || words<=0 || metric<0 || metric>2 ||
        rt_transient_raw_copy_scope_v1()<=0) return SR_INCOMPLETE;
    uint64_t payload,n,work=1024,fields=96,bytes=0;
    if (!sr_copy_mul_v1((uint64_t)words,8,&payload)) return SR_CAPACITY;
    int64_t rw=rt_transient_raw_source_bound_v1(0);
    int64_t rf=rt_transient_raw_source_bound_v1(1);
    int64_t rb=rt_transient_raw_source_bound_v1(2);
    int64_t old=rt_transient_raw_copy_capacity_v1();
    if (rw<0 || rf<0 || rb<0 || old<0) return SR_INCOMPLETE;
    /* Existing raw owner grows at most twice old capacity (initial 256).
     * Conservative cap also covers no-grow and same-cap compaction. */
    uint64_t cap=old ? (uint64_t)old*2 : 256;
    if (rb && (!sr_copy_mul_v1((uint64_t)old,(uint64_t)rb/sizeof(RtTransientRawAlloc),&n) ||
        !sr_copy_mul_v1(n,16,&n) || !sr_copy_add_v1(&work,n))) return SR_CAPACITY;
    if (cap<(uint64_t)old || !sr_copy_mul_v1(cap,64,&n) || !sr_copy_add_v1(&work,n) ||
        !sr_copy_mul_v1((uint64_t)rt_struct_alloc_max_success_probe_v1,16,&n) ||
        !sr_copy_add_v1(&work,n) || !sr_copy_add_v1(&work,(uint64_t)rw) ||
        !sr_copy_mul_v1((uint64_t)old,2,&n) || !sr_copy_add_v1(&fields,n) ||
        !sr_copy_add_v1(&fields,(uint64_t)rf) || !sr_copy_add_v1(&fields,(uint64_t)words) ||
        !sr_copy_add_v1(&bytes,(uint64_t)rb) || !sr_copy_add_v1(&bytes,payload) ||
        !sr_copy_add_v1(&work,payload) || !sr_copy_add_v1(&work,fields) ||
        !sr_copy_add_v1(&work,bytes)) return SR_CAPACITY;
    return (int64_t)(metric==0 ? work : metric==1 ? fields : bytes);
#else
    (void)words; (void)metric; return SR_INCOMPLETE;
#endif
}
int64_t rt_source_region_copy_bound_v1(int64_t words,int64_t metric) {
    if (!sr_try_lock()) return SR_INCOMPLETE;
    int64_t result=sr_copy_bound_locked_v1(words,metric);
    rt_struct_alloc_lock_release(); return result;
}
int64_t rt_source_region_copy_prepare_v1(int64_t control,int64_t generation,
    int64_t words,int64_t work,int64_t fields,int64_t bytes) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (!sr_try_lock()) return SR_INCOMPLETE;
    int64_t w=sr_copy_bound_locked_v1(words,0),f=sr_copy_bound_locked_v1(words,1),b=sr_copy_bound_locked_v1(words,2);
    if (w<0 || f<0 || b<0 || work<w || fields<f || bytes<b) {
        rt_struct_alloc_lock_release(); return w<0 ? w : SR_CAPACITY;
    }
    RtSourceRegionV1* r=sr_control(control);
    int64_t error=sr_validate(r,generation);
    if (!error && (r->copy.state!=SR_COPY_EMPTY || r->lease || r->ticket)) error=SR_CONFLICT;
    if (!error && r->serial>=INT64_MAX) error=SR_CAPACITY;
    int64_t module=rt_transient_raw_copy_scope_v1();
    if (!error && module<=0) error=SR_INCOMPLETE;
    /* All fallible preparation precedes frame publication. Capacity growth
     * alone may survive a refused prepare, as in the existing raw owner. */
    if (!error && rt_transient_raw_source_prepare_v1(work)<0) error=SR_CAPACITY;
    int64_t revision=!error ? rt_transient_raw_copy_scope_pin_v1(module) : -1;
    if (!error && revision<0) error=SR_CONFLICT;
    if (!error) {
        r->copy=(RtSourceCopyFrameV1){.state=SR_COPY_PREPARED,.words=(uint64_t)words,
            .birth=++r->serial,.raw_revision=(uint64_t)revision,
            .raw_capacity=(uint64_t)rt_transient_raw_copy_capacity_v1(),.module=(uint64_t)module};
    }
    rt_struct_alloc_lock_release(); return error;
#else
    (void)control; (void)generation; (void)words; (void)work; (void)fields; (void)bytes;
    return SR_INCOMPLETE;
#endif
}
/* Same UNSAFE retained-control operand contract and identity checker as
 * pinned lifecycle operations; no caller DTO or TLS flag is authority. */
int64_t rt_source_region_copy_alloc_live_v1(int64_t control,int64_t generation,int64_t lease) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (!sr_allocator_ready() || !sr_try_lock()) return SR_INCOMPLETE;
    RtSourceRegionV1* r=NULL;
    int64_t error=sr_live_identity_unsafe_v1(control,generation,&r);
    if (!error) error=sr_validate(r,generation);
    if (!error && (r->copy.state!=SR_COPY_READY || !r->copy.birth || lease<=0 ||
        r->lease!=(uint64_t)lease || r->copy.lease!=(uint64_t)lease)) error=SR_CONSUMED;
    if (!error && (rt_transient_raw_copy_scope_v1()!=(int64_t)r->copy.module ||
        rt_transient_raw_copy_capacity_v1()!=(int64_t)r->copy.raw_capacity ||
        rt_transient_raw_source_revision_v1()!=(int64_t)r->copy.raw_revision)) error=SR_STALE;
    uint8_t* raw=NULL;
    if (!error) {
        raw=rt_alloc((int64_t)(r->copy.words*8));
        if (!raw) error=SR_CAPACITY;
        else {
            /* Retain actual birth immediately. No pointer escapes before the
             * same raw owner installs its non-freeable private pin. */
            r->copy.raw=(uintptr_t)raw;
            if (rt_transient_raw_copy_pin_v1(raw,r->copy.words*8,(int64_t)r->copy.module)) {
                /* Registration rollback uses the canonical allocation branch.
                 * The module/raw entry is ours, never a struct registry birth. */
                rt_transient_raw_owner_unregister(raw);
                rt_dispose_unregistered_raw_v1(raw,0,0);
                r->copy.raw=0; error=SR_INCOMPLETE;
            } else {
                r->copy.state=SR_COPY_LIVE;
                r->copy.raw_revision=(uint64_t)rt_transient_raw_source_revision_v1();
            }
        }
    }
    rt_struct_alloc_lock_release();
    return error ? error : (int64_t)(uintptr_t)raw;
#else
    (void)control; (void)generation; (void)lease; return SR_INCOMPLETE;
#endif
}
int64_t rt_source_region_copy_cleanup_live_v1(int64_t control,int64_t generation,int64_t lease) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (!sr_allocator_ready() || !sr_try_lock()) return SR_INCOMPLETE;
    RtSourceRegionV1* r=NULL;
    int64_t error=sr_live_identity_unsafe_v1(control,generation,&r);
    if (!error && (r->copy.state==SR_COPY_EMPTY || r->copy.state==SR_COPY_CLEANED ||
        !r->copy.birth || rt_transient_raw_copy_scope_v1()!=(int64_t)r->copy.module ||
        rt_transient_raw_copy_capacity_v1()!=(int64_t)r->copy.raw_capacity)) error=SR_CONSUMED;
    if (!error && r->copy.state==SR_COPY_PREPARED) {
        if (lease || r->lease || r->copy.raw || rt_transient_raw_copy_scope_unpin_v1((int64_t)r->copy.module))
            error=SR_CONFLICT;
        else r->copy=(RtSourceCopyFrameV1){0};
    } else if (!error) {
        if (lease<=0 || r->lease!=(uint64_t)lease || r->copy.lease!=(uint64_t)lease) error=SR_CONSUMED;
        if (!error && r->copy.state==SR_COPY_LIVE) {
            if (!r->copy.raw || rt_transient_raw_copy_claim_v1((void*)r->copy.raw,
                r->copy.words*8,(int64_t)r->copy.module,(int64_t)r->copy.raw_capacity)) error=SR_STALE;
            else {
                rt_dispose_unregistered_raw_v1((uint8_t*)r->copy.raw,0,0);
                r->copy.raw=0;
            }
        }
        if (!error) r->copy.state=SR_COPY_CLEANED;
    }
    rt_struct_alloc_lock_release(); return error;
#else
    (void)control; (void)generation; (void)lease; return SR_INCOMPLETE;
#endif
}
