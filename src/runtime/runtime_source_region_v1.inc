/* Private C4 struct provider. Included in the existing memory owner, so every
 * identity check uses its registry. This is not a full SOURCE capability. */
#include "runtime_source_region_v1.h"
#define SR_INCOMPLETE (-1)
#define SR_FOREIGN (-2)
#define SR_STALE (-3)
#define SR_CAPACITY (-4)
#define SR_CLOSED (-5)
#define SR_CONFLICT (-6)
#define SR_CONSUMED (-7)

enum { SR_COPY_EMPTY, SR_COPY_PREPARED, SR_COPY_READY, SR_COPY_ATTEMPTED, SR_COPY_LIVE, SR_COPY_CLEANED };
typedef struct RtSourceCopyFrameV1 {
    uint64_t state, words, birth, lease, raw_revision, raw_capacity, module;
    uintptr_t raw;
} RtSourceCopyFrameV1;
typedef struct RtSourceRegionV1 {
    uint64_t generation, epoch, serial, lease, ticket, members;
    uintptr_t destination;
    uint64_t slot;
    int64_t error;
    _Atomic uint8_t closed;
    uintptr_t execution_owner;
    RtSourceControlMetadataV1* control_metadata;
    RtSourceCopyFrameV1 copy;
} RtSourceRegionV1;

/* A single monotonic identity counter under the existing owner lock. It is
 * neither a registry nor a graph index. Exhaustion never permits address ABA. */
static uint64_t rt_source_region_next_generation_v1 = 1;
static RT_MEMORY_THREAD_LOCAL uint8_t sr_execution_owner_v1;
/* One bounded pending construction preparation per execution owner. */
static RT_MEMORY_THREAD_LOCAL uint64_t sr_prepared_registry_v1;
static RT_MEMORY_THREAD_LOCAL int64_t sr_prepared_raw_v1;
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
extern int64_t rt_transient_raw_source_bound_v1(int64_t metric);
extern int64_t rt_transient_raw_source_prepare_v1(int64_t prepaid);
extern int64_t rt_transient_raw_source_revision_v1(void);
#endif

static int sr_try_lock(void) {
#if defined(_WIN32)
    return TryAcquireSRWLockExclusive(&rt_struct_alloc_lock) != 0;
#else
    return pthread_rwlock_trywrlock(&rt_struct_alloc_lock) == 0;
#endif
}

static RtStructAllocation* sr_find(uintptr_t ptr) {
    if (!ptr || !rt_struct_alloc_cap) return NULL;
    size_t index = rt_transient_raw_hash(ptr) & (rt_struct_alloc_cap - 1);
    for (size_t probes = 0; probes < rt_struct_alloc_max_success_probe_v1; ++probes) {
        RtStructAllocation* entry = &rt_struct_allocs[index];
        if (!entry->ptr) return NULL;
        if (entry->ptr == ptr) return entry;
        index = (index + 1) & (rt_struct_alloc_cap - 1);
    }
    return NULL;
}

static RtSourceRegionV1* sr_control_any_owner(int64_t token) {
    RtStructAllocation* entry = sr_find((uintptr_t)token);
    RtSourceAllocationMetadataV1* metadata=rt_struct_source_metadata_v1(entry);
    return metadata && metadata->control &&
        metadata->bytes == sizeof(RtSourceRegionV1) &&
        metadata->generation == ((RtSourceRegionV1*)(uintptr_t)token)->generation
        ? (RtSourceRegionV1*)(uintptr_t)token : NULL;
}

static RtSourceRegionV1* sr_control(int64_t token) {
    RtSourceRegionV1* r=sr_control_any_owner(token);
    return r && r->execution_owner==(uintptr_t)&sr_execution_owner_v1 ? r : NULL;
}

static int64_t sr_validate(RtSourceRegionV1* r, int64_t generation) {
    if (!r) return SR_INCOMPLETE;
    if (generation <= 0 || r->generation != (uint64_t)generation) return SR_FOREIGN;
    if (atomic_load_explicit(&r->closed,memory_order_acquire)) return SR_CLOSED;
    return r->error;
}

static int64_t sr_fail(RtSourceRegionV1* r, int64_t error) {
    if (r && !r->error) r->error = error;
    return error;
}

/* Only compiler-sealed immutable descriptors reach this private boundary.
 * Certification is a compiler admission obligation, not inferred from C bits. */
static int sr_descriptor_header(const uint64_t* d, int64_t capacity) {
    if (sizeof(uintptr_t) != 8 || !d || d[0] != 1 || d[1] != 1 || d[5] != 1 || capacity != 1 ||
        !d[2] || d[2] > INT64_MAX || d[3] != d[2] / 8 || d[2] % 8 || !d[4]) return 0;
    return 1;
}

static int sr_descriptor(const uint64_t* d, int64_t capacity) {
    if (!sr_descriptor_header(d, capacity)) return 0;
    const uint64_t* slots = (const uint64_t*)(uintptr_t)d[4];
    for (uint64_t i = 0; i < d[3]; ++i) {
        const uint64_t* s = slots + i * 4;
        /* Uniform native-word aggregates only; compact field support must not
         * silently truncate an ordinary native SetField. */
        if (s[0] != i * 8 || s[1] != 8 || s[0] > d[2] ||
            s[1] > d[2] - s[0] || s[2] < 1 || s[2] > 3 ||
            (s[2] == 1 ? s[3] != 0 : (s[3] != 1 && s[3] != 2 && !(s[2]==2 && s[3]==4)))) return 0;
        /* No immutable certification owner exists in this struct provider. */
        if (s[2] == 3) return 0;
    }
    return d[3] * 8 == d[2];
}

static int64_t sr_copy_end_locked_v1(RtSourceRegionV1* r, int64_t lease) {
    if (r->copy.state == SR_COPY_EMPTY) return 0;
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (r->copy.state != SR_COPY_CLEANED || r->copy.raw ||
        r->copy.lease != (uint64_t)lease || rt_transient_raw_copy_scope_unpin_v1((int64_t)r->copy.module))
        return SR_CONFLICT;
    r->copy = (RtSourceCopyFrameV1){0};
    return 0;
#else
    (void)lease; return SR_INCOMPLETE;
#endif
}

/* Guarded/hardened allocator variants need their own bound qualification. */
static int sr_allocator_ready(void) {
    if (sizeof(uintptr_t) != 8) return 0;
#if ATOMIC_CHAR_LOCK_FREE != 2
    /* No hidden lock-backed atomic provider is qualified for SOURCE. */
    return 0;
#endif
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    return rt_transient_raw_owner_thread_allows() &&
        !rt_mem_harden_enabled() && rt_mem_guard_rate() <= 0;
#else
    return !rt_transient_raw_active && !rt_mem_harden_enabled() &&
        rt_mem_guard_rate() <= 0;
#endif
}

int64_t rt_source_region_abi_v1(void) { return 1; }
int64_t rt_source_region_capabilities_v1(void) {
    /* bit0: isolated raw struct primitive, never whole SOURCE coverage. */
    return sr_allocator_ready() ? 1 : 0;
}

static int64_t sr_bound_locked(int64_t operation, int64_t descriptor,
    int64_t capacity, int64_t metric) {
    if (operation < 1 || operation > 12 || metric < 0 || metric > 2) return SR_INCOMPLETE;
    uint64_t cap = rt_struct_alloc_cap;
    uint64_t work = 16 * rt_struct_alloc_max_success_probe_v1 + 512, fields = 0, bytes = 0;
    if (operation == 1 || operation == 12) {
        uint64_t next = 0;
        if (!cap) next = 256;
        else if ((rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10 >= cap * 7) {
            next = cap;
            if (operation == 1 || (rt_struct_alloc_len + 1) * 10 >= cap * 6) {
                if (cap >= RT_STRUCT_ALLOC_MAX_CAP) return SR_CAPACITY;
                next = cap * 2;
            }
        }
        /* Registry rehash reserves old traversal, both insertion probes and
         * the actual new table allocation; encoded metadata needs no extra lookup. */
        if (next) {
            fields += next * 2;
            bytes += next * sizeof(RtStructAllocation);
            work += cap * next + cap + next;
        }
        if (operation == 1) {
            bytes += sizeof(RtSourceRegionV1)+sizeof(RtSourceControlMetadataV1);
            fields += 18 + sizeof(RtSourceCopyFrameV1)/sizeof(uint64_t);
            work += cap;
        }
    }
    if (operation == 2 || operation == 12) {
        const uint64_t* d = (const uint64_t*)(uintptr_t)descriptor;
        /* Header only: requesting a bound must never walk slot metadata. */
        if (!sr_descriptor_header(d, capacity)) return SR_INCOMPLETE;
        if (d[3] > ((uint64_t)INT64_MAX - work) / 16) return SR_CAPACITY;
        work += d[3] * 16;
        if (operation == 2) {
            bytes += d[2]+sizeof(RtSourceAllocationMetadataV1);
            fields += d[3]+5;
            work += cap; /* insertion of a not-yet-allocated pointer */
        }
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
        if (operation == 2) {
            int64_t rw=rt_transient_raw_source_bound_v1(0);
            if (rw < 0 || (uint64_t)rw > INT64_MAX-work) return SR_CAPACITY;
            work+=(uint64_t)rw;
        }
        if (operation == 12) {
            int64_t rw=rt_transient_raw_source_bound_v1(0);
            int64_t rf=rt_transient_raw_source_bound_v1(1);
            int64_t rb=rt_transient_raw_source_bound_v1(2);
            if (rw < 0 || rf < 0 || rb < 0) return SR_INCOMPLETE;
            if ((uint64_t)rw > INT64_MAX-work || (uint64_t)rf > INT64_MAX-fields ||
                (uint64_t)rb > INT64_MAX-bytes) return SR_CAPACITY;
            work+=(uint64_t)rw; fields+=(uint64_t)rf; bytes+=(uint64_t)rb;
        }
#endif
    }
    if (fields > INT64_MAX || bytes > INT64_MAX || work > INT64_MAX-fields ||
        work+fields > INT64_MAX-bytes) return SR_CAPACITY;
    work += fields+bytes;
    return (int64_t)(metric == 0 ? work : metric == 1 ? fields : bytes);
}

int64_t rt_source_region_bound_v1(int64_t operation, int64_t descriptor,
    int64_t capacity, int64_t metric) {
    if (operation>=13 && operation<=17) {
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
        return rt_source_region_dict_bound_v1(operation,descriptor,capacity,metric);
#else
        return SR_INCOMPLETE;
#endif
    }
    if (!sr_try_lock()) return SR_INCOMPLETE;
    int64_t result = sr_bound_locked(operation, descriptor, capacity, metric);
    rt_struct_alloc_lock_release();
    return result;
}

static RT_MEMORY_THREAD_LOCAL int64_t sr_allow_failure_v1;
static int sr_allow(int64_t operation, int64_t descriptor, int64_t capacity,
    int64_t fuel) {
    sr_allow_failure_v1 = SR_INCOMPLETE;
    if (!sr_try_lock()) return 0;
    int64_t bound = sr_bound_locked(operation, descriptor, capacity, 0);
    if (bound > 0 && fuel >= bound) return 1; /* owner lock remains held */
    sr_allow_failure_v1 = bound < 0 ? bound : SR_CAPACITY;
    rt_struct_alloc_lock_release();
    return 0;
}

static int64_t sr_live_identity_unsafe_v1(int64_t control,int64_t generation,
    RtSourceRegionV1** out);
#include "runtime_source_copy_frame_v1.inc"

int64_t rt_source_region_allocation_prepare_v1(int64_t descriptor,
    int64_t capacity, int64_t fuel) {
    if (!sr_allocator_ready()) return SR_INCOMPLETE;
    if (!sr_allow(12, descriptor, capacity, fuel)) return sr_allow_failure_v1;
    int ok = sr_descriptor((const uint64_t*)(uintptr_t)descriptor, capacity);
    if (!ok) { rt_struct_alloc_lock_release(); return SR_INCOMPLETE; }
    if (ok && !rt_struct_alloc_cap) ok = rt_struct_alloc_resize(256);
    else if (ok && (rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10 >=
        rt_struct_alloc_cap * 7) {
        size_t next = rt_struct_alloc_cap;
        if ((rt_struct_alloc_len + 1) * 10 >= next * 6) {
            if (next >= RT_STRUCT_ALLOC_MAX_CAP) ok = 0;
            else next *= 2;
        }
        if (ok) ok = rt_struct_alloc_resize(next);
    }
    if (rt_source_region_registry_revision_v1 >= INT64_MAX) ok = 0;
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    int64_t raw_revision = ok ? rt_transient_raw_source_prepare_v1(fuel) : SR_CAPACITY;
    if (raw_revision < 0) ok = 0;
    sr_prepared_raw_v1 = raw_revision;
#else
    sr_prepared_raw_v1 = 1;
#endif
    sr_prepared_registry_v1 = ok ? rt_source_region_registry_revision_v1 : 0;
    int64_t result = ok ? (int64_t)rt_source_region_registry_revision_v1 : SR_CAPACITY;
    rt_struct_alloc_lock_release();
    return result;
}

int64_t rt_source_region_create_v1(int64_t fuel) {
    if (!sr_allocator_ready()) return SR_INCOMPLETE;
    if (!sr_allow(1, 0, 0, fuel)) return sr_allow_failure_v1;
    if (rt_source_region_next_generation_v1 >= INT64_MAX ||
        rt_source_region_registry_revision_v1 >= INT64_MAX) {
        rt_struct_alloc_lock_release(); return SR_CAPACITY;
    }
    /* Control state is explicitly retained, outside the observed graph. */
    RtSourceRegionV1* r = (RtSourceRegionV1*)rt_observed_calloc_v1(1, sizeof(*r));
    RtSourceControlMetadataV1* control_metadata=(RtSourceControlMetadataV1*)
        rt_observed_calloc_v1(1,sizeof(*control_metadata));
    RtSourceAllocationMetadataV1* metadata=control_metadata ? &control_metadata->allocation : NULL;
    size_t metadata_bits=0;
    int ok = r && rt_struct_source_metadata_bits_v1(metadata,&metadata_bits) &&
        (rt_struct_alloc_cap || rt_struct_alloc_resize(256));
    if (ok && (rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10 >=
        rt_struct_alloc_cap * 7) {
        ok = rt_struct_alloc_cap < RT_STRUCT_ALLOC_MAX_CAP &&
            rt_struct_alloc_resize(rt_struct_alloc_cap * 2);
    }
    if (ok) {
        metadata->bytes=sizeof(*r); metadata->control=1;
        ok = rt_struct_alloc_insert_raw((uintptr_t)r,metadata_bits);
    }
    if (!ok) { free(metadata); free(r); rt_struct_alloc_lock_release(); return SR_CAPACITY; }
    r->generation = rt_source_region_next_generation_v1++;
    r->epoch = 1;
    r->execution_owner = (uintptr_t)&sr_execution_owner_v1;
    r->control_metadata=control_metadata;
    atomic_init(&r->closed,0);
    metadata->region=(uintptr_t)r; metadata->generation=r->generation;
    rt_source_region_registry_changed_v1();
    rt_struct_alloc_lock_release(); return (int64_t)(uintptr_t)r;
}

/* Compiler-sealed birth provenance makes this immutable load infallible.
 * It is not a general token observer and must never be called on saved tokens. */
int64_t rt_source_region_created_generation_v1(int64_t born_control) {
    return (int64_t)((const RtSourceRegionV1*)(uintptr_t)born_control)->generation;
}

int64_t rt_source_region_alloc_v1(int64_t control, int64_t generation,
    int64_t epoch, int64_t descriptor, int64_t capacity, int64_t prepared,
    int64_t fuel) {
    if (!sr_allocator_ready()) return SR_INCOMPLETE;
    if (!sr_allow(2, descriptor, capacity, fuel)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(control);
    int64_t error = sr_validate(r, generation);
    if (!error && !sr_descriptor((const uint64_t*)(uintptr_t)descriptor, capacity)) error = SR_INCOMPLETE;
    if (!error && r->epoch != (uint64_t)epoch) error = SR_STALE;
    if (!error && (r->lease || r->ticket)) error = SR_CONFLICT;
    if (!error && (prepared <= 0 || (uint64_t)prepared != rt_source_region_registry_revision_v1))
        error = SR_STALE;
    if (!error && (uint64_t)prepared != sr_prepared_registry_v1) error = SR_STALE;
#if defined(SIMPLE_RUNTIME_MEMORY_OWNER)
    if (!error && sr_prepared_raw_v1 != rt_transient_raw_source_revision_v1()) error = SR_STALE;
#endif
    if (!error && (rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10 >=
        rt_struct_alloc_cap * 7) error = SR_CAPACITY;
    if (!error && (r->serial >= INT64_MAX || r->members >= INT64_MAX))
        error = sr_fail(r, SR_CAPACITY);
    void* ptr = NULL;
    sr_prepared_registry_v1 = 0;
    if (!error) {
        const uint64_t* d = (const uint64_t*)(uintptr_t)descriptor;
        /* Raw/transient registry capacity was prepared before allocation. */
        RtSourceAllocationMetadataV1* metadata=(RtSourceAllocationMetadataV1*)rt_observed_calloc_v1(1,sizeof(*metadata));
        size_t metadata_bits=0;
        if (!rt_struct_source_metadata_bits_v1(metadata,&metadata_bits)) {
            free(metadata); error=sr_fail(r,SR_CAPACITY);
        } else {
            ptr = rt_alloc((int64_t)d[2]);
            if (!ptr) { free(metadata); error=sr_fail(r,SR_CAPACITY); }
        }
        if (!error) {
            metadata->bytes=(size_t)d[2]; metadata->region=(uintptr_t)r;
            metadata->descriptor=d; metadata->generation=r->generation; ++r->serial;
            rt_struct_alloc_insert_raw((uintptr_t)ptr,metadata_bits);
            ++r->members;
            rt_source_region_registry_changed_v1();
        }
    }
    rt_struct_alloc_lock_release();
    return error ? error : (int64_t)(uintptr_t)ptr;
}

static int64_t sr_observe(int64_t control, int64_t generation, int64_t fuel, int op) {
    if (!sr_allow(op, 0, 0, fuel)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(control);
    int64_t error = op == 3 ? (r ? 0 : SR_INCOMPLETE) : sr_validate(r, generation);
    int64_t result = error ? error : (int64_t)(op == 3 ? r->generation : r->epoch);
    rt_struct_alloc_lock_release(); return result;
}
int64_t rt_source_region_generation_v1(int64_t c, int64_t f) { return sr_observe(c, 0, f, 3); }
int64_t rt_source_region_stamp_v1(int64_t c, int64_t g, int64_t f) { return sr_observe(c, g, f, 4); }

int64_t rt_source_region_read_begin_v1(int64_t c, int64_t g, int64_t e, int64_t f) {
    if (!sr_allow(5, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = sr_validate(r, g);
    if (!error && r->epoch != (uint64_t)e) error = SR_STALE;
    if (!error && (r->lease || r->ticket || (r->copy.state != SR_COPY_EMPTY && r->copy.state != SR_COPY_PREPARED))) error = SR_CONFLICT;
    if (!error && r->serial >= INT64_MAX) error = sr_fail(r, SR_CAPACITY);
    int64_t result = error ? error : (int64_t)(r->lease = ++r->serial);
    if (!error && r->copy.state == SR_COPY_PREPARED) {
        r->copy.lease = r->lease;
        r->copy.state = SR_COPY_READY;
    }
    rt_struct_alloc_lock_release(); return result;
}

int64_t rt_source_region_read_end_v1(int64_t c, int64_t g, int64_t lease, int64_t f) {
    if (!sr_allow(6, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = !r ? SR_INCOMPLETE : r->generation != (uint64_t)g ? SR_FOREIGN :
        lease <= 0 || r->lease != (uint64_t)lease ? SR_CONSUMED : 0;
    if (!error) error = sr_copy_end_locked_v1(r, lease);
    if (!error) r->lease = 0;
    rt_struct_alloc_lock_release(); return error;
}

int64_t rt_source_region_write_begin_v1(int64_t c, int64_t g, int64_t e,
    int64_t destination, int64_t slot, int64_t f) {
    if (!sr_allow(7, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = sr_validate(r, g);
    RtStructAllocation* dst = sr_find((uintptr_t)destination);
    if (!error && r->epoch != (uint64_t)e) error = SR_STALE;
    if (!error && (r->lease || r->ticket)) error = SR_CONFLICT;
    RtSourceAllocationMetadataV1* destination_metadata=rt_struct_source_metadata_v1(dst);
    if (!error && (!destination_metadata || destination_metadata->control ||
        destination_metadata->region != (uintptr_t)r || destination_metadata->generation != r->generation)) error = SR_FOREIGN;
    if (!error && (slot < 0 || (uint64_t)slot >= destination_metadata->descriptor[3])) error = SR_INCOMPLETE;
    if (!error) {
        const uint64_t* row=(const uint64_t*)(uintptr_t)destination_metadata->descriptor[4]+(uint64_t)slot*4;
        if (row[2]==2 && row[3]==4) error=SR_INCOMPLETE; /* only op17 owns Dict edges */
    }
    if (!error && (r->serial >= INT64_MAX || r->epoch >= INT64_MAX)) error = sr_fail(r, SR_CAPACITY);
    if (!error) { r->ticket = ++r->serial; r->destination = (uintptr_t)destination; r->slot = (uint64_t)slot; }
    int64_t result = error ? error : (int64_t)r->ticket;
    rt_struct_alloc_lock_release(); return result;
}

int64_t rt_source_region_write_commit_v1(int64_t c, int64_t g, int64_t ticket,
    int64_t value, int64_t f) {
    if (!sr_allow(8, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = sr_validate(r, g);
    if (!error && (ticket <= 0 || r->ticket != (uint64_t)ticket)) error = SR_CONSUMED;
    RtStructAllocation* dst = !error ? sr_find(r->destination) : NULL;
    RtSourceAllocationMetadataV1* destination_metadata=rt_struct_source_metadata_v1(dst);
    if (!error && (!destination_metadata || destination_metadata->control ||
        destination_metadata->region != (uintptr_t)r || destination_metadata->generation != r->generation)) error = SR_FOREIGN;
    if (!error) {
        const uint64_t* s = (const uint64_t*)(uintptr_t)destination_metadata->descriptor[4] + r->slot * 4;
        if (s[2] == 2) {
            if (s[3]==4) error=SR_INCOMPLETE; /* no dictionary lookup under region lock */
            uintptr_t identity=(uintptr_t)value;
            /* repr2 certifies an exact statically typed Struct, never Any.
             * Nullability is not part of descriptor v1: zero is construction
             * storage only and cannot be committed as a completed edge. */
            if (!identity || (s[3] == 2 && (identity & 7) != 1) ||
                (s[3] == 1 && (identity & 7) != 0)) error=SR_FOREIGN;
            if (s[3] == 2) identity &= ~(uintptr_t)7;
            RtStructAllocation* child = !error ? sr_find(identity) : NULL;
            RtSourceAllocationMetadataV1* child_metadata=rt_struct_source_metadata_v1(child);
            if (!error && (!child_metadata || child_metadata->control ||
                child_metadata->region != (uintptr_t)r || child_metadata->generation != r->generation))
                error = SR_FOREIGN;
        }
        if (!error) { memcpy((void*)(dst->ptr + s[0]), &value, 8); ++r->epoch; }
        /* Every attempted ticket commit is one-use, including rejection. */
        r->ticket = 0; r->destination = 0;
    }
    int64_t result = error ? error : (int64_t)r->epoch;
    rt_struct_alloc_lock_release(); return result;
}

int64_t rt_source_region_alias_write_v1(int64_t c, int64_t g, int64_t destination,
    int64_t slot, int64_t value, int64_t f) {
    /* No user code/callback may intervene in this compiler-private sequence.
     * It never updates a HIR saved stamp. */
    int64_t epoch = rt_source_region_stamp_v1(c, g, f);
    if (epoch < 0) return epoch;
    int64_t ticket = rt_source_region_write_begin_v1(c, g, epoch, destination, slot, f);
    return ticket < 0 ? ticket : rt_source_region_write_commit_v1(c, g, ticket, value, f);
}

/* C owner only: caller retains the qualified dictionary owner lock. No
 * allocation, callback, reserve or dictionary registry access under this lock. */
int64_t rt_source_region_native_struct_dict_write_v1(int64_t c,int64_t g,
    int64_t destination,int64_t slot,int64_t dictionary,int64_t work) {
    if (!sr_allow(9,0,0,work)) return sr_allow_failure_v1;
    RtSourceRegionV1* r=sr_control(c);
    int64_t error=sr_validate(r,g);
    if (!error && (r->lease || r->ticket)) error=SR_CONFLICT;
    RtStructAllocation* dst=!error ? sr_find((uintptr_t)destination) : NULL;
    RtSourceAllocationMetadataV1* metadata=rt_struct_source_metadata_v1(dst);
    if (!error && (!metadata || metadata->control || metadata->region!=(uintptr_t)r ||
        metadata->generation!=r->generation)) error=SR_FOREIGN;
    const uint64_t* row=NULL;
    if (!error && (!sr_descriptor_header(metadata->descriptor,1) ||
        metadata->bytes!=metadata->descriptor[2] || slot<0 ||
        (uint64_t)slot>=metadata->descriptor[3])) error=SR_INCOMPLETE;
    if (!error) {
        row=(const uint64_t*)(uintptr_t)metadata->descriptor[4]+(uint64_t)slot*4;
        if (row[0]!=(uint64_t)slot*8 || row[1]!=8 || row[2]!=2 || row[3]!=4 ||
            row[0]>metadata->bytes || 8>metadata->bytes-row[0] || dictionary<=0 ||
            ((uintptr_t)dictionary&7)!=1) error=SR_INCOMPLETE;
    }
    if (!error && r->epoch>=INT64_MAX) error=SR_CAPACITY;
    if (!error) { memcpy((void*)(dst->ptr+row[0]),&dictionary,8); ++r->epoch; }
    int64_t result=error ? error : (int64_t)r->epoch;
    rt_struct_alloc_lock_release(); return result;
}

int64_t rt_source_region_close_v1(int64_t c, int64_t g, int64_t f) {
    if (!sr_allow(10, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = !r ? SR_INCOMPLETE : r->generation != (uint64_t)g ? SR_FOREIGN : 0;
    if (!error && r->copy.state != SR_COPY_EMPTY) error = SR_CONFLICT;
    if (!error) { atomic_store_explicit(&r->closed,1,memory_order_release); r->ticket = 0; r->destination = 0; }
    rt_struct_alloc_lock_release(); return error;
}

int64_t rt_source_region_release_v1(int64_t c, int64_t g, int64_t f) {
    if (!sr_allow(11, 0, 0, f)) return sr_allow_failure_v1;
    RtSourceRegionV1* r = sr_control(c);
    int64_t error = !r ? SR_INCOMPLETE : r->generation != (uint64_t)g ? SR_FOREIGN :
        !atomic_load_explicit(&r->closed,memory_order_acquire) || r->lease || r->ticket || r->members || r->copy.state != SR_COPY_EMPTY ? SR_CONFLICT : 0;
    if (!error) {
        RtStructAllocation* entry = sr_find((uintptr_t)c);
        RtSourceAllocationMetadataV1* metadata=rt_struct_source_metadata_v1(entry);
        *entry = (RtStructAllocation){.ptr = RT_STRUCT_ALLOC_TOMBSTONE};
        free(metadata);
        --rt_struct_alloc_len; ++rt_struct_alloc_tombs;
        rt_source_region_registry_changed_v1();
        free(r);
    }
    rt_struct_alloc_lock_release(); return error;
}

static void rt_source_region_retire_locked_v1(RtSourceAllocationMetadataV1* metadata) {
    if (metadata->region) {
        /* Retirement runs under the existing registry owner lock. Even an
         * unadmitted foreign raw free must revoke the original region, rather
         * than silently discarding its association. No fresh authority issued. */
        RtSourceRegionV1* r = sr_control_any_owner((int64_t)metadata->region);
        if (r && r->generation == metadata->generation) {
            atomic_store_explicit(&r->closed,1,memory_order_release);
            if (!metadata->control && r->members) --r->members;
        }
    }
    free(metadata);
}

/* These operations are UNSAFE until a compiler-affine lifetime receipt proves
 * that the operand remains a genuinely pinned control. No registry lookup can
 * be substituted for that proof, and a facade live boolean cannot provide it. */
int64_t rt_source_region_live_cleanup_bound_v1(int64_t operation,int64_t metric) {
    if (operation<1 || operation>3 || metric<0 || metric>2) return SR_INCOMPLETE;
    if (metric) return 0;
    return operation==1 ? 16 : operation==2 ? 24 : 64;
}

static int64_t sr_live_identity_unsafe_v1(int64_t control,int64_t generation,
    RtSourceRegionV1** out) {
    if (!control) return SR_INCOMPLETE;
    RtSourceRegionV1* r=(RtSourceRegionV1*)(uintptr_t)control;
    if (generation<=0 || r->generation!=(uint64_t)generation) return SR_FOREIGN;
    if (r->execution_owner!=(uintptr_t)&sr_execution_owner_v1) return SR_INCOMPLETE;
    *out=r;
    return 0;
}

int64_t rt_source_region_revoke_live_v1(int64_t control,int64_t generation,
    int64_t prepaid_work) {
    if (prepaid_work<16) return SR_CAPACITY;
    RtSourceRegionV1* r;
    int64_t error=sr_live_identity_unsafe_v1(control,generation,&r);
    if (error) return error;
    if (r->copy.state != SR_COPY_EMPTY) return SR_CONFLICT;
    /* Only the atomic flag changes: foreign retirement may run under the
     * existing registry lock, and plain ticket/member fields are untouched. */
    atomic_store_explicit(&r->closed,1,memory_order_release);
    return 0;
}

int64_t rt_source_region_read_end_live_v1(int64_t control,int64_t generation,
    int64_t lease,int64_t prepaid_work) {
    if (prepaid_work<24) return SR_CAPACITY;
    RtSourceRegionV1* r;
    int64_t error=sr_live_identity_unsafe_v1(control,generation,&r);
    if (error) return error;
    /* The owner-thread lease pin prevents release. Foreign retirement writes
     * atomic closed and lock-protected membership, never this lease field.
     * Compiler confinement forbids callbacks/another mutable lease owner. */
    if (lease<=0 || r->lease!=(uint64_t)lease) return SR_CONSUMED;
    error=sr_copy_end_locked_v1(r,lease);
    if (error) return error;
    r->lease=0;
    return 0;
}

int64_t rt_source_region_release_live_v1(int64_t control,int64_t generation,
    int64_t prepaid_work) {
    if (prepaid_work<64) return SR_CAPACITY;
    RtSourceRegionV1* r;
    int64_t error=sr_live_identity_unsafe_v1(control,generation,&r);
    if (error) return error;
    if (!sr_try_lock()) return SR_INCOMPLETE; /* consumed attempt; owner retained */
    RtSourceControlMetadataV1* metadata=r->control_metadata;
    size_t slot=metadata->registry_slot;
    if (slot>=rt_struct_alloc_cap) error=SR_INCOMPLETE;
    RtStructAllocation* entry=!error ? &rt_struct_allocs[slot] : NULL;
    if (!error && (entry->ptr!=(uintptr_t)r ||
        rt_struct_source_metadata_v1(entry)!=&metadata->allocation ||
        !metadata->allocation.control || metadata->allocation.region!=(uintptr_t)r ||
        metadata->allocation.generation!=(uint64_t)generation ||
        metadata->allocation.bytes!=sizeof(*r))) error=SR_INCOMPLETE;
    if (!error && (!atomic_load_explicit(&r->closed,memory_order_acquire) ||
        r->members || r->lease || r->copy.state != SR_COPY_EMPTY)) error=SR_CONFLICT;
    if (!error) {
        /* Atomic revocation already invalidated the writer. Discard its plain
         * retained fields only while holding the existing owner lock. */
        r->ticket=0; r->destination=0;
        *entry=(RtStructAllocation){.ptr=RT_STRUCT_ALLOC_TOMBSTONE};
        --rt_struct_alloc_len; ++rt_struct_alloc_tombs;
        rt_source_region_registry_changed_v1();
        free(metadata); free(r);
    }
    rt_struct_alloc_lock_release();
    return error;
}

/* Get16 pays one additional successful member-registry lookup (<=P probes,
 * eight logical slot/branch/index steps per probe) plus 256 fixed logical
 * hash/tag/header/metadata/bound steps. No descriptor-slot
 * walk is performed: SOURCE birth validated its immutable full descriptor. */
static int64_t sr_projection_work_locked_v1(void) {
    if (rt_struct_alloc_max_success_probe_v1>((uint64_t)INT64_MAX-256)/8)
        return SR_CAPACITY;
    return (int64_t)(rt_struct_alloc_max_success_probe_v1*8+256);
}
int64_t rt_source_region_native_projection_bound_v1(void) {
    if (!sr_try_lock()) return SR_INCOMPLETE;
    int64_t result=sr_projection_work_locked_v1();
    rt_struct_alloc_lock_release(); return result;
}
/* Caller holds native owner then region owner after successful enter16.
 * This internal entry cannot mint a lifetime or nominal type certificate. */
int64_t rt_source_region_native_project_struct_v1(int64_t control,int64_t generation,
    int64_t epoch,int64_t child,int64_t representation,int64_t work) {
    int64_t base=sr_bound_locked(9,0,0,0), projection=sr_projection_work_locked_v1();
    if (base<0 || projection<0 || base>INT64_MAX-projection || work<base+projection)
        return SR_CAPACITY; /* before the additional registry lookup */
    RtSourceRegionV1* r=(RtSourceRegionV1*)(uintptr_t)control;
    int64_t error=sr_validate(r,generation);
    if (!error && r->epoch!=(uint64_t)epoch) error=SR_STALE;
    uintptr_t identity=(uintptr_t)child;
    if (!error && (child<=0 || (representation!=1 && representation!=2) ||
        (representation==1 && (identity&7)) ||
        (representation==2 && (identity&7)!=1))) error=SR_FOREIGN;
    if (representation==2) identity &= ~(uintptr_t)7;
    RtStructAllocation* entry=!error ? sr_find(identity) : NULL;
    RtSourceAllocationMetadataV1* metadata=rt_struct_source_metadata_v1(entry);
    if (!error && (!metadata || metadata->control || metadata->region!=(uintptr_t)r ||
        metadata->generation!=r->generation)) error=SR_FOREIGN;
    if (!error && (!sr_descriptor_header(metadata->descriptor,1) ||
        metadata->bytes!=metadata->descriptor[2])) error=SR_INCOMPLETE;
    return error ? error : child; /* preserve documented raw/tag1 bits */
}

int64_t rt_source_region_native_owner_enter_v1(int64_t control,int64_t generation,
    int64_t epoch,int64_t operation,int64_t child,int64_t representation,int64_t work) {
    if (operation<13 || operation>16) return SR_INCOMPLETE;
    if (!sr_allow(9,0,0,work)) return sr_allow_failure_v1;
    if (operation==16) {
        int64_t base=sr_bound_locked(9,0,0,0), projection=sr_projection_work_locked_v1();
        if (base<0 || projection<0 || base>INT64_MAX-projection || work<base+projection) {
            rt_struct_alloc_lock_release(); return SR_CAPACITY;
        }
    }
    RtSourceRegionV1* r=sr_control(control);
    int64_t error=sr_validate(r,generation);
    if (!error && r->epoch!=(uint64_t)epoch) error=SR_STALE;
    if (!error && (r->ticket || (operation!=16 && r->lease))) error=SR_CONFLICT;
    if (!error && operation==13 && r->members>=INT64_MAX) error=sr_fail(r,SR_CAPACITY);
    if (!error && (operation==14 || operation==15) && r->epoch>=INT64_MAX)
        error=sr_fail(r,SR_CAPACITY);
    if (!error && operation==14) {
        uintptr_t identity=(uintptr_t)child;
        if (child<=0 || (representation!=1 && representation!=2) ||
            (representation==1 && (identity&7)) ||
            (representation==2 && (identity&7)!=1)) error=SR_FOREIGN;
        if (representation==2) identity &= ~(uintptr_t)7;
        RtStructAllocation* entry=!error ? sr_find(identity) : NULL;
        RtSourceAllocationMetadataV1* metadata=rt_struct_source_metadata_v1(entry);
        if (!error && (!metadata || metadata->control ||
            metadata->region!=(uintptr_t)r || metadata->generation!=r->generation ||
            !metadata->descriptor || metadata->descriptor[1]!=1)) error=SR_FOREIGN;
    }
    if (error) { rt_struct_alloc_lock_release(); return error; }
    return control; /* Both existing owners remain locked until native exit. */
}

void rt_source_region_native_owner_exit_v1(int64_t control,int64_t operation,
    int64_t changed,int64_t born) {
    RtSourceRegionV1* r=(RtSourceRegionV1*)(uintptr_t)control;
    if (operation==13 && born) ++r->members;
    if ((operation==14 || operation==15) && changed) ++r->epoch;
    rt_struct_alloc_lock_release();
}

void rt_source_region_native_owner_retire_v1(int64_t control,int64_t generation) {
    /* Actual native retirement already holds its owner lock. No reverse
     * blocking acquisition or new synchronization owner is introduced. */
    rt_struct_alloc_lock_acquire();
    RtSourceRegionV1* r=sr_control_any_owner(control);
    if (r && r->generation==(uint64_t)generation) {
        atomic_store_explicit(&r->closed,1,memory_order_release);
        if (r->members) --r->members;
    }
    rt_struct_alloc_lock_release();
}
