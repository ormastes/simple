/* persistent_raw_registry_impl.h -- private persistent raw-alloc size registry
 * shared by runtime_memory.c and runtime_native.c (!SIMPLE_RUNTIME_MEMORY_OWNER).
 *
 * Pre-scope rt_alloc blocks (e.g. SymbolTable / Scope(0) / lowering owners),
 * paused-scope rt_alloc blocks, and promoted transient raw blocks that outlive
 * per-scope transient_raw_alloc clear must retain their byte extents so
 * rt_transient_heap_promote / rt_transient_heap_adopt can traverse their
 * object-reference words in the current or subsequent transient scopes.
 *
 * Kept strictly separate from rt_struct_allocs so rt_struct_receiver_valid
 * remains exclusive to rt_struct_alloc. Synchronization mirrors
 * struct_alloc_registry_impl.h (<windows.h> on _WIN32, <pthread.h> elsewhere).
 * The includer must define PERSISTENT_RAW_REGISTRY_HASH(ptr) before including
 * this header.
 */

#ifndef PERSISTENT_RAW_REGISTRY_HASH
#error "define PERSISTENT_RAW_REGISTRY_HASH(ptr) before including persistent_raw_registry_impl.h"
#endif

typedef struct RtPersistentRawAllocation {
    uintptr_t ptr;
    size_t bytes;
} RtPersistentRawAllocation;

#define RT_PERSISTENT_RAW_TOMBSTONE ((uintptr_t)1)

static RtPersistentRawAllocation* rt_persistent_raw_allocs = NULL;
static size_t rt_persistent_raw_cap = 0;
static size_t rt_persistent_raw_len = 0;
static size_t rt_persistent_raw_tombs = 0;

#if defined(_WIN32)
static SRWLOCK rt_persistent_raw_lock = SRWLOCK_INIT;
#else
static pthread_rwlock_t rt_persistent_raw_lock = PTHREAD_RWLOCK_INITIALIZER;
#endif

static void rt_persistent_raw_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockExclusive(&rt_persistent_raw_lock);
#else
    pthread_rwlock_wrlock(&rt_persistent_raw_lock);
#endif
}

static void rt_persistent_raw_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockExclusive(&rt_persistent_raw_lock);
#else
    pthread_rwlock_unlock(&rt_persistent_raw_lock);
#endif
}

static void rt_persistent_raw_read_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockShared(&rt_persistent_raw_lock);
#else
    pthread_rwlock_rdlock(&rt_persistent_raw_lock);
#endif
}

static void rt_persistent_raw_read_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockShared(&rt_persistent_raw_lock);
#else
    pthread_rwlock_unlock(&rt_persistent_raw_lock);
#endif
}

static int rt_persistent_raw_insert_raw_locked(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_persistent_raw_cap - 1;
    size_t i = PERSISTENT_RAW_REGISTRY_HASH(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (size_t probes = 0; probes < rt_persistent_raw_cap; probes++) {
        uintptr_t entry = rt_persistent_raw_allocs[i].ptr;
        if (entry == 0) {
            size_t target = first_tomb == SIZE_MAX ? i : first_tomb;
            rt_persistent_raw_allocs[target] = (RtPersistentRawAllocation){ptr, bytes};
            if (first_tomb != SIZE_MAX) rt_persistent_raw_tombs--;
            rt_persistent_raw_len++;
            return 1;
        }
        if (entry == RT_PERSISTENT_RAW_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = i;
        } else if (entry == ptr) {
            rt_persistent_raw_allocs[i].bytes = bytes;
            return 1;
        }
        i = (i + 1) & mask;
    }
    if (first_tomb != SIZE_MAX) {
        rt_persistent_raw_allocs[first_tomb] = (RtPersistentRawAllocation){ptr, bytes};
        rt_persistent_raw_tombs--;
        rt_persistent_raw_len++;
        return 1;
    }
    return 0;
}

static int rt_persistent_raw_resize_locked(size_t next_cap) {
    const size_t max_entries = SIZE_MAX / sizeof(RtPersistentRawAllocation);
    if (next_cap == 0 || next_cap > max_entries) return 0;
    RtPersistentRawAllocation* fresh = (RtPersistentRawAllocation*)rt_observed_calloc_v1(
        next_cap, sizeof(RtPersistentRawAllocation));
    if (!fresh) return 0;
    RtPersistentRawAllocation* old = rt_persistent_raw_allocs;
    size_t old_cap = rt_persistent_raw_cap;
    size_t old_len = rt_persistent_raw_len;
    size_t old_tombs = rt_persistent_raw_tombs;
    rt_persistent_raw_allocs = fresh;
    rt_persistent_raw_cap = next_cap;
    rt_persistent_raw_len = 0;
    rt_persistent_raw_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t ptr = old[i].ptr;
        if (ptr != 0 && ptr != RT_PERSISTENT_RAW_TOMBSTONE) {
            if (!rt_persistent_raw_insert_raw_locked(ptr, old[i].bytes)) {
                free(fresh);
                rt_persistent_raw_allocs = old;
                rt_persistent_raw_cap = old_cap;
                rt_persistent_raw_len = old_len;
                rt_persistent_raw_tombs = old_tombs;
                return 0;
            }
        }
    }
    free(old);
    return 1;
}

static int rt_persistent_raw_grow_locked(void) {
    const size_t max_entries = SIZE_MAX / sizeof(RtPersistentRawAllocation);
    size_t next_cap;
    if (rt_persistent_raw_cap == 0) {
        next_cap = 256;
    } else if ((rt_persistent_raw_len + 1) * 10 < rt_persistent_raw_cap * 6) {
        /* Purge tombstones without expanding table footprint. */
        next_cap = rt_persistent_raw_cap;
    } else {
        if (rt_persistent_raw_cap > max_entries / 2) return 0;
        next_cap = rt_persistent_raw_cap * 2;
    }
    return rt_persistent_raw_resize_locked(next_cap);
}

static int rt_persistent_raw_register(void* ptr, size_t bytes) {
    if (!ptr || (uintptr_t)ptr == RT_PERSISTENT_RAW_TOMBSTONE) return 0;
    rt_persistent_raw_lock_acquire();
    if (rt_persistent_raw_cap == 0 ||
            (rt_persistent_raw_len + rt_persistent_raw_tombs + 1) * 10 >=
                rt_persistent_raw_cap * 7) {
        if (!rt_persistent_raw_grow_locked()) {
            rt_persistent_raw_lock_release();
            return 0;
        }
    }
    int inserted = rt_persistent_raw_insert_raw_locked((uintptr_t)ptr, bytes);
    rt_persistent_raw_lock_release();
    return inserted;
}

static void rt_persistent_raw_unregister_locked(void* ptr) {
    uintptr_t raw = (uintptr_t)ptr;
    if (!raw || raw == RT_PERSISTENT_RAW_TOMBSTONE ||
            rt_persistent_raw_cap == 0 || rt_persistent_raw_len == 0) {
        return;
    }
    size_t mask = rt_persistent_raw_cap - 1;
    size_t i = PERSISTENT_RAW_REGISTRY_HASH(raw) & mask;
    for (size_t probes = 0; probes < rt_persistent_raw_cap; probes++) {
        uintptr_t entry = rt_persistent_raw_allocs[i].ptr;
        if (entry == 0) return;
        if (entry == raw) {
            rt_persistent_raw_allocs[i].ptr = RT_PERSISTENT_RAW_TOMBSTONE;
            rt_persistent_raw_allocs[i].bytes = 0;
            rt_persistent_raw_len--;
            rt_persistent_raw_tombs++;
            return;
        }
        i = (i + 1) & mask;
    }
}

static void rt_persistent_raw_unregister(void* ptr) {
    if (!ptr) return;
    rt_persistent_raw_lock_acquire();
    rt_persistent_raw_unregister_locked(ptr);
    rt_persistent_raw_lock_release();
}

static int rt_persistent_raw_lookup_size(void* ptr, size_t* bytes_out) {
    uintptr_t raw = (uintptr_t)ptr;
    if (!raw || raw == RT_PERSISTENT_RAW_TOMBSTONE) return 0;
    int found = 0;
    rt_persistent_raw_read_lock_acquire();
    if (rt_persistent_raw_cap != 0 && rt_persistent_raw_len != 0) {
        size_t mask = rt_persistent_raw_cap - 1;
        size_t i = PERSISTENT_RAW_REGISTRY_HASH(raw) & mask;
        for (size_t probes = 0; probes < rt_persistent_raw_cap; probes++) {
            uintptr_t entry = rt_persistent_raw_allocs[i].ptr;
            if (entry == 0) break;
            if (entry == raw) {
                if (bytes_out) *bytes_out = rt_persistent_raw_allocs[i].bytes;
                found = 1;
                break;
            }
            i = (i + 1) & mask;
        }
    }
    rt_persistent_raw_read_lock_release();
    return found;
}
