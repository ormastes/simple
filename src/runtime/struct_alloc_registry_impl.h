/* struct_alloc_registry_impl.h -- private struct-allocation registry shared by
 * runtime_memory.c and runtime_native.c.
 *
 * Not a public header: include it exactly once, from one translation unit,
 * after <stdint.h>/<stdlib.h>/<string.h> and the platform lock headers
 * (<windows.h> on _WIN32, <pthread.h> elsewhere). Everything here is static,
 * so both runtimes may be linked into one image.
 *
 * Includer knobs:
 *   STRUCT_ALLOC_REGISTRY_HASH(ptr)      required: pointer hash (uintptr_t -> size_t)
 *   STRUCT_ALLOC_REGISTRY_TEST_EXPORTS   define to emit the rt_struct_registry_*
 *                                        accessors when SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING
 *   STRUCT_ALLOC_REGISTRY_COUNT_WRITE_LOCKS  define to count exclusive acquisitions
 *                                        (exports spl_struct_registry_write_locks_v1)
 */
#ifndef SIMPLE_STRUCT_ALLOC_REGISTRY_IMPL_H
#define SIMPLE_STRUCT_ALLOC_REGISTRY_IMPL_H

#ifndef STRUCT_ALLOC_REGISTRY_HASH
#error "define STRUCT_ALLOC_REGISTRY_HASH(ptr) before including struct_alloc_registry_impl.h"
#endif

/* Struct field accesses are emitted as direct native loads/stores.  Keep a
 * registry of allocations that may legally back those accesses so forged or
 * stale tagged values are rejected before dereference. */
typedef struct RtStructAllocation {
    uintptr_t ptr;
    size_t bytes;
} RtStructAllocation;

#define RT_STRUCT_ALLOC_TOMBSTONE ((uintptr_t)1)

static RtStructAllocation* rt_struct_allocs = NULL;
static size_t rt_struct_alloc_cap = 0;
static size_t rt_struct_alloc_len = 0;
static size_t rt_struct_alloc_tombs = 0;
static size_t rt_struct_alloc_failures = 0;
static size_t rt_struct_alloc_max_cap_for_test = 0;
#if defined(_WIN32)
static SRWLOCK rt_struct_alloc_lock = SRWLOCK_INIT;
#else
static pthread_rwlock_t rt_struct_alloc_lock = PTHREAD_RWLOCK_INITIALIZER;
#endif

#if defined(SIMPLE_RUNTIME_STRUCT_REGISTRY_TESTING) && defined(STRUCT_ALLOC_REGISTRY_TEST_EXPORTS)
int64_t rt_struct_registry_len(void) { return (int64_t)rt_struct_alloc_len; }
int64_t rt_struct_registry_cap(void) { return (int64_t)rt_struct_alloc_cap; }
int64_t rt_struct_registry_failures(void) { return (int64_t)rt_struct_alloc_failures; }
void rt_struct_registry_set_max_cap_for_test(size_t max_cap) {
    rt_struct_alloc_max_cap_for_test = max_cap;
}
#endif

#if defined(STRUCT_ALLOC_REGISTRY_COUNT_WRITE_LOCKS)
/* Test-only: exclusive acquisitions of the struct registry lock, so a spec can
 * pin that scope-end reclaim takes it per batch, not per allocation. */
static int64_t rt_struct_alloc_write_locks = 0;
int64_t spl_struct_registry_write_locks_v1(void) { return rt_struct_alloc_write_locks; }
#endif

static void rt_struct_alloc_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockExclusive(&rt_struct_alloc_lock);
#else
    pthread_rwlock_wrlock(&rt_struct_alloc_lock);
#endif
#if defined(STRUCT_ALLOC_REGISTRY_COUNT_WRITE_LOCKS)
    rt_struct_alloc_write_locks++;
#endif
}

static void rt_struct_alloc_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockExclusive(&rt_struct_alloc_lock);
#else
    pthread_rwlock_unlock(&rt_struct_alloc_lock);
#endif
}

static void rt_struct_alloc_read_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockShared(&rt_struct_alloc_lock);
#else
    pthread_rwlock_rdlock(&rt_struct_alloc_lock);
#endif
}

static void rt_struct_alloc_read_lock_release(void) {
#if defined(_WIN32)
    ReleaseSRWLockShared(&rt_struct_alloc_lock);
#else
    pthread_rwlock_unlock(&rt_struct_alloc_lock);
#endif
}

static size_t rt_struct_alloc_hash(uintptr_t ptr) {
    return STRUCT_ALLOC_REGISTRY_HASH(ptr);
}

static size_t rt_struct_alloc_load_limit(size_t cap) {
    size_t limit = cap - (cap / 4);
    if (limit >= cap && cap > 0) limit = cap - 1;
    return limit;
}

static size_t rt_struct_alloc_next_cap(size_t current) {
    const size_t max_entries = SIZE_MAX / sizeof(RtStructAllocation);
    size_t ceiling = rt_struct_alloc_max_cap_for_test != 0 &&
            rt_struct_alloc_max_cap_for_test < max_entries
        ? rt_struct_alloc_max_cap_for_test
        : max_entries;
    if (current == 0) return ceiling < 256 ? 0 : 256;
    if (current >= ceiling || current > max_entries / 2) return 0;
    size_t next = current * 2;
    return next > ceiling ? 0 : next;
}

static int rt_struct_alloc_needs_rehash(size_t cap) {
    size_t limit = rt_struct_alloc_load_limit(cap);
    if (rt_struct_alloc_len >= limit) return 1;
    size_t remaining = limit - rt_struct_alloc_len;
    return rt_struct_alloc_tombs >= remaining - 1;
}

static void rt_struct_alloc_record_failure(void) {
    if (rt_struct_alloc_failures != SIZE_MAX) {
        rt_struct_alloc_failures++;
    }
}

static int rt_struct_alloc_insert_raw(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_struct_alloc_cap - 1;
    size_t index = rt_struct_alloc_hash(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (size_t probes = 0; probes < rt_struct_alloc_cap; probes++) {
        uintptr_t entry = rt_struct_allocs[index].ptr;
        if (entry == 0) {
            size_t target = first_tomb == SIZE_MAX ? index : first_tomb;
            rt_struct_allocs[target] = (RtStructAllocation){ptr, bytes};
            if (first_tomb != SIZE_MAX) rt_struct_alloc_tombs--;
            rt_struct_alloc_len++;
            return 1;
        }
        if (entry == RT_STRUCT_ALLOC_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = index;
        } else if (entry == ptr) {
            rt_struct_allocs[index].bytes = bytes;
            return 1;
        }
        index = (index + 1) & mask;
    }
    if (first_tomb != SIZE_MAX) {
        rt_struct_allocs[first_tomb] = (RtStructAllocation){ptr, bytes};
        rt_struct_alloc_tombs--;
        rt_struct_alloc_len++;
        return 1;
    }
    return 0;
}

static int rt_struct_alloc_resize(size_t next_cap) {
    const size_t max_entries = SIZE_MAX / sizeof(RtStructAllocation);
    if (next_cap == 0 || next_cap > max_entries) return 0;
    if (rt_struct_alloc_max_cap_for_test != 0 &&
            next_cap > rt_struct_alloc_max_cap_for_test) return 0;
    RtStructAllocation* fresh = (RtStructAllocation*)rt_observed_calloc_v1(
        next_cap, sizeof(RtStructAllocation));
    if (!fresh) return 0;
    RtStructAllocation* old = rt_struct_allocs;
    size_t old_cap = rt_struct_alloc_cap;
    size_t old_len = rt_struct_alloc_len;
    size_t old_tombs = rt_struct_alloc_tombs;
    rt_struct_allocs = fresh;
    rt_struct_alloc_cap = next_cap;
    rt_struct_alloc_len = 0;
    rt_struct_alloc_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t ptr = old[i].ptr;
        if (ptr != 0 && ptr != RT_STRUCT_ALLOC_TOMBSTONE) {
            if (!rt_struct_alloc_insert_raw(ptr, old[i].bytes)) {
                free(fresh);
                rt_struct_allocs = old;
                rt_struct_alloc_cap = old_cap;
                rt_struct_alloc_len = old_len;
                rt_struct_alloc_tombs = old_tombs;
                return 0;
            }
        }
    }
    free(old);
    return 1;
}

static int rt_struct_alloc_register(void* ptr, size_t bytes) {
    if (!ptr) return 0;
    rt_struct_alloc_lock_acquire();
    int ok = 1;
    if (rt_struct_alloc_cap == 0) {
        size_t init_cap = rt_struct_alloc_next_cap(0);
        ok = init_cap != 0 && rt_struct_alloc_resize(init_cap);
    } else if (rt_struct_alloc_needs_rehash(rt_struct_alloc_cap)) {
        if ((rt_struct_alloc_len + 1) * 10 < rt_struct_alloc_cap * 6) {
            ok = rt_struct_alloc_resize(rt_struct_alloc_cap);
        } else {
            size_t grown = rt_struct_alloc_next_cap(rt_struct_alloc_cap);
            if (grown != 0) {
                ok = rt_struct_alloc_resize(grown);
            } else if (rt_struct_alloc_len + rt_struct_alloc_tombs + 1 >= rt_struct_alloc_cap) {
                if (rt_struct_alloc_tombs > 0 && rt_struct_alloc_len + 1 < rt_struct_alloc_cap) {
                    ok = rt_struct_alloc_resize(rt_struct_alloc_cap);
                } else if (rt_struct_alloc_len + 1 >= rt_struct_alloc_cap) {
                    ok = 0;
                }
            }
        }
    }
    if (ok && rt_struct_alloc_len + 1 >= rt_struct_alloc_cap) {
        ok = 0;
    }
    if (ok) ok = rt_struct_alloc_insert_raw((uintptr_t)ptr, bytes);
    if (!ok) rt_struct_alloc_record_failure();
    rt_struct_alloc_lock_release();
    return ok;
}

/* caller holds the struct registry write lock */
static void rt_struct_alloc_unregister_locked(void* ptr) {
    if (!ptr || rt_struct_alloc_cap == 0) return;
    size_t mask = rt_struct_alloc_cap - 1;
    size_t index = rt_struct_alloc_hash((uintptr_t)ptr) & mask;
    for (size_t probes = 0; probes < rt_struct_alloc_cap; probes++) {
        uintptr_t entry = rt_struct_allocs[index].ptr;
        if (entry == 0) break;
        if (entry == (uintptr_t)ptr) {
            rt_struct_allocs[index] =
                (RtStructAllocation){RT_STRUCT_ALLOC_TOMBSTONE, 0};
            rt_struct_alloc_len--;
            rt_struct_alloc_tombs++;
            break;
        }
        index = (index + 1) & mask;
    }
}

static void rt_struct_alloc_unregister(void* ptr) {
    if (!ptr) return;
    rt_struct_alloc_lock_acquire();
    rt_struct_alloc_unregister_locked(ptr);
    rt_struct_alloc_lock_release();
}

static int rt_struct_alloc_lookup_size(void* ptr, size_t* bytes_out) {
    if (!ptr) return 0;
    int found = 0;
    rt_struct_alloc_read_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t index = rt_struct_alloc_hash((uintptr_t)ptr) & mask;
        for (size_t probes = 0; probes < rt_struct_alloc_cap; probes++) {
            uintptr_t entry = rt_struct_allocs[index].ptr;
            if (entry == 0) break;
            if (entry == (uintptr_t)ptr) {
                *bytes_out = rt_struct_allocs[index].bytes;
                found = 1;
                break;
            }
            index = (index + 1) & mask;
        }
    }
    rt_struct_alloc_read_lock_release();
    return found;
}

#endif /* SIMPLE_STRUCT_ALLOC_REGISTRY_IMPL_H */
