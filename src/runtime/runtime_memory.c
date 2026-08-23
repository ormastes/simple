/*
 * Simple Runtime — Memory FFI Functions
 *
 * C equivalents of src/compiler_rust/runtime/src/value/ffi/memory.rs.
 * Build: cc -c -fPIC -O2 -std=gnu11 runtime_memory.c -o runtime_memory.o
 */

#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#if defined(_WIN32)
#include <windows.h>
#else
#include <pthread.h>
#endif

#include "runtime_memory_guard.h"

#if defined(_MSC_VER)
#define RT_MEMORY_THREAD_LOCAL __declspec(thread)
#else
#define RT_MEMORY_THREAD_LOCAL _Thread_local
#endif

typedef struct RtTransientRawAlloc {
    uintptr_t ptr;
    size_t bytes;
} RtTransientRawAlloc;

static RT_MEMORY_THREAD_LOCAL RtTransientRawAlloc* rt_transient_raw_allocs = NULL;
static RT_MEMORY_THREAD_LOCAL size_t rt_transient_raw_cap = 0;
static RT_MEMORY_THREAD_LOCAL size_t rt_transient_raw_len = 0;
static RT_MEMORY_THREAD_LOCAL size_t rt_transient_raw_tombs = 0;
static RT_MEMORY_THREAD_LOCAL int rt_transient_raw_active = 0;
static RT_MEMORY_THREAD_LOCAL int rt_transient_raw_paused = 0;

#define RT_TRANSIENT_RAW_TOMBSTONE ((uintptr_t)1)
#define RT_TRANSIENT_RAW_OWNED_BIT ((size_t)1 << (sizeof(size_t) * CHAR_BIT - 1))
#define RT_TRANSIENT_RAW_SIZE_MASK (~RT_TRANSIENT_RAW_OWNED_BIT)

void rt_free(uint8_t* ptr);

static size_t rt_transient_raw_hash(uintptr_t ptr) {
    uint64_t value = (uint64_t)ptr;
    value ^= value >> 33;
    value *= 0xff51afd7ed558ccdULL;
    value ^= value >> 33;
    return (size_t)value;
}

static int rt_transient_raw_insert(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_transient_raw_cap - 1;
    size_t index = rt_transient_raw_hash(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (;;) {
        uintptr_t entry = rt_transient_raw_allocs[index].ptr;
        if (entry == 0) {
            size_t target = first_tomb == SIZE_MAX ? index : first_tomb;
            rt_transient_raw_allocs[target] = (RtTransientRawAlloc){ptr, bytes};
            if (first_tomb != SIZE_MAX) rt_transient_raw_tombs--;
            rt_transient_raw_len++;
            return 1;
        }
        if (entry == RT_TRANSIENT_RAW_TOMBSTONE) {
            if (first_tomb == SIZE_MAX) first_tomb = index;
        } else if (entry == ptr) {
            rt_transient_raw_allocs[index].bytes = bytes;
            return 1;
        }
        index = (index + 1) & mask;
    }
}

/* Rehash into a table of exactly `next_cap` slots. `next_cap` may EQUAL the
 * current capacity: linear probing cannot purge tombstones in place, so a
 * same-capacity rehash through a fresh table is the only way to reclaim them.
 * Live entries keep their `bytes` word verbatim, so the OWNED bit and the
 * size field survive a resize unchanged. */
static int rt_transient_raw_resize(size_t next_cap) {
    if (next_cap == 0) return 0;
    if (next_cap > SIZE_MAX / sizeof(RtTransientRawAlloc)) return 0;
    RtTransientRawAlloc* fresh = (RtTransientRawAlloc*)calloc(
        next_cap, sizeof(RtTransientRawAlloc));
    if (!fresh) return 0;
    RtTransientRawAlloc* old = rt_transient_raw_allocs;
    size_t old_cap = rt_transient_raw_cap;
    rt_transient_raw_allocs = fresh;
    rt_transient_raw_cap = next_cap;
    rt_transient_raw_len = 0;
    rt_transient_raw_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t ptr = old[i].ptr;
        if (ptr != 0 && ptr != RT_TRANSIENT_RAW_TOMBSTONE) {
            rt_transient_raw_insert(ptr, old[i].bytes);
        }
    }
    free(old);
    return 1;
}

static RtTransientRawAlloc* rt_transient_raw_lookup(uintptr_t ptr) {
    if (!ptr || rt_transient_raw_cap == 0) return NULL;
    size_t mask = rt_transient_raw_cap - 1;
    size_t index = rt_transient_raw_hash(ptr) & mask;
    for (;;) {
        uintptr_t entry = rt_transient_raw_allocs[index].ptr;
        if (entry == 0) return NULL;
        if (entry == ptr) return &rt_transient_raw_allocs[index];
        index = (index + 1) & mask;
    }
}

static int rt_transient_raw_register(void* ptr, size_t bytes) {
    if (!ptr || !rt_transient_raw_active) return ptr != NULL;
    if (bytes > RT_TRANSIENT_RAW_SIZE_MASK) return 0;
    if ((rt_transient_raw_len + rt_transient_raw_tombs + 1) * 10
            >= rt_transient_raw_cap * 7) {
        size_t next_cap = rt_transient_raw_cap == 0 ? 256 : rt_transient_raw_cap * 2;
        /* PERF (stage3_hir_imports_memory_explosion_driver_riscv_gen2):
         * tombstones count as occupancy above because they lengthen probe
         * chains exactly as live entries do -- but rt_free erases in place
         * (see rt_free below) and rt_realloc frees the old block on EVERY
         * array/dict growth, so a long-lived transient scope accumulates
         * millions of tombstones while very few blocks are live. Doubling on
         * those made capacity track CUMULATIVE churn instead of the live set,
         * and every rt_alloc then probed an ever-larger sparse table. Purge
         * them at the SAME capacity instead. Identical guard, and identical
         * reason, to rt_core_register_immortal_ptr in runtime_native.c. */
        if (rt_transient_raw_cap != 0 &&
            rt_transient_raw_tombs > rt_transient_raw_len &&
            (rt_transient_raw_len + 1) * 10 < rt_transient_raw_cap * 5) {
            next_cap = rt_transient_raw_cap;
        }
        if (!rt_transient_raw_resize(next_cap)) return 0;
    }
    size_t stored = bytes |
        (rt_transient_raw_paused ? 0 : RT_TRANSIENT_RAW_OWNED_BIT);
    return rt_transient_raw_insert((uintptr_t)ptr, stored);
}

static void rt_transient_raw_erase(void* ptr) {
    RtTransientRawAlloc* entry = rt_transient_raw_lookup((uintptr_t)ptr);
    if (!entry) return;
    entry->ptr = RT_TRANSIENT_RAW_TOMBSTONE;
    entry->bytes = 0;
    rt_transient_raw_len--;
    rt_transient_raw_tombs++;
}

int32_t rt_transient_raw_scope_begin(void) {
    if (rt_transient_raw_active || rt_transient_raw_len != 0) return 0;
    rt_transient_raw_active = 1;
    rt_transient_raw_paused = 0;
    return 1;
}

int32_t rt_transient_raw_scope_pause(void) {
    if (!rt_transient_raw_active) return 0;
    rt_transient_raw_paused = 1;
    return 1;
}

int64_t rt_transient_raw_words(
    int64_t value, const uintptr_t** words, uintptr_t* canonical_ptr) {
    uintptr_t ptr = ((uintptr_t)value) & ~(uintptr_t)7;
    RtTransientRawAlloc* entry = rt_transient_raw_lookup(ptr);
    if (!entry) return -1;
    if (words) *words = (const uintptr_t*)ptr;
    if (canonical_ptr) *canonical_ptr = ptr;
    return (int64_t)((entry->bytes & RT_TRANSIENT_RAW_SIZE_MASK) / sizeof(uintptr_t));
}

int32_t rt_transient_raw_promote(uintptr_t ptr) {
    RtTransientRawAlloc* entry = rt_transient_raw_lookup(ptr & ~(uintptr_t)7);
    if (!entry) return 0;
    entry->bytes &= RT_TRANSIENT_RAW_SIZE_MASK;
    return 1;
}

int32_t rt_transient_raw_scope_end(void) {
    if (!rt_transient_raw_active) return 0;
    for (size_t i = 0; i < rt_transient_raw_cap; i++) {
        RtTransientRawAlloc* entry = &rt_transient_raw_allocs[i];
        if (entry->ptr == 0 || entry->ptr == RT_TRANSIENT_RAW_TOMBSTONE) continue;
        if (entry->bytes & RT_TRANSIENT_RAW_OWNED_BIT) {
            rt_free((uint8_t*)entry->ptr);
        }
    }
    /* PERF (stage3_hir_imports_memory_explosion_driver_riscv_gen2): the table
     * used to be memset and RETAINED at its high-water capacity. Scopes are
     * per-source (driver_hir_pipeline_lowering.spl:72..113), so one large
     * module's capacity was then paid by EVERY later module: an O(cap) scan
     * plus a full memset per scope end, and -- the part the profile shows --
     * one random probe into a huge sparse array on every single rt_alloc.
     * Release it instead. Post-end this is observationally identical to the
     * all-zero table: rt_transient_raw_lookup returns NULL for cap == 0
     * (:98), which is what every erase/promote/words caller already handles,
     * and rt_transient_raw_register re-seeds at 256 through the cap == 0 arm.
     * A small table is kept as-is so an ordinary module pays no extra calloc. */
    if (rt_transient_raw_cap > 4096) {
        free(rt_transient_raw_allocs);
        rt_transient_raw_allocs = NULL;
        rt_transient_raw_cap = 0;
    } else if (rt_transient_raw_cap != 0) {
        memset(rt_transient_raw_allocs, 0,
            rt_transient_raw_cap * sizeof(RtTransientRawAlloc));
    }
    rt_transient_raw_len = 0;
    rt_transient_raw_tombs = 0;
    rt_transient_raw_active = 0;
    rt_transient_raw_paused = 0;
    return 1;
}

/*
 * Hardened debug allocator (mirrors the hosted quarantine in
 * interpreter_extern/memory.rs; see
 * doc/05_design/runtime/memory_analysis/m2_guard_and_harden_design.md §3).
 *
 * Gated by SIMPLE_MEM_HARDEN=1, read via getenv exactly once (cached in a
 * static int; the result is fixed for the life of the process). When
 * enabled, every rt_alloc grows the block by one hidden size_t header so
 * rt_free can recover the block's length without changing the rt_free ABI.
 * rt_free then poisons the user bytes with 0xDE and defers the real free()
 * into a small fixed-size FIFO quarantine ring instead of releasing the
 * block immediately; a double-free of a pointer still sitting in the ring
 * is refused (no-op) rather than acted on twice.
 */

#define RT_MEM_HARDEN_POISON_BYTE 0xDE
#define RT_MEM_HARDEN_HEADER_BYTES (sizeof(size_t))
#define RT_MEM_QUARANTINE_SLOTS 64

typedef struct RtMemQuarantineSlot {
    uint8_t* user_ptr;  /* pointer as handed out by rt_alloc / seen by rt_free */
    uint8_t* base_ptr;  /* real malloc'd base (user_ptr - header); NULL = empty slot */
    size_t size;        /* user-visible size, for poisoning + tamper scan */
} RtMemQuarantineSlot;

static RtMemQuarantineSlot rt_mem_quarantine[RT_MEM_QUARANTINE_SLOTS];
static size_t rt_mem_quarantine_write = 0;

static int rt_mem_harden_enabled(void) {
    static int cached = -1;
    if (cached < 0) {
        const char* v = getenv("SIMPLE_MEM_HARDEN");
        cached = (v != NULL && v[0] == '1' && v[1] == '\0') ? 1 : 0;
    }
    return cached;
}

static int rt_mem_quarantine_contains(uint8_t* ptr) {
    for (size_t i = 0; i < RT_MEM_QUARANTINE_SLOTS; i++) {
        if (rt_mem_quarantine[i].base_ptr != NULL && rt_mem_quarantine[i].user_ptr == ptr) {
            return 1;
        }
    }
    return 0;
}

/* FIFO by construction: slot index cycles 0..N-1 as writes happen, so the
 * occupant being overwritten at index i is always the one inserted exactly
 * (a multiple of RT_MEM_QUARANTINE_SLOTS) writes ago -- the oldest entry
 * currently mapped to that bucket. */
static void rt_mem_quarantine_push(uint8_t* user_ptr, uint8_t* base_ptr, size_t size) {
    size_t idx = rt_mem_quarantine_write % RT_MEM_QUARANTINE_SLOTS;
    RtMemQuarantineSlot* slot = &rt_mem_quarantine[idx];
    if (slot->base_ptr != NULL) {
        free(slot->base_ptr);
    }
    slot->user_ptr = user_ptr;
    slot->base_ptr = base_ptr;
    slot->size = size;
    rt_mem_quarantine_write++;
}

/* Scans the quarantine ring for blocks whose bytes are no longer all
 * 0xDE poison -- i.e. something wrote to memory after it was "freed".
 * Returns the number of tampered blocks (not tampered bytes). */
int64_t rt_mem_guard_stats(void) {
    return rt_mem_guard_stats_native();
}

int64_t rt_mem_harden_check_native(void) {
    int64_t tampered = 0;
    for (size_t i = 0; i < RT_MEM_QUARANTINE_SLOTS; i++) {
        RtMemQuarantineSlot* slot = &rt_mem_quarantine[i];
        if (slot->base_ptr == NULL) continue;
        for (size_t j = 0; j < slot->size; j++) {
            if (slot->user_ptr[j] != (uint8_t)RT_MEM_HARDEN_POISON_BYTE) {
                tampered++;
                break;
            }
        }
    }
    return tampered;
}

uint8_t* rt_alloc(int64_t size) {
    if (size <= 0) return NULL;
    if (rt_mem_guard_should_sample((size_t)size)) {
        void* guarded = rt_mem_guard_alloc_sampled((size_t)size);
        if (guarded != NULL) return (uint8_t*)guarded;
        /* mmap/mprotect failed (or the slot table is full) -- fall through
         * to the normal allocator below rather than returning NULL for a
         * sampling decision that isn't itself an OOM. */
    }
    if (rt_mem_harden_enabled()) {
        size_t total = (size_t)size + RT_MEM_HARDEN_HEADER_BYTES;
        uint8_t* base = (uint8_t*)calloc(1, total);
        if (!base) return NULL;
        *(size_t*)base = (size_t)size;
        uint8_t* user = base + RT_MEM_HARDEN_HEADER_BYTES;
        if (!rt_transient_raw_register(user, (size_t)size)) {
            free(base);
            return NULL;
        }
        return user;
    }
    uint8_t* ptr = (uint8_t*)calloc(1, (size_t)size);
    if (ptr && !rt_transient_raw_register(ptr, (size_t)size)) {
        free(ptr);
        return NULL;
    }
    return ptr;
}

/* Struct field accesses are emitted as direct native loads/stores.  Keep a
 * registry of allocations that may legally back those accesses so forged or
 * stale tagged values are rejected before dereference. */
typedef struct RtStructAllocation {
    uintptr_t ptr;
    size_t bytes;
} RtStructAllocation;

#define RT_STRUCT_ALLOC_TOMBSTONE ((uintptr_t)1)
#define RT_STRUCT_ALLOC_MAX_CAP ((size_t)1 << 22)

static RtStructAllocation* rt_struct_allocs = NULL;
static size_t rt_struct_alloc_cap = 0;
static size_t rt_struct_alloc_len = 0;
static size_t rt_struct_alloc_tombs = 0;
#if defined(_WIN32)
static SRWLOCK rt_struct_alloc_lock = SRWLOCK_INIT;
#else
static pthread_rwlock_t rt_struct_alloc_lock = PTHREAD_RWLOCK_INITIALIZER;
#endif

static void rt_struct_alloc_lock_acquire(void) {
#if defined(_WIN32)
    AcquireSRWLockExclusive(&rt_struct_alloc_lock);
#else
    pthread_rwlock_wrlock(&rt_struct_alloc_lock);
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

static int rt_struct_alloc_insert_raw(uintptr_t ptr, size_t bytes) {
    size_t mask = rt_struct_alloc_cap - 1;
    size_t index = rt_transient_raw_hash(ptr) & mask;
    size_t first_tomb = SIZE_MAX;
    for (;;) {
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
}

static int rt_struct_alloc_resize(size_t next_cap) {
    if (next_cap > RT_STRUCT_ALLOC_MAX_CAP ||
            next_cap > SIZE_MAX / sizeof(RtStructAllocation)) return 0;
    RtStructAllocation* fresh = (RtStructAllocation*)calloc(
        next_cap, sizeof(RtStructAllocation));
    if (!fresh) return 0;
    RtStructAllocation* old = rt_struct_allocs;
    size_t old_cap = rt_struct_alloc_cap;
    rt_struct_allocs = fresh;
    rt_struct_alloc_cap = next_cap;
    rt_struct_alloc_len = 0;
    rt_struct_alloc_tombs = 0;
    for (size_t i = 0; i < old_cap; i++) {
        uintptr_t ptr = old[i].ptr;
        if (ptr != 0 && ptr != RT_STRUCT_ALLOC_TOMBSTONE) {
            rt_struct_alloc_insert_raw(ptr, old[i].bytes);
        }
    }
    free(old);
    return 1;
}

static int rt_struct_alloc_register(void* ptr, size_t bytes) {
    if (!ptr) return 0;
    rt_struct_alloc_lock_acquire();
    int ok = rt_struct_alloc_cap != 0 || rt_struct_alloc_resize(256);
    if (ok && (rt_struct_alloc_len + rt_struct_alloc_tombs + 1) * 10
            >= rt_struct_alloc_cap * 7) {
        if (rt_struct_alloc_cap < RT_STRUCT_ALLOC_MAX_CAP) {
            ok = rt_struct_alloc_resize(rt_struct_alloc_cap * 2);
        } else if (rt_struct_alloc_tombs > rt_struct_alloc_len / 4) {
            ok = rt_struct_alloc_resize(rt_struct_alloc_cap);
        } else if (rt_struct_alloc_len + 1 >= rt_struct_alloc_cap) {
            ok = 0;
        }
    }
    if (ok) ok = rt_struct_alloc_insert_raw((uintptr_t)ptr, bytes);
    rt_struct_alloc_lock_release();
    return ok;
}

static void rt_struct_alloc_unregister(void* ptr) {
    if (!ptr) return;
    rt_struct_alloc_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t index = rt_transient_raw_hash((uintptr_t)ptr) & mask;
        for (;;) {
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
    rt_struct_alloc_lock_release();
}

static int rt_struct_alloc_lookup_size(void* ptr, size_t* bytes_out) {
    if (!ptr) return 0;
    int found = 0;
    rt_struct_alloc_read_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t index = rt_transient_raw_hash((uintptr_t)ptr) & mask;
        for (;;) {
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

uint8_t* rt_struct_alloc(int64_t size) {
    if (size <= 0) return NULL;
    uint8_t* ptr = rt_alloc(size);
    if (ptr && !rt_struct_alloc_register(ptr, (size_t)size)) {
        rt_free(ptr);
        return NULL;
    }
    return ptr;
}

int8_t rt_struct_receiver_valid(
    int64_t receiver, int64_t byte_offset, int64_t access_width) {
    if (receiver == 0 || byte_offset < 0 || access_width <= 0) return 0;
    uintptr_t ptr = ((uintptr_t)receiver) & ~(uintptr_t)7;
    if (ptr == 0) return 0;

    int8_t valid = 0;
    rt_struct_alloc_read_lock_acquire();
    if (rt_struct_alloc_cap != 0) {
        size_t mask = rt_struct_alloc_cap - 1;
        size_t index = rt_transient_raw_hash(ptr) & mask;
        for (;;) {
            uintptr_t entry = rt_struct_allocs[index].ptr;
            if (entry == 0) break;
            if (entry == ptr) {
                size_t offset = (size_t)byte_offset;
                size_t width = (size_t)access_width;
                size_t bytes = rt_struct_allocs[index].bytes;
                valid = offset <= bytes && width <= bytes - offset;
                break;
            }
            index = (index + 1) & mask;
        }
    }
    rt_struct_alloc_read_lock_release();
    return valid;
}

void* rt_realloc(void* ptr, int64_t size) {
    if (size < 0) return NULL;
    if (!ptr) return rt_alloc(size);
    if (size == 0) {
        rt_free((uint8_t*)ptr);
        return NULL;
    }

    size_t old_size = 0;
    if (rt_struct_alloc_lookup_size(ptr, &old_size)) {
        void* next = rt_struct_alloc(size);
        if (!next) return NULL;
        memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
        rt_free((uint8_t*)ptr);
        return next;
    }

    RtMemGuardSlot* guard_slot = rt_mem_guard_find(ptr);
    if (guard_slot != NULL) {
        old_size = guard_slot->size;
        void* next = rt_alloc(size);
        if (!next) return NULL;
        memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
        rt_free((uint8_t*)ptr);
        return next;
    }

    if (rt_mem_harden_enabled()) {
        uint8_t* base = (uint8_t*)ptr - RT_MEM_HARDEN_HEADER_BYTES;
        old_size = *(size_t*)base;
        void* next = rt_alloc(size);
        if (!next) return NULL;
        memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
        rt_free((uint8_t*)ptr);
        return next;
    }

    RtTransientRawAlloc* tracked = rt_transient_raw_lookup((uintptr_t)ptr);
    if (tracked != NULL) {
        old_size = tracked->bytes & RT_TRANSIENT_RAW_SIZE_MASK;
        void* next = rt_alloc(size);
        if (!next) return NULL;
        memcpy(next, ptr, old_size < (size_t)size ? old_size : (size_t)size);
        rt_free((uint8_t*)ptr);
        return next;
    }

    return realloc(ptr, (size_t)size);
}

void rt_free(uint8_t* ptr) {
    if (!ptr) return;
    rt_struct_alloc_unregister(ptr);
    if (rt_mem_guard_is_slot(ptr)) {
        /* Guard slots are never transient-scope-owned and never enter the
         * harden quarantine -- guard_free_sampled already PROT_NONEs the
         * whole mapping, which is the stronger (page-fault) protection. */
        rt_mem_guard_free_sampled(ptr);
        return;
    }
    if (rt_mem_harden_enabled()) {
        if (rt_mem_quarantine_contains(ptr)) {
            /* Double free of a quarantined block: refused, not acted on. */
            return;
        }
        rt_transient_raw_erase(ptr);
        uint8_t* base = ptr - RT_MEM_HARDEN_HEADER_BYTES;
        size_t size = *(size_t*)base;
        memset(ptr, RT_MEM_HARDEN_POISON_BYTE, size);
        rt_mem_quarantine_push(ptr, base, size);
        return;
    }
    rt_transient_raw_erase(ptr);
    free(ptr);
}

int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) {
    if (addr <= 0 || offset < 0) abort();
    int64_t value;
    memcpy(&value, (char*)(uintptr_t)addr + offset, sizeof(value));
    return value;
}

int64_t rt_ptr_read_u8(int64_t addr, int64_t offset) {
    if (addr <= 0 || offset < 0) abort();
    return (int64_t)*(uint8_t*)((char*)(uintptr_t)addr + offset);
}

int32_t rt_ptr_read_i32(int64_t addr, int64_t offset) {
    if (addr <= 0 || offset < 0) abort();
    int32_t value;
    memcpy(&value, (char*)(uintptr_t)addr + offset, sizeof(value));
    return value;
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    if (addr <= 0 || offset < 0) abort();
    *(uint8_t*)((char*)(uintptr_t)addr + offset) = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    if (addr <= 0 || offset < 0) abort();
    *(int32_t*)((char*)(uintptr_t)addr + offset) = value;
}

void rt_ptr_write_i16(int64_t addr, int64_t offset, int32_t value) {
    if (addr <= 0 || offset < 0) abort();
    int16_t narrowed = (int16_t)value;
    memcpy((char*)(uintptr_t)addr + offset, &narrowed, sizeof(narrowed));
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    if (addr <= 0 || offset < 0) abort();
    *(int64_t*)((char*)(uintptr_t)addr + offset) = value;
}

/* All-i64 bulk copy: memcpy(addr + offset, src, len).
 *
 * The Rust runtime shim `rt_ptr_write_bytes_raw_shim`
 * (src/compiler_rust/runtime/src/value/sffi/memory.rs) declares this symbol
 * extern and its comment asserted "the C runtime already exports
 * rt_ptr_write_bytes_raw" -- it did not, and the seed failed to LINK with
 * `rust-lld: error: undefined symbol: rt_ptr_write_bytes_raw`. Defined here,
 * next to the other rt_ptr_write_* primitives.
 * Returns the number of bytes written, 0 for a rejected descriptor. */
int64_t rt_ptr_write_bytes_raw(int64_t addr, int64_t offset, const uint8_t* src, int64_t len) {
    if (len == 0) return 0;
    if (addr <= 0 || (intptr_t)src <= 0 || offset < 0 || len < 0) abort();
    memcpy((char*)(uintptr_t)addr + offset, src, (size_t)len);
    return len;
}

int64_t spl_f64_to_bits(double value) {
    int64_t bits;
    memcpy(&bits, &value, sizeof(bits));
    return bits;
}

int32_t spl_i64_is_zero(int64_t value) {
    return value == 0 ? 1 : 0;
}

uint8_t* rt_memset(uint8_t* dst, int8_t val, int64_t n) {
    memset(dst, (unsigned char)val, (size_t)n);
    return dst;
}

uint8_t* rt_memcpy(uint8_t* dst, const uint8_t* src, int64_t n) {
    memcpy(dst, src, (size_t)n);
    return dst;
}

uint8_t* copy_mem(uint8_t* dst, const uint8_t* src, int64_t n) {
    return rt_memcpy(dst, src, n);
}

/*
 * Memory-profiling capability surface.
 * Mirrors src/compiler_rust/compiler/src/interpreter_extern/memory.rs.
 * Feature bits: bit0 = header-bytes counters, bit1 = hosted-alloc-metadata,
 * bit2 = real-memory-usage. The C runtime frees via libc directly (no hosted
 * metadata map) and implements none of the profiling counters here, so the
 * feature mask is 0; only the ABI version is shared.
 */
int64_t rt_mem_profile_abi_version(void) {
    return 1;
}

int64_t rt_mem_profile_features(void) {
    return 0;
}
