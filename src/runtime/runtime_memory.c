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

static int rt_transient_raw_grow(void) {
    size_t next_cap = rt_transient_raw_cap == 0 ? 256 : rt_transient_raw_cap * 2;
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
            >= rt_transient_raw_cap * 7 && !rt_transient_raw_grow()) {
        return 0;
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
        if (entry->bytes & RT_TRANSIENT_RAW_OWNED_BIT) free((void*)entry->ptr);
    }
    if (rt_transient_raw_cap != 0) {
        memset(rt_transient_raw_allocs, 0,
            rt_transient_raw_cap * sizeof(RtTransientRawAlloc));
    }
    rt_transient_raw_len = 0;
    rt_transient_raw_tombs = 0;
    rt_transient_raw_active = 0;
    rt_transient_raw_paused = 0;
    return 1;
}

uint8_t* rt_alloc(int64_t size) {
    if (size <= 0) return NULL;
    uint8_t* ptr = (uint8_t*)calloc(1, (size_t)size);
    if (ptr && !rt_transient_raw_register(ptr, (size_t)size)) {
        free(ptr);
        return NULL;
    }
    return ptr;
}

void rt_free(uint8_t* ptr) {
    rt_transient_raw_erase(ptr);
    free(ptr);
}

int64_t rt_ptr_read_i64(int64_t addr, int64_t offset) {
    return *(int64_t*)((char*)(uintptr_t)addr + offset);
}

int32_t rt_ptr_read_i32(int64_t addr, int64_t offset) {
    return *(int32_t*)((char*)(uintptr_t)addr + offset);
}

void rt_ptr_write_u8(int64_t addr, int64_t offset, int64_t value) {
    *(uint8_t*)((char*)(uintptr_t)addr + offset) = (uint8_t)value;
}

void rt_ptr_write_i32(int64_t addr, int64_t offset, int32_t value) {
    *(int32_t*)((char*)(uintptr_t)addr + offset) = value;
}

void rt_ptr_write_i64(int64_t addr, int64_t offset, int64_t value) {
    *(int64_t*)((char*)(uintptr_t)addr + offset) = value;
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
