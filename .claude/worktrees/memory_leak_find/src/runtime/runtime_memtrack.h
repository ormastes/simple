/*
 * Simple Runtime — Memory Allocation Tracker
 *
 * Near-zero overhead when disabled (single branch, predicted not-taken).
 * Tracks all C-level allocations through the runtime to detect leaks.
 *
 * Usage:
 *   spl_memtrack_enable();
 *   int64_t snap = spl_memtrack_snapshot();
 *   // ... allocate/free ...
 *   spl_memtrack_dump_since(snap, "/tmp/leaks.txt");
 *   spl_memtrack_disable();
 */

#ifndef SPL_RUNTIME_MEMTRACK_H
#define SPL_RUNTIME_MEMTRACK_H

#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

/* Ensure strdup is declared (POSIX, not in strict C11) */
#if !defined(_POSIX_C_SOURCE) && !defined(_GNU_SOURCE)
char* strdup(const char*);
#endif

#ifdef __cplusplus
extern "C" {
#endif

/* ===== Global enable flag (near-zero overhead when 0) ===== */
extern int g_memtrack_enabled;

/* ===== Control ===== */
void spl_memtrack_enable(void);
void spl_memtrack_disable(void);
int  spl_memtrack_is_enabled(void);

/* ===== Record / Unrecord ===== */
void spl_memtrack_record(void* ptr, int64_t size, const char* tag);
void spl_memtrack_unrecord(void* ptr);

/* ===== Snapshot ===== */
/* Returns monotonic snapshot ID (current alloc counter value) */
int64_t spl_memtrack_snapshot(void);

/* ===== Dump ===== */
/* Write allocations with alloc_id > snapshot_id to out_path.
 * Format: one line per entry: "ALLOC_ID SIZE TAG\n" */
void spl_memtrack_dump_since(int64_t snapshot_id, const char* out_path);

/* ===== Stats ===== */
int64_t spl_memtrack_live_count(void);
int64_t spl_memtrack_live_bytes(void);
void    spl_memtrack_reset(void);

/* ===== Snapshot comparison (in-memory, no file I/O) ===== */
/* Count live allocations with alloc_id > snapshot_id */
int64_t spl_memtrack_count_since(int64_t snapshot_id);
/* Sum bytes of live allocations with alloc_id > snapshot_id */
int64_t spl_memtrack_bytes_since(int64_t snapshot_id);

/* ===== Tracked allocation wrappers ===== */

static inline void* spl_rt_malloc(size_t size, const char* tag) {
    void* p = malloc(size);
    if (g_memtrack_enabled && p)
        spl_memtrack_record(p, (int64_t)size, tag);
    return p;
}

static inline void* spl_rt_calloc(size_t n, size_t sz, const char* tag) {
    void* p = calloc(n, sz);
    if (g_memtrack_enabled && p)
        spl_memtrack_record(p, (int64_t)(n * sz), tag);
    return p;
}

static inline void* spl_rt_realloc(void* ptr, size_t size, const char* tag) {
    if (g_memtrack_enabled && ptr)
        spl_memtrack_unrecord(ptr);
    void* p = realloc(ptr, size);
    if (g_memtrack_enabled && p)
        spl_memtrack_record(p, (int64_t)size, tag);
    return p;
}

static inline char* spl_rt_strdup(const char* s, const char* tag) {
    char* p = strdup(s);
    if (g_memtrack_enabled && p)
        spl_memtrack_record(p, (int64_t)(strlen(p) + 1), tag);
    return p;
}

static inline void spl_rt_free(void* ptr) {
    if (g_memtrack_enabled && ptr)
        spl_memtrack_unrecord(ptr);
    free(ptr);
}

/* ===== Convenience macros ===== */
#define SPL_MALLOC(size, tag)       spl_rt_malloc(size, tag)
#define SPL_CALLOC(n, sz, tag)      spl_rt_calloc(n, sz, tag)
#define SPL_REALLOC(ptr, size, tag) spl_rt_realloc(ptr, size, tag)
#define SPL_STRDUP(s, tag)          spl_rt_strdup(s, tag)
#define SPL_FREE(ptr)               spl_rt_free(ptr)

#ifdef __cplusplus
}
#endif

#endif /* SPL_RUNTIME_MEMTRACK_H */
