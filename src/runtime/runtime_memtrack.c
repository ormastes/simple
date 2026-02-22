/*
 * Simple Runtime — Memory Allocation Tracker Implementation
 *
 * Open-addressing hash table keyed by (void* ptr).
 * The hash table itself uses raw malloc/realloc (NOT tracked) to avoid recursion.
 */

#include "runtime_memtrack.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ===== Global state ===== */

int g_memtrack_enabled = 0;

/* ===== Hash table entry ===== */

typedef struct {
    void*       ptr;        /* key — NULL means empty slot */
    int64_t     size;
    const char* tag;        /* static string, not owned */
    int64_t     alloc_id;
    int         occupied;   /* 1 = live, 0 = empty, -1 = tombstone */
} MemtrackEntry;

/* ===== Hash table ===== */

#define MEMTRACK_INIT_CAP  4096
#define MEMTRACK_LOAD_PCT  70   /* grow at 70% load */

static MemtrackEntry* g_entries   = NULL;
static int64_t        g_cap       = 0;
static int64_t        g_len       = 0;      /* live entries */
static int64_t        g_tombstone = 0;
static int64_t        g_alloc_id  = 0;      /* monotonic counter */

/* ===== Hash function (pointer -> index) ===== */

static inline uint64_t ptr_hash(void* p) {
    uint64_t x = (uint64_t)(uintptr_t)p;
    /* Murmur-style mix */
    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;
    x ^= x >> 33;
    x *= 0xc4ceb9fe1a85ec53ULL;
    x ^= x >> 33;
    return x;
}

/* ===== Internal helpers ===== */

static void memtrack_ensure_init(void) {
    if (g_entries) return;
    g_cap = MEMTRACK_INIT_CAP;
    g_entries = (MemtrackEntry*)calloc((size_t)g_cap, sizeof(MemtrackEntry));
    g_len = 0;
    g_tombstone = 0;
}

static void memtrack_resize(int64_t new_cap) {
    MemtrackEntry* old = g_entries;
    int64_t old_cap = g_cap;

    g_entries = (MemtrackEntry*)calloc((size_t)new_cap, sizeof(MemtrackEntry));
    g_cap = new_cap;
    g_len = 0;
    g_tombstone = 0;

    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].occupied == 1) {
            /* Re-insert into new table */
            uint64_t h = ptr_hash(old[i].ptr);
            int64_t idx = (int64_t)(h & (uint64_t)(new_cap - 1));
            for (;;) {
                if (g_entries[idx].occupied <= 0) {
                    g_entries[idx].ptr      = old[i].ptr;
                    g_entries[idx].size     = old[i].size;
                    g_entries[idx].tag      = old[i].tag;
                    g_entries[idx].alloc_id = old[i].alloc_id;
                    g_entries[idx].occupied = 1;
                    g_len++;
                    break;
                }
                idx = (idx + 1) & (new_cap - 1);
            }
        }
    }
    free(old);
}

static MemtrackEntry* memtrack_find(void* ptr) {
    if (!g_entries || g_len == 0) return NULL;
    uint64_t h = ptr_hash(ptr);
    int64_t idx = (int64_t)(h & (uint64_t)(g_cap - 1));
    for (;;) {
        MemtrackEntry* e = &g_entries[idx];
        if (e->occupied == 0) return NULL;  /* empty = not found */
        if (e->occupied == 1 && e->ptr == ptr) return e;
        idx = (idx + 1) & (g_cap - 1);
    }
}

/* ===== Public API ===== */

void spl_memtrack_enable(void) {
    memtrack_ensure_init();
    g_memtrack_enabled = 1;
}

void spl_memtrack_disable(void) {
    g_memtrack_enabled = 0;
}

int spl_memtrack_is_enabled(void) {
    return g_memtrack_enabled;
}

void spl_memtrack_record(void* ptr, int64_t size, const char* tag) {
    if (!ptr) return;
    memtrack_ensure_init();

    /* Grow if needed */
    if ((g_len + g_tombstone + 1) * 100 > g_cap * MEMTRACK_LOAD_PCT) {
        memtrack_resize(g_cap * 2);
    }

    uint64_t h = ptr_hash(ptr);
    int64_t idx = (int64_t)(h & (uint64_t)(g_cap - 1));
    for (;;) {
        MemtrackEntry* e = &g_entries[idx];
        if (e->occupied <= 0) {
            /* Empty or tombstone — insert */
            if (e->occupied == -1) g_tombstone--;
            e->ptr      = ptr;
            e->size     = size;
            e->tag      = tag;
            e->alloc_id = ++g_alloc_id;
            e->occupied = 1;
            g_len++;
            return;
        }
        if (e->ptr == ptr) {
            /* Same address reused (shouldn't normally happen without unrecord) */
            e->size     = size;
            e->tag      = tag;
            e->alloc_id = ++g_alloc_id;
            return;
        }
        idx = (idx + 1) & (g_cap - 1);
    }
}

void spl_memtrack_unrecord(void* ptr) {
    if (!ptr) return;
    MemtrackEntry* e = memtrack_find(ptr);
    if (!e) return;
    e->ptr      = NULL;
    e->occupied = -1;  /* tombstone */
    g_len--;
    g_tombstone++;
}

int64_t spl_memtrack_snapshot(void) {
    return g_alloc_id;
}

void spl_memtrack_dump_since(int64_t snapshot_id, const char* out_path) {
    if (!out_path) return;
    FILE* f = fopen(out_path, "w");
    if (!f) return;

    if (g_entries) {
        for (int64_t i = 0; i < g_cap; i++) {
            MemtrackEntry* e = &g_entries[i];
            if (e->occupied == 1 && e->alloc_id > snapshot_id) {
                fprintf(f, "%lld %lld %s\n",
                        (long long)e->alloc_id,
                        (long long)e->size,
                        e->tag ? e->tag : "unknown");
            }
        }
    }

    fclose(f);
}

int64_t spl_memtrack_live_count(void) {
    return g_len;
}

int64_t spl_memtrack_live_bytes(void) {
    int64_t total = 0;
    if (g_entries) {
        for (int64_t i = 0; i < g_cap; i++) {
            if (g_entries[i].occupied == 1) {
                total += g_entries[i].size;
            }
        }
    }
    return total;
}

void spl_memtrack_reset(void) {
    if (g_entries) {
        free(g_entries);
        g_entries = NULL;
    }
    g_cap       = 0;
    g_len       = 0;
    g_tombstone = 0;
    g_alloc_id  = 0;
}

int64_t spl_memtrack_count_since(int64_t snapshot_id) {
    int64_t count = 0;
    if (g_entries) {
        for (int64_t i = 0; i < g_cap; i++) {
            if (g_entries[i].occupied == 1 && g_entries[i].alloc_id > snapshot_id) {
                count++;
            }
        }
    }
    return count;
}

int64_t spl_memtrack_bytes_since(int64_t snapshot_id) {
    int64_t total = 0;
    if (g_entries) {
        for (int64_t i = 0; i < g_cap; i++) {
            if (g_entries[i].occupied == 1 && g_entries[i].alloc_id > snapshot_id) {
                total += g_entries[i].size;
            }
        }
    }
    return total;
}
