/* Private scoped identity index. No object ABI changes and no entries for
 * permanent allocations. All operations use rt_core_immortal_registry_lock;
 * mutations that touch an existing object also hold the lifecycle lock. */
static RtCoreScopedAllocationKey* rt_core_scoped_keys = NULL;
static size_t rt_core_scoped_cap, rt_core_scoped_len, rt_core_scoped_tombs;
static uint64_t rt_core_scoped_next_birth = 1;
#define RT_CORE_SCOPED_TOMBSTONE ((void*)(uintptr_t)1)

static RtCoreScopedAllocationKey* core_scoped_find_locked(void* ptr) {
    if (!rt_core_scoped_cap) return NULL;
    size_t slot = rt_core_immortal_hash_ptr((uintptr_t)ptr) & (rt_core_scoped_cap - 1);
    for (size_t n = 0; n < rt_core_scoped_cap; ++n) {
        RtCoreScopedAllocationKey* key = &rt_core_scoped_keys[slot];
        if (!key->ptr) return NULL;
        if (key->ptr == ptr) return key;
        slot = (slot + 1) & (rt_core_scoped_cap - 1);
    }
    return NULL;
}
static void core_scoped_remove_locked(void* ptr) {
    RtCoreScopedAllocationKey* key = core_scoped_find_locked(ptr);
    if (!key) return;
    *key = (RtCoreScopedAllocationKey){RT_CORE_SCOPED_TOMBSTONE, 0, 0};
    --rt_core_scoped_len;
    ++rt_core_scoped_tombs;
}
static int core_scoped_place_locked(RtCoreScopedAllocationKey key) {
    size_t slot = rt_core_immortal_hash_ptr((uintptr_t)key.ptr) & (rt_core_scoped_cap - 1);
    for (size_t n = 0; n < rt_core_scoped_cap; ++n) {
        void* old = rt_core_scoped_keys[slot].ptr;
        if (!old || old == RT_CORE_SCOPED_TOMBSTONE) {
            if (old) --rt_core_scoped_tombs;
            rt_core_scoped_keys[slot] = key;
            ++rt_core_scoped_len;
            return 1;
        }
        slot = (slot + 1) & (rt_core_scoped_cap - 1);
    }
    return 0;
}
/* Also used by the SOURCE provider to precharge exact storage and conservative
 * finite hash-probe bounds BEFORE entering the mutation. */
static size_t core_scoped_next_capacity_locked(void) {
    if ((rt_core_scoped_len + rt_core_scoped_tombs + 1) * 10 < rt_core_scoped_cap * 7)
        return 0;
    if (rt_core_scoped_cap && (rt_core_scoped_len + 1) * 10 < rt_core_scoped_cap * 5)
        return rt_core_scoped_cap;
    return rt_core_scoped_cap ? rt_core_scoped_cap * 2 : 64;
}
static int core_scoped_insert_locked(void* ptr, uint32_t owner, RtCoreScopedAllocationKey* out) {
    if (!ptr || !owner || !rt_core_scoped_next_birth || core_scoped_find_locked(ptr)) return 0;
    size_t next = core_scoped_next_capacity_locked();
    if (next) {
        if (next < rt_core_scoped_cap || next > SIZE_MAX / sizeof(RtCoreScopedAllocationKey)) return 0;
        RtCoreScopedAllocationKey* fresh = (RtCoreScopedAllocationKey*)rt_observed_calloc_v1(next, sizeof(*fresh));
        if (!fresh) return 0;
        RtCoreScopedAllocationKey* old = rt_core_scoped_keys;
        size_t old_cap = rt_core_scoped_cap;
        rt_core_scoped_keys = fresh;
        rt_core_scoped_cap = next;
        rt_core_scoped_len = rt_core_scoped_tombs = 0;
        for (size_t i = 0; i < old_cap; ++i)
            if (old[i].ptr && old[i].ptr != RT_CORE_SCOPED_TOMBSTONE)
                core_scoped_place_locked(old[i]);
        free(old);
    }
    RtCoreScopedAllocationKey key = {ptr, rt_core_scoped_next_birth, owner};
    if (!core_scoped_place_locked(key)) return 0;
    rt_core_scoped_next_birth = key.birth == UINT64_MAX ? 0 : key.birth + 1;
    *out = key;
    return 1;
}
static int core_scoped_registered_locked(void* ptr) {
    if (!rt_core_immortal_registry_cap) return 0;
    size_t slot = rt_core_immortal_hash_ptr((uintptr_t)ptr) & (rt_core_immortal_registry_cap - 1);
    for (size_t n = 0; n < rt_core_immortal_registry_cap; ++n) {
        uintptr_t entry = rt_core_immortal_registry[slot];
        if (!entry) return 0;
        if (rt_core_immortal_entry_pointer_v1(entry) == (uintptr_t)ptr) return 1;
        slot = (slot + 1) & (rt_core_immortal_registry_cap - 1);
    }
    return 0;
}
/* Lifecycle lock held; session capacity was reserved before this commit. The
 * destination key is published BEFORE changing registry ownership. A source
 * ledger's old key subsequently fails the exact owner comparison. */
static int core_scoped_transfer(void* ptr, uint32_t from, uint32_t to) {
    rt_core_immortal_registry_acquire();
    RtCoreScopedAllocationKey* live = core_scoped_find_locked(ptr);
    if (!live || live->owner != from) {
        rt_core_immortal_registry_release();
        return 1; /* persistent/foreign nodes are graph traversal prune points */
    }
    RtCoreScopedAllocationKey expected = *live;
    if (!expected.birth || !core_scoped_registered_locked(ptr)) {
        rt_core_immortal_registry_release();
        return 0;
    }
    if (to) {
        if (rt_core_session_heap_object_len == rt_core_session_heap_object_cap) {
            rt_core_immortal_registry_release();
            return 0;
        }
        RtCoreScopedAllocationKey destination = {ptr, expected.birth, to};
        rt_core_session_heap_objects[rt_core_session_heap_object_len++] = destination;
        live->owner = to;
    } else {
        core_scoped_remove_locked(ptr);
    }
    switch (rt_core_registered_object_kind(ptr)) {
        case RT_VALUE_HEAP_STRING: {
            RtCoreString* string = (RtCoreString*)ptr;
            string->reserved &= ~(RT_CORE_STRING_FLAG_TRANSIENT | RT_CORE_STRING_FLAG_SESSION);
            if (to) string->reserved |= RT_CORE_STRING_FLAG_TRANSIENT | RT_CORE_STRING_FLAG_SESSION;
            break;
        }
        case RT_VALUE_HEAP_ARRAY: ((RtCoreArray*)ptr)->transient_scope_id = to; break;
        case RT_VALUE_HEAP_DICT: ((RtCoreDict*)ptr)->transient_scope_id = to; break;
        case RT_VALUE_HEAP_ENUM: ((RtCoreEnum*)ptr)->transient_scope_id = to; break;
        case RT_VALUE_HEAP_CLOSURE: ((RtCoreClosure*)ptr)->transient_scope_id = to; break;
        case RT_VALUE_HEAP_FLOAT:
        case RT_VALUE_HEAP_INT:
        case RT_VALUE_HEAP_UINT: ((RtCoreFloat*)ptr)->transient_scope_id = to; break;
    }
    rt_core_immortal_registry_release();
    return 1;
}
