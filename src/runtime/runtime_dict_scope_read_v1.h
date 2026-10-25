/* Allocation-free, owner-thread-only compiler scope-binding view.
 * Included after the dictionary owner implementation; never exports a pointer
 * or a tagged heap value. The caller must retain the dictionary and charge its
 * read permit before each operation. Concurrent dictionary mutation is outside
 * the dictionary's existing thread-safety contract. */
/* One unit per registry probe plus one payload operation. The optional reader
 * permits at most 64 probes per membership; longer collision tails fail closed
 * instead of spending global registry capacity for every key byte. No waiting for a
 * contended registry lock: a concurrent owner is unsupported and fails closed. */
#define RT_DICT_SCOPE_READ_PROBE_LIMIT_V1 64
int64_t rt_dict_scope_read_bound_v1(void) {
    if (atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock, memory_order_acquire)) return -1;
    size_t cap = rt_core_immortal_registry_cap;
    rt_core_immortal_registry_release();
    size_t probes = cap < RT_DICT_SCOPE_READ_PROBE_LIMIT_V1 ? cap : RT_DICT_SCOPE_READ_PROBE_LIMIT_V1;
    return (int64_t)probes * 3 + 1;
}

static void* rt_core_dict_scope_read_heap_v1(int64_t value, uint32_t kind, int64_t* fuel) {
    uintptr_t raw = (uintptr_t)value;
    if (raw < 4096 || (raw & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) return NULL;
    uintptr_t ptr = raw & ~RT_VALUE_TAG_MASK;
    if (atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock, memory_order_acquire)) return NULL;
    size_t cap = rt_core_immortal_registry_cap;
    int found = 0;
    if (cap) {
        size_t index = rt_core_immortal_hash_ptr(ptr) & (cap - 1);
        for (size_t probes = 0; probes < cap && probes < RT_DICT_SCOPE_READ_PROBE_LIMIT_V1 && *fuel > 0; probes++) {
            --*fuel;
            uintptr_t entry = rt_core_immortal_registry[index];
            if (!entry) break;
            if (entry == ptr) { found = 1; break; }
            index = (index + 1) & (cap - 1);
        }
    }
    rt_core_immortal_registry_release();
    if (!found) return NULL;
    /* Dict kind is byte-sized; numeric and text kinds are 32-bit. */
    if (kind == RT_VALUE_HEAP_DICT)
        return ((RtCoreDict*)ptr)->kind == kind ? (void*)ptr : NULL;
    return *(uint32_t*)ptr == kind ? (void*)ptr : NULL;
}

static RtCoreDict* rt_core_dict_scope_read_checked_v1(
    int64_t dict, int64_t owner, int64_t epoch, int64_t fuel) {
    int64_t bound = rt_dict_scope_read_bound_v1();
    if (bound < 0 || fuel < bound) return NULL;
    RtCoreDict* d = rt_core_dict_scope_read_heap_v1(dict, RT_VALUE_HEAP_DICT, &fuel);
    if (!d || owner <= 0 || epoch <= 0 || d->read_owner != owner ||
        d->read_epoch != epoch || d->read_backing <= 0 || !d->entries)
        return NULL;
    return d;
}

int64_t rt_dict_scope_read_owner_v1(int64_t dict, int64_t fuel) {
    int64_t bound = rt_dict_scope_read_bound_v1();
    if (bound < 0 || fuel < bound) return -1;
    RtCoreDict* d = rt_core_dict_scope_read_heap_v1(dict, RT_VALUE_HEAP_DICT, &fuel);
    return d && d->read_owner > 0 && d->read_epoch > 0 ? d->read_owner : -1;
}

int64_t rt_dict_scope_read_epoch_v1(int64_t dict, int64_t owner, int64_t fuel) {
    int64_t bound = rt_dict_scope_read_bound_v1();
    if (bound < 0 || fuel < bound) return -1;
    RtCoreDict* d = rt_core_dict_scope_read_heap_v1(dict, RT_VALUE_HEAP_DICT, &fuel);
    return d && owner > 0 && d->read_owner == owner && d->read_epoch > 0
        ? d->read_epoch : -1;
}

int64_t rt_dict_scope_read_meta_v1(int64_t dict, int64_t owner,
    int64_t epoch, int64_t field, int64_t fuel) {
    RtCoreDict* d = rt_core_dict_scope_read_checked_v1(dict, owner, epoch, fuel);
    if (!d || d->cap <= 0 || d->len < 0 || d->len > d->cap ||
        (uint64_t)d->cap > INT64_MAX / sizeof(RtCoreDictEntry)) return -1;
    switch (field) {
        case 0: return 1; /* native hash-slot order, exactly rt_dict_keys */
        case 1: return d->len;
        case 2: case 3: return d->cap;
        case 4: return d->read_backing;
        case 5: return sizeof(RtCoreDict);
        case 6: return d->cap * (int64_t)sizeof(RtCoreDictEntry);
        default: return -1;
    }
}

int64_t rt_dict_scope_read_slot_v1(int64_t dict, int64_t owner,
    int64_t epoch, int64_t slot, int64_t field, int64_t byte_index, int64_t fuel) {
    RtCoreDict* d = rt_core_dict_scope_read_checked_v1(dict, owner, epoch, fuel);
    if (!d || slot < 0 || slot >= d->cap) return -1;
    RtCoreDictEntry* entry = &d->entries[slot];
    if (field == 0) return entry->occupied == 1 ? 1 : 0;
    if (entry->occupied != 1) return -1;
    /* The checked owner may spend up to one registry-cap of the original
     * allowance. Reserve that worst case before key/value validation. */
    size_t owner_probes = rt_core_immortal_registry_cap < RT_DICT_SCOPE_READ_PROBE_LIMIT_V1
        ? rt_core_immortal_registry_cap : RT_DICT_SCOPE_READ_PROBE_LIMIT_V1;
    if ((uint64_t)fuel <= owner_probes) return -1;
    fuel -= (int64_t)owner_probes;
    RtCoreString* key = rt_core_dict_scope_read_heap_v1(entry->key, RT_VALUE_HEAP_STRING, &fuel);
    if (!key || key->len > INT64_MAX) return -1;
    RtCoreWideInt* wide = rt_core_dict_scope_read_heap_v1(entry->value, RT_VALUE_HEAP_INT, &fuel);
    if (!wide && !rt_core_is_int(entry->value)) return -1;
    int64_t value = wide ? wide->value : rt_core_as_int(entry->value);
    if (value < 0) return -1;
    switch (field) {
        case 1: return value;
        case 2: return (int64_t)key->len;
        case 3:
            return byte_index >= 0 && (uint64_t)byte_index < key->len
                ? (uint8_t)key->data[byte_index] : -1;
        default: return -1;
    }
}
