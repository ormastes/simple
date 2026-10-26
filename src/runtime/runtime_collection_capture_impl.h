/* Private capture implementation shared by core-C and Rust-owned runtimes.
 * Runtime text, builder, and nil values are accessed only through runtime.h.
 * The including translation unit supplies the standard C headers. */
#ifndef SIMPLE_RUNTIME_COLLECTION_CAPTURE_IMPL_H
#define SIMPLE_RUNTIME_COLLECTION_CAPTURE_IMPL_H

/* Run-scoped collection telemetry. The active path does no file I/O and the
 * inactive path is one atomic load. The driver owns .sprof validation/writing
 * after finish(), outside interpreted or native collection operations. */
#define RT_COLLECTION_CAPTURE_SLOTS 131071u
/* Each site writes one collection sample and six named P6 metric samples.
 * The .sprof loader admits at most 100000 samples across both record kinds. */
#define RT_COLLECTION_CAPTURE_MAX_SITES 14285u
#define RT_COLLECTION_CAPTURE_MAX_SITE_BYTES 4096u
#define RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES 256u

#ifndef SPL_COLLECTION_CAPTURE_TEXT_COPY
/* Core-C owns NUL-terminated runtime texts and trusted raw C strings. Keep
 * reads bytewise so a short raw allocation need not span the token limit. */
static int64_t spl_collection_capture_core_text_copy(int64_t value, char* buffer,
                                                     size_t max_len) {
    const char* text = rt_interp_cstr(value);
    if (!text || !buffer || max_len > RT_COLLECTION_CAPTURE_MAX_SITE_BYTES) return 0;
    for (size_t i = 0; i <= max_len; i++) {
        if (!text[i]) { buffer[i] = '\0'; return 1; }
        if (i == max_len) return 0;
        buffer[i] = text[i];
    }
    return 0;
}
#define SPL_COLLECTION_CAPTURE_TEXT_COPY(value, buffer, max_len) \
    spl_collection_capture_core_text_copy((value), (buffer), (max_len))
#endif

static const char* spl_collection_capture_text(int64_t value, char* buffer,
                                              size_t max_len) {
    return SPL_COLLECTION_CAPTURE_TEXT_COPY(value, buffer, max_len) ? buffer : NULL;
}

typedef struct RtCollectionCaptureEntry {
    char* site;
    uint64_t hash;
    int64_t current_size;
    int64_t peak_size;
    int64_t lookups;
    int64_t hits;
    int64_t misses;
    int64_t materializations;
    int64_t hash_probes;
    int64_t hash_collisions;
    int hash_probe_observed;
} RtCollectionCaptureEntry;

static atomic_flag spl_collection_capture_lock = ATOMIC_FLAG_INIT;
static _Atomic int spl_collection_capture_active = 0;
static RtCollectionCaptureEntry* spl_collection_capture_slots = NULL;
static char* spl_collection_capture_target = NULL;
static size_t spl_collection_capture_count = 0;
static int spl_collection_capture_error = 0;

static void spl_collection_capture_lock_enter(void) {
    while (atomic_flag_test_and_set_explicit(&spl_collection_capture_lock,
                                             memory_order_acquire)) { }
}

static void spl_collection_capture_lock_leave(void) {
    atomic_flag_clear_explicit(&spl_collection_capture_lock, memory_order_release);
}

static int spl_collection_capture_token_valid(const char* text, size_t max_len,
                                             int require_site) {
    if (!text) return 0;
    size_t len = strlen(text);
    if (len == 0 || len > max_len) return 0;
    if (require_site && (len < 6 || memcmp(text, "ast://", 6) != 0)) return 0;
    for (size_t i = 0; i < len; i++) {
        if (text[i] == ';' || text[i] == '\n' || text[i] == '\r') return 0;
    }
    return 1;
}

static char* spl_collection_capture_copy(const char* text) {
    size_t len = strlen(text);
    char* copy = (char*)malloc(len + 1);
    if (copy) memcpy(copy, text, len + 1);
    return copy;
}

static uint64_t spl_collection_capture_hash(const char* site) {
    uint64_t hash = UINT64_C(14695981039346656037);
    for (const unsigned char* p = (const unsigned char*)site; *p; p++) {
        hash = (hash ^ *p) * UINT64_C(1099511628211);
    }
    return hash;
}

static void spl_collection_capture_free_slots(RtCollectionCaptureEntry* slots) {
    if (!slots) return;
    for (size_t i = 0; i < RT_COLLECTION_CAPTURE_SLOTS; i++) free(slots[i].site);
    free(slots);
}

static RtCollectionCaptureEntry* spl_collection_capture_site_locked(const char* site) {
    uint64_t hash = spl_collection_capture_hash(site);
    size_t first = (size_t)(hash % RT_COLLECTION_CAPTURE_SLOTS);
    for (size_t probe = 0; probe < RT_COLLECTION_CAPTURE_SLOTS; probe++) {
        RtCollectionCaptureEntry* entry = &spl_collection_capture_slots[
            (first + probe) % RT_COLLECTION_CAPTURE_SLOTS];
        if (entry->site) {
            if (entry->hash == hash && strcmp(entry->site, site) == 0) return entry;
            continue;
        }
        if (spl_collection_capture_count >= RT_COLLECTION_CAPTURE_MAX_SITES) return NULL;
        entry->site = spl_collection_capture_copy(site);
        if (!entry->site) return NULL;
        entry->hash = hash;
        spl_collection_capture_count++;
        return entry;
    }
    return NULL;
}

static int spl_collection_capture_target_matches_locked(const char* target) {
    return target && (target[0] == '\0' ||
        (spl_collection_capture_target && strcmp(target, spl_collection_capture_target) == 0));
}

int64_t spl_collection_capture_begin(int64_t target_value) {
    char target_buffer[RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES + 1];
    const char* target = spl_collection_capture_text(target_value, target_buffer,
        RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES);
    if (!spl_collection_capture_token_valid(target, RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES, 0))
        return 0;
    char* owned_target = spl_collection_capture_copy(target);
    RtCollectionCaptureEntry* slots = (RtCollectionCaptureEntry*)calloc(
        RT_COLLECTION_CAPTURE_SLOTS, sizeof(RtCollectionCaptureEntry));
    if (!owned_target || !slots) {
        free(owned_target);
        free(slots);
        return 0;
    }
    spl_collection_capture_lock_enter();
    if (atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        free(owned_target);
        free(slots);
        return 0;
    }
    spl_collection_capture_slots = slots;
    spl_collection_capture_target = owned_target;
    spl_collection_capture_count = 0;
    spl_collection_capture_error = 0;
    atomic_store_explicit(&spl_collection_capture_active, 1, memory_order_release);
    spl_collection_capture_lock_leave();
    return 1;
}

int64_t spl_collection_capture_note_size(int64_t site_value, int64_t target_value,
                                        int64_t size) {
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_acquire)) return 1;
    char site_buffer[RT_COLLECTION_CAPTURE_MAX_SITE_BYTES + 1];
    char target_buffer[RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES + 1];
    const char* target = spl_collection_capture_text(target_value, target_buffer,
        RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES);
    spl_collection_capture_lock_enter();
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    if (!spl_collection_capture_target_matches_locked(target)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    const char* site = spl_collection_capture_text(site_value, site_buffer,
        RT_COLLECTION_CAPTURE_MAX_SITE_BYTES);
    if (size < 0 || !spl_collection_capture_token_valid(site,
            RT_COLLECTION_CAPTURE_MAX_SITE_BYTES, 1)) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    RtCollectionCaptureEntry* entry = spl_collection_capture_site_locked(site);
    if (!entry) spl_collection_capture_error = 1;
    else {
        entry->current_size = size;
        if (size > entry->peak_size) entry->peak_size = size;
    }
    spl_collection_capture_lock_leave();
    return entry ? 1 : 0;
}

int64_t spl_collection_capture_note_lookup(int64_t site_value, int64_t target_value,
                                          int64_t found) {
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_acquire)) return 1;
    char site_buffer[RT_COLLECTION_CAPTURE_MAX_SITE_BYTES + 1];
    char target_buffer[RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES + 1];
    const char* target = spl_collection_capture_text(target_value, target_buffer,
        RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES);
    spl_collection_capture_lock_enter();
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    if (!spl_collection_capture_target_matches_locked(target)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    const char* site = spl_collection_capture_text(site_value, site_buffer,
        RT_COLLECTION_CAPTURE_MAX_SITE_BYTES);
    if ((found != 0 && found != 1) || !spl_collection_capture_token_valid(site,
            RT_COLLECTION_CAPTURE_MAX_SITE_BYTES, 1)) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    RtCollectionCaptureEntry* entry = spl_collection_capture_site_locked(site);
    if (!entry || entry->lookups == INT64_MAX ||
            (found && entry->hits == INT64_MAX) ||
            (!found && entry->misses == INT64_MAX)) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    entry->lookups++;
    if (found) entry->hits++;
    else entry->misses++;
    spl_collection_capture_lock_leave();
    return 1;
}

int64_t spl_collection_capture_note_materialization(int64_t site_value,
                                                   int64_t target_value) {
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_acquire)) return 1;
    char site_buffer[RT_COLLECTION_CAPTURE_MAX_SITE_BYTES + 1];
    char target_buffer[RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES + 1];
    const char* target = spl_collection_capture_text(target_value, target_buffer,
        RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES);
    spl_collection_capture_lock_enter();
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    if (!spl_collection_capture_target_matches_locked(target)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    const char* site = spl_collection_capture_text(site_value, site_buffer,
        RT_COLLECTION_CAPTURE_MAX_SITE_BYTES);
    if (!spl_collection_capture_token_valid(site, RT_COLLECTION_CAPTURE_MAX_SITE_BYTES, 1)) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    RtCollectionCaptureEntry* entry = spl_collection_capture_site_locked(site);
    if (!entry || entry->materializations == INT64_MAX) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    entry->materializations++;
    spl_collection_capture_lock_leave();
    return 1;
}

int64_t spl_collection_capture_note_hash_probe(int64_t site_value,
                                              int64_t target_value,
                                              int64_t probes,
                                              int64_t collisions) {
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_acquire)) return 1;
    char site_buffer[RT_COLLECTION_CAPTURE_MAX_SITE_BYTES + 1];
    char target_buffer[RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES + 1];
    const char* target = spl_collection_capture_text(target_value, target_buffer,
        RT_COLLECTION_CAPTURE_MAX_TARGET_BYTES);
    spl_collection_capture_lock_enter();
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    if (!spl_collection_capture_target_matches_locked(target)) {
        spl_collection_capture_lock_leave();
        return 1;
    }
    const char* site = spl_collection_capture_text(site_value, site_buffer,
        RT_COLLECTION_CAPTURE_MAX_SITE_BYTES);
    if (probes < 1 || collisions < 0 || collisions > probes ||
            !spl_collection_capture_token_valid(site,
                RT_COLLECTION_CAPTURE_MAX_SITE_BYTES, 1)) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    RtCollectionCaptureEntry* entry = spl_collection_capture_site_locked(site);
    if (!entry || entry->hash_probes > INT64_MAX - probes ||
            entry->hash_collisions > INT64_MAX - collisions) {
        spl_collection_capture_error = 1;
        spl_collection_capture_lock_leave();
        return 0;
    }
    entry->hash_probes += probes;
    entry->hash_collisions += collisions;
    entry->hash_probe_observed = 1;
    spl_collection_capture_lock_leave();
    return 1;
}

static int spl_collection_capture_entry_order(const void* left, const void* right) {
    const RtCollectionCaptureEntry* a = *(const RtCollectionCaptureEntry* const*)left;
    const RtCollectionCaptureEntry* b = *(const RtCollectionCaptureEntry* const*)right;
    return strcmp(a->site, b->site);
}

int64_t spl_collection_capture_finish(void) {
    spl_collection_capture_lock_enter();
    if (!atomic_load_explicit(&spl_collection_capture_active, memory_order_relaxed)) {
        spl_collection_capture_lock_leave();
        return rt_value_nil();
    }
    atomic_store_explicit(&spl_collection_capture_active, 0, memory_order_release);
    RtCollectionCaptureEntry* slots = spl_collection_capture_slots;
    char* target = spl_collection_capture_target;
    size_t count = spl_collection_capture_count;
    int failed = spl_collection_capture_error;
    spl_collection_capture_slots = NULL;
    spl_collection_capture_target = NULL;
    spl_collection_capture_count = 0;
    spl_collection_capture_error = 0;
    spl_collection_capture_lock_leave();

    RtCollectionCaptureEntry** ordered = count ?
        (RtCollectionCaptureEntry**)malloc(count * sizeof(*ordered)) : NULL;
    if (count && !ordered) failed = 1;
    if (!failed) {
        size_t next = 0;
        for (size_t i = 0; i < RT_COLLECTION_CAPTURE_SLOTS; i++) {
            if (slots[i].site) ordered[next++] = &slots[i];
        }
        if (next != count) failed = 1;
    }
    if (!failed && count) qsort(ordered, count, sizeof(*ordered),
                               spl_collection_capture_entry_order);
    int64_t builder = failed ? 0 : rt_string_builder_new();
    if (!failed && !builder) failed = 1;
    size_t next_metric_sample = count;
    for (size_t i = 0; !failed && i < count; i++) {
        char row[8192];
        RtCollectionCaptureEntry* entry = ordered[i];
        int len = snprintf(row, sizeof(row),
            "%scollection;sample=%zu;site=%s;target=%s;samples=1;size_p95=%lld;lookup_p95=%lld;hits_p95=%lld;misses_p95=%lld",
            i ? "\n" : "", i, entry->site, target,
            (long long)entry->peak_size, (long long)entry->lookups,
            (long long)entry->hits, (long long)entry->misses);
        if (len < 0 || (size_t)len >= sizeof(row)) {
            failed = 1;
            break;
        }
        int64_t text = rt_string_new((const uint8_t*)row, (uint64_t)len);
        if (text == rt_value_nil() || !rt_string_builder_push(builder, text)) failed = 1;
    }
    for (size_t i = 0; !failed && i < count; i++) {
        RtCollectionCaptureEntry* entry = ordered[i];
        const char* names[6] = {
            "collection_size", "lookup_count", "distinct_key_count",
            "materialization_count", "hash_probe_count", "hash_collision_count"
        };
        const int64_t values[6] = {
            entry->peak_size, entry->lookups, entry->current_size,
            entry->materializations, entry->hash_probes, entry->hash_collisions
        };
        for (size_t metric = 0; !failed && metric < 6; metric++) {
            if (metric >= 4 && !entry->hash_probe_observed) continue;
            char row[8192];
            size_t sample_id = next_metric_sample++;
            int len = snprintf(row, sizeof(row),
                "\nmetric;sample=%zu;site=%s;target=%s;name=%s;value=%lld",
                sample_id, entry->site, target, names[metric],
                (long long)values[metric]);
            if (len < 0 || (size_t)len >= sizeof(row)) {
                failed = 1;
                break;
            }
            int64_t text = rt_string_new((const uint8_t*)row, (uint64_t)len);
            if (text == rt_value_nil() || !rt_string_builder_push(builder, text))
                failed = 1;
        }
    }
    int64_t result = failed ? rt_value_nil() : rt_string_builder_finish(builder);
    if (failed && builder) rt_string_builder_free(builder);
    free(ordered);
    spl_collection_capture_free_slots(slots);
    free(target);
    return result;
}

int64_t spl_collection_capture_abort(void) {
    spl_collection_capture_lock_enter();
    atomic_store_explicit(&spl_collection_capture_active, 0, memory_order_release);
    RtCollectionCaptureEntry* slots = spl_collection_capture_slots;
    char* target = spl_collection_capture_target;
    spl_collection_capture_slots = NULL;
    spl_collection_capture_target = NULL;
    spl_collection_capture_count = 0;
    spl_collection_capture_error = 0;
    spl_collection_capture_lock_leave();
    spl_collection_capture_free_slots(slots);
    free(target);
    return 1;
}

#endif
