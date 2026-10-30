/* Real core-C boundary tests, including private overflow/reuse sabotage.
 * Compile this translation unit with runtime.c, function sections and gc-sections.
 * Link --wrap=malloc,--wrap=calloc,--wrap=realloc,--wrap=free. The test allocator
 * can retain/reissue one real dictionary header to make address reuse exact. */
#include "../runtime_native.c"
#include <assert.h>
#include <sys/resource.h>

static size_t allocations;
static void* recycle_watch;
static void* recycle_slot;
void* __real_malloc(size_t n);
void* __real_calloc(size_t n, size_t s);
void* __real_realloc(void* p, size_t n);
void __real_free(void* p);
void* __wrap_malloc(size_t n) { allocations++; return __real_malloc(n); }
void* __wrap_calloc(size_t n, size_t s) {
    allocations++;
    if (n == 1 && s == sizeof(RtCoreDict) && recycle_slot) {
        void* p = recycle_slot; recycle_slot = NULL;
        memset(p, 0, s); return p;
    }
    return __real_calloc(n, s);
}
void* __wrap_realloc(void* p, size_t n) { allocations++; return __real_realloc(p, n); }
void __wrap_free(void* p) {
    if (p && p == recycle_watch) {
        recycle_watch = NULL; recycle_slot = p; return;
    }
    __real_free(p);
}

static int64_t text_key(const char* key) {
    return rt_string_new((const uint8_t*)key, strlen(key));
}
static int64_t owner_of(int64_t d) {
    return rt_dict_scope_read_owner_v1(d, rt_dict_scope_read_bound_v1());
}
static int64_t epoch_of(int64_t d, int64_t owner) {
    return rt_dict_scope_read_epoch_v1(d, owner, rt_dict_scope_read_bound_v1());
}
static int64_t meta(int64_t d, int64_t o, int64_t e, int64_t field) {
    return rt_dict_scope_read_meta_v1(d, o, e, field, rt_dict_scope_read_bound_v1());
}
static int64_t slot(int64_t d, int64_t o, int64_t e, int64_t s, int64_t f, int64_t b) {
    return rt_dict_scope_read_slot_v1(d, o, e, s, f, b, rt_dict_scope_read_bound_v1());
}

static void compare_keys(int64_t d) {
    int64_t keys = rt_dict_keys(d);
    int64_t o = owner_of(d), e = epoch_of(d, o), ordinal = 0;
    int64_t scan = meta(d, o, e, 3);
    for (int64_t s = 0; s < scan; s++) {
        int64_t occupied = slot(d, o, e, s, 0, 0);
        assert(occupied == 0 || occupied == 1);
        if (!occupied) continue;
        int64_t k = rt_array_get((SplArray*)(uintptr_t)keys, ordinal++);
        RtCoreString* key = rt_core_as_string(k);
        assert(key);
        assert(slot(d, o, e, s, 2, 0) == (int64_t)key->len);
        assert(slot(d, o, e, s, 1, 0) == rt_core_numeric_arg(rt_dict_get(d, k)));
        for (uint64_t b = 0; b < key->len; b++)
            assert(slot(d, o, e, s, 3, b) == (uint8_t)key->data[b]);
        assert(slot(d, o, e, s, 3, key->len) == -1);
    }
    assert(ordinal == rt_dict_len(d));
    assert(meta(d, o, e, 5) == sizeof(RtCoreDict));
    assert(meta(d, o, e, 6) == meta(d, o, e, 2) * sizeof(RtCoreDictEntry));
}

int main(void) {
    int64_t d = rt_dict_new(0), o = owner_of(d), e = epoch_of(d, o);
    assert(o > 0 && e > 0 && meta(d, o, e, 1) == 0);
    compare_keys(d);
    int64_t bound = rt_dict_scope_read_bound_v1();
    assert(rt_dict_scope_read_owner_v1(d, 0) == -1);
    assert(rt_dict_scope_read_owner_v1(d, bound - 1) == -1);
    assert(rt_dict_scope_read_owner_v1(d, bound) == o);
    assert(rt_dict_scope_read_owner_v1(0x10001, bound) == -1);
    assert(rt_dict_scope_read_epoch_v1(d, o + 1, bound) == -1);
    int64_t utf8 = text_key("caf\xc3\xa9\xf0\x9f\x90\x88");
    assert(rt_dict_set(d, utf8, rt_value_int(INT64_MAX)));
    assert(meta(d, o, e, 1) == -1);
    compare_keys(d);
    for (int i = 0; i < 192; i++) {
        char key[32]; snprintf(key, sizeof key, "scope-%d", i);
        assert(rt_dict_set(d, text_key(key), rt_value_int(i)));
    }
    compare_keys(d);
    e = epoch_of(d, o);
    int64_t backing = meta(d, o, e, 4);
    assert(backing > 1);
    assert(rt_dict_set(d, utf8, rt_value_int(42)));
    assert(meta(d, o, e, 4) == -1);
    e = epoch_of(d, o);
    assert(meta(d, o, e, 4) == backing);
    for (int i = 0; i < 160; i++) {
        char key[32]; snprintf(key, sizeof key, "scope-%d", i);
        assert(rt_dict_remove(d, text_key(key)));
    }
    compare_keys(d);
    assert(rt_dict_clear(d));
    assert(meta(d, o, e, 1) == -1);
    assert(rt_dict_set(d, utf8, rt_value_int(77)));
    compare_keys(d);
    e = epoch_of(d, o);
    int64_t live = 0;
    while (!slot(d, o, e, live, 0, 0)) live++;
    assert(slot(d, o, e, -1, 0, 0) == -1);
    assert(slot(d, o, e, live, 3, -1) == -1);

    int64_t wrong = rt_dict_new(0);
    assert(rt_dict_set(wrong, rt_value_int(5), rt_value_int(8)));
    int64_t wo = owner_of(wrong), we = epoch_of(wrong, wo), ws = 0;
    while (!slot(wrong, wo, we, ws, 0, 0)) ws++;
    assert(slot(wrong, wo, we, ws, 1, 0) == -1);
    assert(rt_dict_clear(wrong));
    assert(rt_dict_set(wrong, utf8, rt_value_int(-1)));
    we = epoch_of(wrong, wo); ws = 0;
    while (!slot(wrong, wo, we, ws, 0, 0)) ws++;
    assert(slot(wrong, wo, we, ws, 2, 0) == -1);
    assert(rt_dict_set(wrong, utf8, text_key("wrong-value")));
    we = epoch_of(wrong, wo);
    assert(slot(wrong, wo, we, ws, 1, 0) == -1);

    /* A realistic large scope retains 2,049 live bindings while benchmarking,
     * rather than timing an empty/cleared table or a source-only oracle. */
    for (int i = 0; i < 2048; i++) {
        char key[32]; snprintf(key, sizeof key, "large-scope-%d", i);
        assert(rt_dict_set(d, text_key(key), rt_value_int(1000 + i)));
    }
    e = epoch_of(d, o);
    live = 0;
    while (slot(d, o, e, live, 0, 0) != 1 || slot(d, o, e, live, 1, 0) != 77) live++;
    assert(meta(d, o, e, 1) == 2049);
    /* No allocator call during 300k real payload reads and validation. */
    size_t before = allocations;
    struct timespec start, end;
    clock_gettime(CLOCK_MONOTONIC, &start);
    for (int i = 0; i < 100000; i++) {
        assert(slot(d, o, e, live, 1, 0) == 77);
        assert(slot(d, o, e, live, 2, 0) == 9);
        assert(slot(d, o, e, live, 3, 3) == 0xc3);
    }
    clock_gettime(CLOCK_MONOTONIC, &end);
    assert(allocations == before);

    /* Real unregister/free, then allocator-forced reuse through rt_dict_new. */
    int64_t dead = rt_dict_new(0), old_owner = owner_of(dead);
    recycle_watch = (void*)(uintptr_t)(dead & -8);
    assert(rt_dict_free_deep(dead) != 0);
    assert(owner_of(dead) == -1);
    int reused = 0;
    for (int i = 0; i < 128; i++) {
        int64_t fresh = rt_dict_new(0), fresh_owner = owner_of(fresh);
        assert(fresh_owner > old_owner);
        assert(rt_dict_scope_read_epoch_v1(fresh, old_owner, rt_dict_scope_read_bound_v1()) == -1);
        if (fresh == dead) {
            reused = 1;
            assert(rt_dict_scope_read_epoch_v1(dead, old_owner, rt_dict_scope_read_bound_v1()) == -1);
        }
        rt_dict_free_deep(fresh);
    }
    assert(reused);
    atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock, memory_order_acquire);
    assert(rt_dict_scope_read_bound_v1() == -1);
    assert(rt_dict_scope_read_owner_v1(d, 193) == -1);
    atomic_flag_clear_explicit(&rt_core_immortal_registry_lock, memory_order_release);
    /* Overflow is irreversible while ordinary set still succeeds. */
    RtCoreDict* raw = rt_core_as_dict(d);
    raw->read_epoch = INT64_MAX;
    assert(rt_dict_set(d, utf8, rt_value_int(78)));
    assert(owner_of(d) == -1);
    assert(rt_dict_set(d, utf8, rt_value_int(79)));
    assert(owner_of(d) == -1 && rt_core_numeric_arg(rt_dict_get(d, utf8)) == 79);
    struct rusage usage; getrusage(RUSAGE_SELF, &usage);
    double seconds = (end.tv_sec - start.tv_sec) + (end.tv_nsec - start.tv_nsec) / 1e9;
    printf("PASS native-scope-read bindings=2049 reads=300000 allocations=0 seconds=%.6f maxrss_kib=%ld address_reuse_observed=%d\n",
        seconds, usage.ru_maxrss, reused);
    return 0;
}
