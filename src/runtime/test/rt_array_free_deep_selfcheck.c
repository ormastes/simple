/* Self-check for rt_array_free_deep -- the deep (recursive) array free.
 *
 * rt_array_free is shallow: it drops the outer buffer and leaks every heap
 * element. rt_array_free_deep recurses, but only into structures it can PROVE
 * are exclusively owned trees of registered arrays and non-shared strings; it
 * refuses everything else, and a refusal must free NOTHING (all-or-nothing).
 *
 * The cases that actually bite:
 *   - case 3/4: an element from the process-wide short-string cache or the
 *     literal intern table must refuse the WHOLE call, and must leave both the
 *     string and the array fully intact and still usable afterwards.
 *   - case 6: aliasing. RuntimeValue is Copy over a u64, so an element can be a
 *     duplicate or the array itself. Freeing such a structure double-frees.
 *   - case 9: probe-chain integrity across the tombstoned immortal registry and
 *     the swap-remove array registry -- free every other structure out of a
 *     large batch, then prove every survivor is still readable AND still
 *     freeable. A truncating erase strands survivors and fails here.
 *
 * Build + run (the runtime dir holds mutually-exclusive alternative TUs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/rtaf \
 *     src/runtime/test/rt_array_free_deep_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3 && /tmp/rtaf
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>

typedef struct SplArray SplArray;

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_new_literal(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_free(int64_t value);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_heap_registry_count(void);

extern SplArray* rt_array_new(int64_t cap);
extern SplArray* rt_array_new_with_cap_u64(int64_t cap);
extern SplArray* rt_byte_array_new_len(uint64_t len);
extern int8_t rt_array_push(SplArray* array, int64_t value);
extern void rt_array_set(SplArray* array, int64_t idx, int64_t value);
extern int64_t rt_array_get(SplArray* array, int64_t idx);
extern int64_t rt_array_len(SplArray* array);
extern void rt_array_free(SplArray* array);
extern int64_t rt_array_free_deep(int64_t value);
extern int64_t rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);

static int failures = 0;

static void check(int cond, const char* what) {
    if (cond) {
        printf("  ok   %s\n", what);
    } else {
        printf("  FAIL %s\n", what);
        failures++;
    }
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

static int64_t handle(SplArray* a) {
    return (int64_t)(uintptr_t)a;
}

int main(void) {
    /* ---- 1. trivially-safe tier: a packed [u8] has no heap elements ---- */
    int64_t base = rt_heap_registry_count();
    SplArray* bytes = rt_byte_array_new_len(4096);
    check(rt_heap_registry_count() == base + 1, "byte array registers (+1)");
    check(rt_array_free_deep(handle(bytes)) == 1, "packed [u8] deep-freed");
    check(rt_heap_registry_count() == base, "registry back to baseline");

    /* ---- 2. double free refused, with no second decrement ---- */
    int64_t after = rt_heap_registry_count();
    check(rt_array_free_deep(handle(bytes)) == 0, "double deep-free refused");
    check(rt_heap_registry_count() == after, "refused free does not decrement");
    check(rt_array_free_deep(0) == 0, "nil refused");
    int64_t lone = mkstr("a string is not an array root");
    check(rt_array_free_deep(lone) == 0, "string root refused (belongs to rt_string_free)");
    check(rt_string_free(lone) == 1, "that string is still intact and freeable");

    /* ---- 3. an element from the process-wide short-string cache refuses ----
     *  len<=1 strings are handed out repeatedly, so freeing one corrupts every
     *  other holder. The refusal must be TOTAL: the array survives too. */
    base = rt_heap_registry_count();
    SplArray* with_shared = rt_array_new(4);
    int64_t shared = mkstr("x");
    int64_t owned = mkstr("an owned element that would have been freed");
    rt_array_push(with_shared, owned);
    rt_array_push(with_shared, shared);
    int64_t peak = rt_heap_registry_count();
    check(rt_array_free_deep(handle(with_shared)) == 0, "array holding a cached string refused");
    check(rt_heap_registry_count() == peak, "refusal freed nothing (count unchanged)");
    check(rt_string_len(shared) == 1, "cached string still usable");
    check(rt_string_len(owned) == (int64_t)strlen("an owned element that would have been freed"),
          "the freeable sibling element was NOT freed either (all-or-nothing)");
    check(rt_array_len(with_shared) == 2, "the array itself survived the refusal");
    /* drop the shared element and it becomes freeable */
    rt_array_set(with_shared, 1, 0);
    check(rt_array_free_deep(handle(with_shared)) == 1, "same array frees once the cached element is gone");
    /* exactly 2 of the 3 registrations go away: the array and the owned string.
     * The cached "x" stays registered forever by design -- it is process-wide
     * and unowned, which is the whole reason the refusal above exists. */
    check(rt_heap_registry_count() == peak - 2, "array + owned string reclaimed, cached string still registered");
    check(rt_string_len(shared) == 1, "cached string outlived the array that referenced it");
    (void)base;

    /* ---- 4. interned literal elements refuse the same way ---- */
    static const uint8_t lit[] = "an interned literal inside an array";
    base = rt_heap_registry_count();
    SplArray* with_lit = rt_array_new(4);
    rt_array_push(with_lit, rt_string_new_literal(lit, sizeof(lit) - 1));
    peak = rt_heap_registry_count();
    check(rt_array_free_deep(handle(with_lit)) == 0, "array holding an interned literal refused");
    check(rt_heap_registry_count() == peak, "literal refusal freed nothing");
    check(rt_string_new_literal(lit, sizeof(lit) - 1) == rt_array_get(with_lit, 0),
          "literal interning still returns the same live object");
    rt_array_free(with_lit); /* shallow: the literal must outlive it */
    check(rt_string_len(rt_string_new_literal(lit, sizeof(lit) - 1)) == (int64_t)(sizeof(lit) - 1),
          "interned literal intact after the array went away");

    /* ---- 5. NESTED array: outer -> inner [u8] + inner generic + string ---- */
    base = rt_heap_registry_count();
    SplArray* outer = rt_array_new(4);
    SplArray* inner_bytes = rt_byte_array_new_len(64);
    SplArray* inner_generic = rt_array_new(4);
    rt_array_push(inner_generic, mkstr("a deeply nested owned string element"));
    rt_array_push(outer, handle(inner_bytes));
    rt_array_push(outer, handle(inner_generic));
    rt_array_push(outer, mkstr("a string held directly by the outer array"));
    rt_array_push(outer, 12345 << 3); /* a tagged immediate: nothing to free */
    check(rt_heap_registry_count() == base + 5, "nested structure registered 5 objects");
    check(rt_array_free_deep(handle(outer)) == 1, "nested structure deep-freed");
    check(rt_heap_registry_count() == base, "all 5 nodes reclaimed, none stranded");

    /* ---- 6. aliasing and self-reference must refuse ---- */
    base = rt_heap_registry_count();
    SplArray* dup_holder = rt_array_new(4);
    SplArray* shared_child = rt_array_new(4);
    rt_array_push(dup_holder, handle(shared_child));
    rt_array_push(dup_holder, handle(shared_child)); /* same pointer twice */
    peak = rt_heap_registry_count();
    check(rt_array_free_deep(handle(dup_holder)) == 0, "duplicated child pointer refused");
    check(rt_heap_registry_count() == peak, "alias refusal freed nothing");
    check(rt_array_len(shared_child) == 0, "the aliased child is still live");
    rt_array_set(dup_holder, 1, 0);
    check(rt_array_free_deep(handle(dup_holder)) == 1, "frees once the duplicate is cleared");

    SplArray* selfref = rt_array_new(4);
    rt_array_push(selfref, handle(selfref)); /* cycle: contains itself */
    peak = rt_heap_registry_count();
    check(rt_array_free_deep(handle(selfref)) == 0, "self-referential array refused (no infinite walk)");
    check(rt_heap_registry_count() == peak, "cycle refusal freed nothing");
    rt_array_free(selfref);

    /* ---- 7. non-array/non-string heap elements refuse rather than strand ----
     *  A boxed enum is a registered, owned object this primitive has no free
     *  path for. Dropping the buffer would make it permanently unreachable. */
    base = rt_heap_registry_count();
    SplArray* with_enum = rt_array_new(4);
    rt_array_push(with_enum, rt_enum_new(7, 1, 42));
    peak = rt_heap_registry_count();
    check(rt_array_free_deep(handle(with_enum)) == 0, "array holding a boxed enum refused");
    check(rt_heap_registry_count() == peak, "enum refusal freed nothing");
    rt_array_free(with_enum);

    /* ---- 8. packed u64 array: raw payloads may alias the HEAP tag bits, and
     *  that is fine -- a U64_PACKED buffer holds no heap references at all. */
    base = rt_heap_registry_count();
    SplArray* packed = rt_array_new_with_cap_u64(8);
    rt_array_push(packed, (int64_t)0x7f1122334455aa01LL); /* low bits 0b001 */
    rt_array_push(packed, (int64_t)0x00005566778899f9LL);
    check(rt_array_free_deep(handle(packed)) == 1, "u64-packed array deep-freed despite tag-aliasing payloads");
    check(rt_heap_registry_count() == base, "u64-packed reclaimed");

    /* ---- 9. PROBE-CHAIN INTEGRITY across both registries ----
     *  Build many outer arrays, each owning a byte array and a unique string,
     *  free every other structure, then prove every survivor is still readable
     *  AND still freeable. Catches a truncating (tombstone-less) erase in the
     *  immortal table and a mis-ordered swap-remove in the array registry. */
    enum { N = 1024 };
    static SplArray* roots[N];
    char buf[80];
    base = rt_heap_registry_count();
    for (int i = 0; i < N; i++) {
        SplArray* r = rt_array_new(4);
        SplArray* payload = rt_byte_array_new_len(16);
        snprintf(buf, sizeof buf, "probe-chain-deep-free-element-%d", i);
        rt_array_push(r, handle(payload));
        rt_array_push(r, mkstr(buf));
        roots[i] = r;
    }
    peak = rt_heap_registry_count();
    check(peak == base + 3 * N, "batch registered 3 objects per structure");

    int freed = 0;
    for (int i = 0; i < N; i += 2) {
        if (rt_array_free_deep(handle(roots[i])) == 1) freed++;
    }
    check(freed == N / 2, "every even-indexed structure deep-freed");
    check(rt_heap_registry_count() == peak - 3 * freed, "registry dropped by exactly 3 per freed structure");

    int survivors_ok = 1;
    for (int i = 1; i < N; i += 2) {
        snprintf(buf, sizeof buf, "probe-chain-deep-free-element-%d", i);
        if (rt_array_len(roots[i]) != 2) { survivors_ok = 0; break; }
        if (rt_array_len((SplArray*)(uintptr_t)rt_array_get(roots[i], 0)) != 16) { survivors_ok = 0; break; }
        if (rt_string_len(rt_array_get(roots[i], 1)) != (int64_t)strlen(buf)) { survivors_ok = 0; break; }
    }
    check(survivors_ok, "all survivors (and their nested elements) still readable");

    int refreed = 0;
    for (int i = 1; i < N; i += 2) {
        if (rt_array_free_deep(handle(roots[i])) == 1) refreed++;
    }
    check(refreed == N / 2, "every survivor still found in both registries and freed");
    check(rt_heap_registry_count() == base, "whole batch reclaimed, nothing stranded");

    /* ---- 10. the tables still work after all that churn ---- */
    SplArray* post = rt_array_new(4);
    rt_array_push(post, mkstr("post-churn allocation must still register and free"));
    check(rt_array_free_deep(handle(post)) == 1, "post-churn structure frees");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
