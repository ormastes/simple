/* Scoped parser-heap reclamation self-check.
 *
 * The core-C bootstrap runtime capsule compiles and runs this check.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "../runtime.h"

extern int64_t rt_dict_new(int64_t cap_hint);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value);

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

static clock_t time_empty_scopes(int count) {
    clock_t start = clock();
    if (start == (clock_t)-1) return (clock_t)-1;
    for (int i = 0; i < count; i++) {
        if (!rt_transient_array_scope_begin() || !rt_transient_array_scope_end()) {
            return (clock_t)-1;
        }
    }
    clock_t finish = clock();
    return finish == (clock_t)-1 ? (clock_t)-1 : finish - start;
}

typedef struct Graph {
    SplArray* outer;
    SplArray* inner;
    int64_t dict;
    int64_t enum_value;
    int64_t closure;
    int64_t float_value;
} Graph;

static Graph make_graph(int32_t enum_id) {
    Graph graph = {0};
    graph.outer = rt_array_new(2);
    graph.inner = rt_array_new(2);
    graph.dict = rt_dict_new(0);
    graph.float_value = rt_value_float(0.125);
    graph.enum_value = rt_enum_new(enum_id, 1, graph.float_value);
    graph.closure = rt_closure_new(1, 1);
    rt_array_push(graph.outer, graph.dict);
    rt_dict_set(graph.dict, graph.enum_value, graph.closure);
    rt_closure_set_capture(graph.closure, 0, (int64_t)(uintptr_t)graph.inner);
    rt_array_push(graph.inner, graph.float_value);
    rt_array_push(graph.inner, (int64_t)(uintptr_t)graph.outer);
    return graph;
}

int main(void) {
    const int64_t baseline = rt_heap_registry_count();

    check(rt_transient_array_scope_begin() == 1, "unpromoted scope begins");
    Graph reclaimed = make_graph(700001);
    check(reclaimed.outer && reclaimed.inner && reclaimed.dict && reclaimed.enum_value &&
              reclaimed.closure && reclaimed.float_value,
          "unpromoted graph allocates");
    check(rt_heap_registry_count() == baseline + 6, "all unpromoted graph nodes register");
    check(rt_transient_array_scope_end() == 1, "unpromoted scope ends");
    check(rt_heap_registry_count() == baseline, "unpromoted graph is reclaimed and unregistered");

    check(rt_transient_array_scope_begin() == 1, "promoted scope begins");
    Graph kept = make_graph(700002);
    int64_t* carrier_child = (int64_t*)rt_alloc((int64_t)sizeof(int64_t));
    int64_t* carrier_root = (int64_t*)rt_alloc((int64_t)sizeof(int64_t));
    check(carrier_child && carrier_root, "raw aggregate carriers allocate");
    carrier_child[0] = (int64_t)(uintptr_t)kept.inner;
    carrier_root[0] = (int64_t)(uintptr_t)kept.outer;
    rt_array_push(kept.outer, (int64_t)(uintptr_t)carrier_child);
    check(rt_transient_array_scope_pause() == 1, "scope pauses before promotion");
    int carriers_promoted =
        rt_transient_heap_promote((int64_t)((uintptr_t)carrier_root | 1));
    check(carriers_promoted == 1,
          "tagged raw root promotes through collection and raw aggregate edges");
    check(rt_transient_last_promoted_nodes() == 8,
          "promotion reports exactly two raw carriers plus six heap nodes");
    check(rt_transient_last_promoted_bytes() > 8 * (int64_t)sizeof(int64_t),
          "promotion reports retained header and backing bytes");
    check(rt_transient_heap_promote(kept.dict) == 1,
          "a second promotion of the retained graph succeeds");
    check(rt_transient_array_scope_end() == 1, "promoted scope ends");
    if (carriers_promoted) {
        rt_free(carrier_root);
        rt_free(carrier_child);
    }
    check(rt_heap_registry_count() == baseline + 6, "promoted graph registry count is bounded");
    check(rt_array_len(kept.outer) == 2, "promoted array survives");
    check(rt_dict_get(kept.dict, kept.enum_value) == kept.closure,
          "promoted dict key and value survive");
    check(rt_enum_payload(kept.enum_value) == kept.float_value,
          "promoted enum payload survives");
    check(rt_closure_get_capture(kept.closure, 0) == (int64_t)(uintptr_t)kept.inner,
          "promoted closure capture survives");
    check(rt_array_get(kept.inner, 0) == kept.float_value &&
              rt_value_as_float(kept.float_value) == 0.125,
          "promoted nested array and boxed float survive");

    check(rt_transient_array_scope_begin() == 1, "follow-up scope begins");
    check(rt_array_new(1) != NULL, "follow-up scoped allocation succeeds");
    check(rt_transient_array_scope_end() == 1, "follow-up scope ends");
    check(rt_heap_registry_count() == baseline + 6,
          "later reclamation leaves the promoted registry bound unchanged");

    /* CONTRACT (ast_arena_reset_inside_transient_scope_2026-08-01): an object
     * born inside a scope and NOT promoted is DEAD after scope end -- and the
     * death is SILENT, not a crash. A caller that parks process-lifetime state
     * (e.g. the flat-AST arena globals stmt_tag, expr_tag, decl_tag) in a
     * scope gets an
     * array that reports no length forever, drops every push, and no-ops every
     * clear. That is what produced the Stage 4 `[stmt_get_tag] OOB ...
     * arena_len=0` flood: ast_reset() reallocated arena state while a transient
     * parse scope was still active, and scope end then freed it. This case pins
     * the behaviour so the hazard stays visible to anyone adding a new
     * rt_transient_array_scope_begin() call site. The CONTROL array allocated
     * outside the scope must stay healthy, so this cannot pass vacuously. */
    SplArray* outside_control = rt_array_new(0);
    check(rt_array_push(outside_control, 41) == 1 &&
              rt_array_push(outside_control, 42) == 1 &&
              rt_array_len(outside_control) == 2,
          "scope-death CONTROL array (allocated outside) is healthy");
    check(rt_transient_array_scope_begin() == 1, "scope-death scope begins");
    SplArray* born_in_scope = rt_array_new(0);
    check(born_in_scope != NULL && rt_array_push(born_in_scope, 7) == 1 &&
              rt_array_len(born_in_scope) == 1,
          "array born inside the scope is healthy WHILE the scope is open");
    check(rt_transient_array_scope_end() == 1, "scope-death scope ends");
    check(rt_array_len(born_in_scope) <= 0,
          "unpromoted scope-born array reports no length after scope end");
    check(rt_array_push(born_in_scope, 8) == 0,
          "push into an unpromoted scope-born array is SILENTLY dropped");
    check(rt_array_len(born_in_scope) <= 0,
          "an unpromoted scope-born array can never grow again");
    check(rt_array_clear(born_in_scope) == 0,
          "clear on an unpromoted scope-born array is a SILENT no-op");
    check(rt_array_len(outside_control) == 2 && rt_array_get(outside_control, 1) == 42,
          "scope-death CONTROL array is unaffected by the scope");

    /* CONTRACT: a raw rt_alloc block born in a scope and left unpromoted is
     * reclaimed at scope end. Under SIMPLE_MEM_GUARD_RATE that block can be a
     * SAMPLED GUARD SLOT -- a page-aligned mmap mapping, not a libc heap chunk
     * -- so reclamation must route it through the guard's own free path and
     * never through free(). Handing an mmap slot to free() is undefined
     * behaviour and aborts under glibc. Without this case the guard-slot branch
     * of transient raw reclamation is never entered, so it would ship
     * unverified. The CONTROL block is promoted and read back after scope end,
     * so a broken rt_alloc cannot let this pass vacuously. Run this file with
     * SIMPLE_MEM_GUARD_RATE=1 to exercise the sampled path. */
    check(rt_transient_array_scope_begin() == 1, "raw-reclaim scope begins");
    int64_t* raw_dropped = (int64_t*)rt_alloc((int64_t)sizeof(int64_t) * 4);
    int64_t* raw_control = (int64_t*)rt_alloc((int64_t)sizeof(int64_t) * 4);
    check(raw_dropped != NULL && raw_control != NULL,
          "scope-born raw blocks allocate");
    raw_dropped[0] = 0x5AFE;
    check(raw_dropped[0] == 0x5AFE, "unpromoted scope-born raw block is writable");
    check(rt_transient_array_scope_pause() == 1, "raw-reclaim scope pauses");
    check(rt_transient_heap_promote((int64_t)((uintptr_t)raw_control | 1)) == 1,
          "raw CONTROL block promotes");
    raw_control[0] = 0x600D;
    check(rt_transient_array_scope_end() == 1,
          "scope end reclaims the unpromoted raw block without aborting");
    check(raw_control[0] == 0x600D,
          "promoted raw CONTROL block survives reclamation of its sibling");
    rt_free(raw_control);

    int64_t string_base = rt_heap_registry_count();
    check(rt_transient_array_scope_begin() == 1, "direct-string scope begins");
    int64_t direct_string = rt_string_new(
        (const uint8_t*)"transient-direct-string", 23);
    check(rt_heap_registry_count() == string_base + 1,
          "ordinary pre-pause string registers in the scope");
    check(rt_transient_array_scope_end() == 1, "direct-string scope ends");
    check(rt_heap_registry_count() == string_base,
          "unpromoted ordinary string is reclaimed");

    check(rt_transient_array_scope_begin() == 1, "aliased-string scope begins");
    int64_t aliased = rt_string_new((const uint8_t*)"aliased-transient", 17);
    SplArray* alias_a = rt_array_new(1);
    SplArray* alias_b = rt_array_new(1);
    rt_array_push(alias_a, aliased);
    rt_array_push(alias_b, aliased);
    check(rt_heap_registry_count() == string_base + 3,
          "one string alias and two owners register once each");
    check(rt_transient_array_scope_end() == 1, "aliased-string scope ends");
    check(rt_heap_registry_count() == string_base,
          "aliased string graph is reclaimed exactly once");

    check(rt_transient_array_scope_begin() == 1, "direct promoted-string scope begins");
    int64_t direct_promoted = rt_string_new((const uint8_t*)"direct-promoted", 15);
    check(rt_transient_array_scope_pause() == 1 &&
              rt_transient_heap_promote(direct_promoted) == 1,
          "a direct string root promotes");
    check(rt_transient_array_scope_end() == 1 && rt_string_len(direct_promoted) == 15,
          "direct promoted string survives");
    check(rt_string_free(direct_promoted) == 1,
          "direct promoted string remains explicitly reclaimable");

    int64_t graph_base = rt_heap_registry_count();
    check(rt_transient_array_scope_begin() == 1, "promoted-string graph scope begins");
    int64_t promoted_text = rt_string_new((const uint8_t*)"promoted-text-value", 19);
    (void)rt_string_new((const uint8_t*)"unreachable-sibling", 19);
    SplArray* promoted_root = rt_array_new(3);
    int64_t promoted_dict = rt_dict_new(0);
    int64_t promoted_enum = rt_enum_new(700003, 1, promoted_text);
    int64_t promoted_closure = rt_closure_new(1, 1);
    rt_closure_set_capture(promoted_closure, 0, promoted_text);
    rt_array_push(promoted_root, promoted_text);
    rt_array_push(promoted_root, promoted_dict);
    rt_array_push(promoted_root, promoted_closure);
    rt_dict_set(promoted_dict, promoted_text, promoted_enum);
    rt_dict_set(promoted_dict, promoted_enum, (int64_t)(uintptr_t)promoted_root);
    check(rt_transient_array_scope_pause() == 1, "promoted-string graph pauses");
    check(rt_transient_heap_promote((int64_t)(uintptr_t)promoted_root) == 1,
          "promotion walks string aliases, dict keys, enum payloads, and cycle");
    check(rt_transient_array_scope_end() == 1, "promoted-string graph scope ends");
    check(rt_string_len(promoted_text) == 19 &&
              rt_dict_get(promoted_dict, promoted_text) == promoted_enum &&
              rt_enum_payload(promoted_enum) == promoted_text &&
              rt_closure_get_capture(promoted_closure, 0) == promoted_text,
          "promoted string graph survives scope end");
    check(rt_heap_registry_count() == graph_base + 5,
          "unreachable sibling string is reclaimed while five graph nodes survive");

    static const uint8_t scoped_literal[] = "scope-shared-literal";
    int64_t shared_base = rt_heap_registry_count();
    check(rt_transient_array_scope_begin() == 1, "shared-string scope begins");
    int64_t shared_short = rt_string_new((const uint8_t*)"q", 1);
    int64_t shared_literal = rt_string_new_literal(
        scoped_literal, sizeof(scoped_literal) - 1);
    check(rt_transient_array_scope_end() == 1, "shared-string scope ends");
    check(rt_string_len(shared_short) == 1 &&
              rt_string_len(shared_literal) == (int64_t)sizeof(scoped_literal) - 1,
          "shared cache and literal-intern strings survive first creation in a scope");
    check(rt_string_new((const uint8_t*)"q", 1) == shared_short &&
              rt_string_new_literal(scoped_literal, sizeof(scoped_literal) - 1) == shared_literal,
          "shared cache and literal intern preserve pointer identity");
    check(rt_string_new_literal((const uint8_t*)"q", 1) == shared_short &&
              rt_string_free(shared_short) == 0,
          "one-byte literal reuses the ordinary short cache and refuses free");
    check(rt_heap_registry_count() == shared_base + 2,
          "shared strings remain registered without transient duplicates");

    int64_t paused_base = rt_heap_registry_count();
    check(rt_transient_array_scope_begin() == 1 &&
              rt_transient_array_scope_pause() == 1,
          "post-pause string scope begins and pauses");
    int64_t post_pause = rt_string_new((const uint8_t*)"post-pause-persistent", 21);
    check(rt_transient_array_scope_end() == 1, "post-pause string scope ends");
    check(rt_heap_registry_count() == paused_base + 1 && rt_string_len(post_pause) == 21,
          "ordinary post-pause string remains persistent by current scope contract");
    check(rt_string_free(post_pause) == 1 && rt_heap_registry_count() == paused_base,
          "post-pause test string remains explicitly reclaimable");

    int64_t repeated_base = rt_heap_registry_count();
    int repeated_ok = 1;
    for (int round = 0; round < 128; round++) {
        if (!rt_transient_array_scope_begin()) repeated_ok = 0;
        for (int item = 0; item < 256; item++) {
            char dynamic[48];
            int len = snprintf(dynamic, sizeof(dynamic),
                "scope-%d-transient-string-%d", round, item);
            if (rt_string_new((const uint8_t*)dynamic, (uint64_t)len) == 3) repeated_ok = 0;
        }
        if (!rt_transient_array_scope_end()) repeated_ok = 0;
        if (rt_heap_registry_count() != repeated_base) repeated_ok = 0;
    }
    check(repeated_ok, "repeated string scopes return the registry to a fixed bound");

    enum { PERSISTENT_STRINGS = 100000, PERSISTENT_ARRAYS = 20000, TIMED_SCOPES = 1024 };
    clock_t before_strings = time_empty_scopes(TIMED_SCOPES);
    int64_t persistent_base = rt_heap_registry_count();
    char text[64];
    for (int i = 0; i < PERSISTENT_STRINGS; i++) {
        int len = snprintf(text, sizeof(text), "persistent-scope-cost-probe-%d", i);
        (void)rt_string_new((const uint8_t*)text, (uint64_t)len);
    }
    check(rt_heap_registry_count() == persistent_base + PERSISTENT_STRINGS,
          "persistent strings remain registered");
    clock_t after_strings = time_empty_scopes(TIMED_SCOPES);
    double before_seconds = (double)before_strings / CLOCKS_PER_SEC;
    double after_seconds = (double)after_strings / CLOCKS_PER_SEC;
    check(before_strings != (clock_t)-1 && after_strings != (clock_t)-1 &&
              after_seconds <= before_seconds * 20.0 + 0.10,
          "scope-end cost stays bounded after 100000 persistent strings");

    int64_t array_base = rt_heap_registry_count();
    int arrays_ok = 1;
    for (int i = 0; i < PERSISTENT_ARRAYS; i++) {
        if (rt_array_new(0) == NULL) arrays_ok = 0;
    }
    check(arrays_ok, "persistent arrays allocate");
    check(rt_heap_registry_count() == array_base + PERSISTENT_ARRAYS,
          "persistent arrays remain registered");
    clock_t after_arrays = time_empty_scopes(TIMED_SCOPES);
    double after_array_seconds = (double)after_arrays / CLOCKS_PER_SEC;
    check(after_arrays != (clock_t)-1 &&
              after_array_seconds <= after_seconds * 20.0 + 0.10,
          "scope-end cost stays bounded after 20000 persistent arrays");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
