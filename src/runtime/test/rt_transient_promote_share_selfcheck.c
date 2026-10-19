/* Promotion share-window self-check.
 *
 * MIR's promote_transient_owner promotes ~190 overlapping roots back to back.
 * rt_transient_heap_promote_share_begin/end let those calls share one
 * committed-node set so the common subgraph is walked once. The window must
 * be lifetime-neutral: this check builds the same overlapping-roots graph
 * twice, promotes it once without and once with a window, and requires the
 * exact same set of objects to survive scope end -- including a transient
 * child stored into a PERSISTENT carrier (no write barrier exists, so walks
 * must never stop merely because a node is already persistent/promoted) and
 * a transient child reached only through a recycled temporary carrier.
 */
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>

#include "../runtime.h"

static int failures = 0;

static void check(int condition, const char* message) {
    if (condition) {
        printf("  ok   %s\n", message);
    } else {
        printf("  FAIL %s\n", message);
        failures++;
    }
}

static int64_t as_value(SplArray* array) { return (int64_t)(uintptr_t)array; }

static int64_t text(const char* bytes) {
    return rt_string_new((const uint8_t*)bytes, strlen(bytes));
}

enum {
    OBJ_SHARED, OBJ_SHARED_TEXT, OBJ_DICT, OBJ_DICT_KEY, OBJ_DICT_VALUE, OBJ_ENUM,
    OBJ_RAW, OBJ_RAW_TEXT, OBJ_ROOT_A, OBJ_ROOT_B, OBJ_ONLY_A, OBJ_ONLY_B,
    OBJ_PERSISTENT_CHILD, OBJ_LATE_CHILD, OBJ_DISCARDED, OBJ_COUNT
};

static const char* const OBJ_NAMES[OBJ_COUNT] = {
    "shared array", "shared text", "dict", "dict key", "dict value", "enum",
    "raw struct", "raw text", "root A", "root B", "only-A text", "only-B text",
    "persistent carrier child", "late carrier child", "discarded text"};

/* Promote one root the way MIR does: through a released one-element carrier. */
static int promote_through_carrier(int64_t root) {
    SplArray* carrier = rt_array_new(1);
    rt_array_push(carrier, root);
    int ok = rt_transient_heap_promote(as_value(carrier)) == 1;
    rt_array_free(carrier);
    return ok;
}

/* Builds the overlapping-roots graph in a fresh scope, promotes it with or
 * without a share window, ends the scope and records which objects survived.
 * Returns 1 when every scope/promote step answered success. */
static int run_case(int shared, int live[OBJ_COUNT], SplArray* persistent_carrier) {
    int64_t obj[OBJ_COUNT] = {0};
    int ok = rt_transient_array_scope_begin() == 1;
    SplArray* shared_array = rt_array_new(4);
    obj[OBJ_SHARED] = as_value(shared_array);
    obj[OBJ_SHARED_TEXT] = text("shared transient text reached by every root");
    obj[OBJ_DICT] = rt_dict_new(0);
    obj[OBJ_DICT_KEY] = text("dict key reached through the shared array");
    obj[OBJ_DICT_VALUE] = text("dict value reached through the shared array");
    rt_dict_set(obj[OBJ_DICT], obj[OBJ_DICT_KEY], obj[OBJ_DICT_VALUE]);
    obj[OBJ_ENUM] = rt_enum_new(910001, 1, obj[OBJ_DICT]);
    rt_array_push(shared_array, obj[OBJ_SHARED_TEXT]);
    rt_array_push(shared_array, obj[OBJ_ENUM]);
    int64_t* raw = (int64_t*)rt_alloc((int64_t)(2 * sizeof(int64_t)));
    obj[OBJ_RAW] = (int64_t)(uintptr_t)raw;
    obj[OBJ_RAW_TEXT] = text("text reached only through a raw struct word");
    if (raw) {
        raw[0] = obj[OBJ_RAW_TEXT];
        raw[1] = obj[OBJ_SHARED];
    }
    rt_array_push(shared_array, obj[OBJ_RAW]);

    SplArray* root_a = rt_array_new(2);
    SplArray* root_b = rt_array_new(2);
    obj[OBJ_ROOT_A] = as_value(root_a);
    obj[OBJ_ROOT_B] = as_value(root_b);
    obj[OBJ_ONLY_A] = text("text reached only from root A");
    obj[OBJ_ONLY_B] = text("text reached only from root B");
    rt_array_push(root_a, obj[OBJ_SHARED]);
    rt_array_push(root_a, obj[OBJ_ONLY_A]);
    rt_array_push(root_b, obj[OBJ_SHARED]);
    rt_array_push(root_b, obj[OBJ_ONLY_B]);
    /* Root B also points back at root A: overlapping, cyclic-ish roots. */
    rt_array_push(root_b, obj[OBJ_ROOT_A]);

    /* A persistent (pre-scope) carrier mutated to hold a transient child. */
    obj[OBJ_PERSISTENT_CHILD] = text("transient child stored into a persistent carrier");
    rt_array_push(persistent_carrier, obj[OBJ_PERSISTENT_CHILD]);
    obj[OBJ_LATE_CHILD] = text("transient child reached only via a recycled carrier");
    obj[OBJ_DISCARDED] = text("transient text reachable from no root");

    ok = rt_transient_array_scope_pause() == 1 && ok;
    if (shared) ok = rt_transient_heap_promote_share_begin() == 1 && ok;
    ok = promote_through_carrier(obj[OBJ_ROOT_A]) && ok;
    ok = promote_through_carrier(obj[OBJ_ROOT_B]) && ok;
    ok = promote_through_carrier(obj[OBJ_SHARED]) && ok;
    ok = promote_through_carrier(obj[OBJ_ENUM]) && ok;
    /* The persistent carrier was already persistent; its new child must still
     * be found (no early stop at non-transient nodes). Promote it twice so the
     * second call runs against an already-committed carrier. */
    ok = promote_through_carrier(as_value(persistent_carrier)) && ok;
    ok = promote_through_carrier(as_value(persistent_carrier)) && ok;
    /* Freed carriers above may be recycled; a new carrier at a recycled
     * address must still be walked. */
    ok = promote_through_carrier(obj[OBJ_LATE_CHILD]) && ok;
    if (shared) ok = rt_transient_heap_promote_share_end() == 1 && ok;
    ok = rt_transient_array_scope_end() == 1 && ok;

    /* Raw structs are not in the C immortal registry; their liveness is
     * probed separately by raw_survives_probe. */
    for (int i = 0; i < OBJ_COUNT; i++) {
        live[i] = obj[i] != 0 && rt_heap_ref_registered_c(obj[i]) == 1;
    }
    return ok;
}

/* Raw allocations are tracked outside the immortal registry: observe their
 * survival through the data they carry instead. */
static int raw_survives_probe(int shared) {
    int ok = rt_transient_array_scope_begin() == 1;
    int64_t child = text("raw-carried text that must outlive the scope");
    int64_t* raw = (int64_t*)rt_alloc((int64_t)sizeof(int64_t));
    if (!raw) return 0;
    raw[0] = child;
    SplArray* root = rt_array_new(1);
    rt_array_push(root, (int64_t)(uintptr_t)raw);
    ok = rt_transient_array_scope_pause() == 1 && ok;
    if (shared) ok = rt_transient_heap_promote_share_begin() == 1 && ok;
    ok = promote_through_carrier(as_value(root)) && ok;
    ok = promote_through_carrier((int64_t)(uintptr_t)raw) && ok;
    if (shared) ok = rt_transient_heap_promote_share_end() == 1 && ok;
    ok = rt_transient_array_scope_end() == 1 && ok;
    ok = ok && raw[0] == child && rt_heap_ref_registered_c(child) == 1 &&
        rt_heap_ref_registered_c(as_value(root)) == 1;
    rt_free(raw);
    return ok;
}

static double time_overlapping_roots(int shared, int roots, int width, int* ok_out) {
    int ok = rt_transient_array_scope_begin() == 1;
    SplArray* common = rt_array_new(width);
    for (int i = 0; i < width; i++) {
        char buf[64];
        int len = snprintf(buf, sizeof(buf), "common-subgraph-node-%d", i);
        rt_array_push(common, rt_string_new((const uint8_t*)buf, (uint64_t)len));
    }
    ok = rt_transient_array_scope_pause() == 1 && ok;
    clock_t start = clock();
    if (shared) ok = rt_transient_heap_promote_share_begin() == 1 && ok;
    for (int r = 0; r < roots; r++) ok = promote_through_carrier(as_value(common)) && ok;
    if (shared) ok = rt_transient_heap_promote_share_end() == 1 && ok;
    clock_t finish = clock();
    ok = rt_transient_array_scope_end() == 1 && ok;
    ok = ok && rt_array_len(common) == width &&
        rt_heap_ref_registered_c(rt_array_get(common, width - 1)) == 1;
    *ok_out = ok;
    return (double)(finish - start) / CLOCKS_PER_SEC;
}

int main(void) {
    check(rt_transient_heap_promote_share_begin() == 0,
          "share window refuses to open without a paused scope");
    check(rt_transient_heap_promote_share_end() == 0,
          "share end reports no open window");

    SplArray* carrier_plain = rt_array_new(1);   /* persistent: pre-scope */
    SplArray* carrier_shared = rt_array_new(1);
    int live_plain[OBJ_COUNT];
    int live_shared[OBJ_COUNT];
    check(run_case(0, live_plain, carrier_plain) == 1,
          "unshared promotion of overlapping roots succeeds");
    check(run_case(1, live_shared, carrier_shared) == 1,
          "shared-window promotion of overlapping roots succeeds");

    int same = 1;
    for (int i = 0; i < OBJ_COUNT; i++) {
        if (i == OBJ_RAW) continue; /* raw liveness is probed separately */
        if (live_plain[i] != live_shared[i]) {
            printf("    mismatch: %s unshared=%d shared=%d\n",
                   OBJ_NAMES[i], live_plain[i], live_shared[i]);
            same = 0;
        }
    }
    check(same, "shared window promotes exactly the same object set");

    int reachable_live = 1;
    for (int i = 0; i < OBJ_COUNT; i++) {
        if (i == OBJ_RAW || i == OBJ_DISCARDED) continue;
        if (!live_shared[i]) {
            printf("    left transient (freed) though reachable: %s\n", OBJ_NAMES[i]);
            reachable_live = 0;
        }
    }
    check(reachable_live,
          "no transient object reachable from a promoted root is left unpromoted");
    check(live_plain[OBJ_PERSISTENT_CHILD] && live_shared[OBJ_PERSISTENT_CHILD],
          "transient child of a persistent carrier is still promoted (no early stop)");
    check(live_shared[OBJ_LATE_CHILD],
          "root behind a recycled carrier address is still walked");
    check(!live_plain[OBJ_DISCARDED] && !live_shared[OBJ_DISCARDED],
          "unreachable transient object is reclaimed in both modes");
    check(raw_survives_probe(0) && raw_survives_probe(1),
          "raw struct edge survives identically with and without a window");

    int ok_plain = 0, ok_shared = 0;
    double plain_s = time_overlapping_roots(0, 190, 4000, &ok_plain);
    double shared_s = time_overlapping_roots(1, 190, 4000, &ok_shared);
    printf("    190 overlapping roots x 4000 nodes: unshared %.4fs, shared %.4fs\n",
           plain_s, shared_s);
    check(ok_plain && ok_shared, "timed overlapping-root promotions retain the subgraph");
    check(shared_s <= plain_s, "shared window is not slower than per-root re-walks");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
