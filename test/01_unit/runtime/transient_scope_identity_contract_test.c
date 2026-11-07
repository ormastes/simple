/* Full native provider. Reuse the common real-provider lifecycle/thread
 * harness, then exercise this provider's actual private exhaustion counter.
 * No allocator replacement, fabricated scope, or backfilled extern. */
#include "../../../src/runtime/runtime_native.c"
#define main scope_state_and_identity_contract
#include "transient_scope_state_contract_test.c"
#undef main

#define REQUIRE(condition, code) do { if (!(condition)) return (code); } while (0)
int main(void) {
    int result = scope_state_and_identity_contract();
    if (result) return result;
    /* No resume/nested operation exists: begin refuses while active/paused.
     * The common test verifies the same ID survives those refused attempts. */
    /* Advance only this isolated test process's real allocator counter. */
    atomic_store_explicit(&rt_core_transient_array_scope_next_id, UINT32_MAX - 1,
        memory_order_relaxed);
    REQUIRE(rt_transient_array_scope_begin(), 26);
    REQUIRE(rt_transient_array_scope_identity_v1() == (int64_t)UINT32_MAX - 1, 27);
    REQUIRE(rt_transient_array_scope_end() && rt_transient_array_scope_begin(), 28);
    REQUIRE(rt_transient_array_scope_identity_v1() == (int64_t)UINT32_MAX, 29);
    REQUIRE(rt_transient_array_scope_end(), 30);
    REQUIRE(!rt_transient_array_scope_begin() && !rt_transient_array_scope_begin(), 31);
    REQUIRE(rt_transient_array_scope_identity_v1() == 0 &&
        rt_transient_array_scope_state_v1() == 0, 32);
    REQUIRE(atomic_load_explicit(&rt_core_transient_scope_owner,
        memory_order_acquire) == 0, 33);
    return 0;
}
