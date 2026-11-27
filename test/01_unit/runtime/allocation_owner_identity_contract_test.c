/* Real full native provider; inspect actual registered allocations, not a
 * reconstructed state model or a substitute allocator. Build with the same
 * canonical standalone owner composition as the scope-identity fixture. */
#include "../../../src/runtime/runtime_native.c"

static int allocated_owner_matches(uint32_t expected) {
    SplArray* value = rt_array_new(1);
    RtCoreArray* array = rt_core_array_ptr(value);
    if (!array || array->transient_scope_id != expected) return 0;
    /* Process allocations have no scope sweep; scope/session allocations are
     * deliberately retained here so their actual owners reclaim them. */
    if (!expected) rt_array_free(value);
    return 1;
}

#define REQUIRE(condition, code) do { if (!(condition)) return (code); } while (0)
int main(void) {
    REQUIRE(rt_allocation_owner_identity_v1() == 0 && allocated_owner_matches(0), 1);
    REQUIRE(!rt_session_alloc_begin(), 2);
    uint32_t session = rt_session_heap_begin();
    REQUIRE(session > 0, 3);
    REQUIRE(rt_allocation_owner_identity_v1() == -(int64_t)session &&
        allocated_owner_matches(session), 4);
    REQUIRE(rt_transient_array_scope_begin(), 5);
    int64_t scope = rt_transient_array_scope_identity_v1();
    REQUIRE(scope > 0 && rt_transient_array_scope_state_v1() == 1, 6);
    REQUIRE(rt_allocation_owner_identity_v1() == scope &&
        allocated_owner_matches((uint32_t)scope), 7);
    REQUIRE(rt_session_alloc_begin(), 8);
    REQUIRE(rt_transient_array_scope_identity_v1() == scope &&
        rt_transient_array_scope_state_v1() == 1 &&
        rt_allocation_owner_identity_v1() == -(int64_t)session &&
        allocated_owner_matches(session), 9);
    REQUIRE(rt_session_alloc_begin() && rt_session_alloc_end(), 10);
    REQUIRE(rt_allocation_owner_identity_v1() == -(int64_t)session &&
        allocated_owner_matches(session), 11);
    REQUIRE(rt_session_alloc_end(), 12);
    REQUIRE(rt_transient_array_scope_identity_v1() == scope &&
        rt_transient_array_scope_state_v1() == 1 &&
        rt_allocation_owner_identity_v1() == scope &&
        allocated_owner_matches((uint32_t)scope), 13);
    REQUIRE(!rt_session_alloc_end(), 14);
    REQUIRE(rt_transient_array_scope_pause(), 15);
    REQUIRE(rt_transient_array_scope_identity_v1() == scope &&
        rt_allocation_owner_identity_v1() == -(int64_t)session &&
        allocated_owner_matches(session), 16);
    REQUIRE(rt_session_alloc_begin() && rt_session_alloc_end(), 17);
    REQUIRE(rt_allocation_owner_identity_v1() == -(int64_t)session &&
        allocated_owner_matches(session), 18);
    REQUIRE(rt_transient_array_scope_end(), 19);
    REQUIRE(rt_allocation_owner_identity_v1() == -(int64_t)session, 20);
    REQUIRE(rt_session_heap_end(session), 21);
    REQUIRE(rt_allocation_owner_identity_v1() == 0 && allocated_owner_matches(0), 22);
    REQUIRE(rt_transient_array_scope_begin(), 23);
    int64_t newer_scope = rt_transient_array_scope_identity_v1();
    REQUIRE(newer_scope > scope && rt_allocation_owner_identity_v1() == newer_scope &&
        allocated_owner_matches((uint32_t)newer_scope), 24);
    REQUIRE(rt_transient_array_scope_pause(), 25);
    REQUIRE(rt_allocation_owner_identity_v1() == 0 && allocated_owner_matches(0), 26);
    REQUIRE(rt_transient_array_scope_end(), 27);
    uint32_t newer_session = rt_session_heap_begin();
    REQUIRE(newer_session > session && rt_allocation_owner_identity_v1() == -(int64_t)newer_session,
        28);
    REQUIRE(rt_session_heap_end(newer_session), 29);
    REQUIRE(rt_allocation_owner_identity_v1() == 0, 30);
    return 0;
}
