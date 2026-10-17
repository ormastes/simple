# Selected C runtime omitted tagged-value predicates

Fresh Stage1-to-Phase2 diagnostic cycle1 compiled1353 units with0compile failures, then failed link on rt_value_is_nil/bool/int and __simple_pow. Runtime ownership is the selected core-C provider; no generated stubs are allowed. The predicate declarations already exist in canonical Simple SFFI wrappers, and Rust runtime provides corresponding operations.

Add C provider functions using existing runtime constants/helpers, returning the established I8 boolean ABI. Nil checks exact selected nil; bool accepts true and false only; int accepts tagged immediate, registered wide signed integer and registered wide unsigned integer. Registry checks precede heap dereference through existing owners. No raw integer is reinterpreted as an owned heap value.

The separate power symbol already belongs to runtime_core_intrinsics.c. Current source source-list includes that translation unit, while retained Stage1 seed does not. Repair its diagnostic link through that actual provider object, never a dummy pow or new duplicate definition in runtime_native.c.

Status: source fix, native checks pending. Bug DB reconciliation pending qualified tooling. Original source652227c35f7a45ccfd3cedce5d446f489a26dde2; bootstrap seed951cf2f1936b72d1f0b9412639e6e1908550b17ab6911959afadbb8d3ee399f0. Retained objects/logs in external fresh-stage2-direct-cycle1 directory. No Phase3 or deployment success.
