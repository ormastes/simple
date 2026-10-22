# Cold HIR capture ownership

The typed HIR emitter used the private artifact directory digest as its
`module_identity`. The cold HIR publisher, MIR capture, and native V2 consumer
all compare that field against the logical HIR module owner. For a normal name
such as `std.emission`, the old output therefore fails those identity gates.
The emitter now returns the actual `module.name` and retains the same original
directory digest in the separate `artifact_identity` field. Existing private
root derivation, ancestor/no-follow checks, exclusive bounded writes, readback,
and file hashes are unchanged. The logical owner checks remain required.

`driver_cold_hir_capture_module_in_owned_scope_v1` consumes one complete live
HIR module in an active unpaused lease. It invokes the existing admitted-entry
typed ABI consumer. For a full inventory capture it also invokes the real SMF
emitter and derives the native emission witness from that same complete HIR,
including all original function, data/default and runtime initialization rows.
It neither substitutes declarations for bodies nor fabricates active counts.

The retained-body wrapper starts one scratch scope, pauses and promotes only
the whole scalar/text receipt result and existing cache diagnostic owner, then
closes the scope. It never promotes the input HIR. A borrowed archive caller
must supply its correctly admitted complete body inside its own decode lease.
The helper opens/closes/promotes nothing in that borrowed path.

This is capture mechanics, not SCV or driver-stage admission. The actual
compilation owner must still validate snapshot/inventory generation, retained
physical source rows, target CFG, source counts and selected artifact authority,
and supply the body at the existing post-validation/post-weave capture point.
No production route is switched by this helper. A lowered-unresolved original
archive alone cannot substitute for an admitted transformed parent.

Four authored compiled-only specs use real parsing/lowering and verify actual
typed ABI parity after closure, changed owner/byte-count refusals, borrowed and
occupied/paused ownership, real artifact publication and actual witness/count
parity. The existing emitter spec now checks distinct logical and storage
identities with the exact physical directory suffix. Neither set has run under
the prepared compiler. Source review/diff checks do not qualify native ownership,
the complete bootstrap, or full CLI RSS.
