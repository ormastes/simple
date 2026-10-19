# Coherence suggestion loses optional payload metadata

Status: consumer mitigation authored; execution UNRUN.
Requirement: REQ-ENUM-COHERENCE-PAYLOAD in
`doc/03_plan/sys_test/robust_any_enum_extension_2026-10-14.md`.

Historical enum audit group 155 identified a payload mismatch at slot 2 of
`CoherenceError.OrphanImpl`. `check_orphan_rules` merges `Some(text)` and `nil`
into an unannotated local, then supplies it to the declared `text?` slot. That
source witness remains in release base
`7ac25381e98545e7ad57503428094d1b1e3811ba`; collector PR 3762 and PassScope PR
3765 have already landed and are not repeated by this repair.

The mitigation explicitly types the existing suggestion local as `text?`.
The diagnostic renderer qualifies all four `CoherenceError` patterns and keeps
them exhaustive, preserving the exact text and payload order. It adds no
catch-all, automatic payload conversion, or foreign-owner compatibility.
This is a consumer metadata repair, not a general fix to branch-join inference.

Executable regressions:

- `test/01_unit/compiler/traits/trait_coherence_optional_payload_spec.spl`
  checks actual orphan diagnostics with absent/present suggestions, local
  trait/type exceptions, inherent implementations, all current message
  variants, and a bounded 128-local-type registry without mutation.
- `test/01_unit/compiler/mir/optional_enum_payload_owner_spec.spl` adds real
  frontend/HIR/MIR checks for a typed Some/nil text merge and a wrong optional
  boolean merge into a text slot.
- `test/01_unit/compiler/mir/enum_payload_extension_boundary_spec.spl` calls
  the production metadata boundary with a registered declaration, injected
  unsupported payload kind, unknown variant, and wrong arities. These are
  exact diagnostic assertions; they are not a full native enum-mutation run.

The small boundary spec uses current named HIR constructors. The older
`declared_enum_constructor_spec.spl` helper omits required HirEnum presence
fields and attributes and supplies nil to desugared text fields. That existing
fixture debt was found by source inspection; this change does not silently
depend on it or claim that older suite passes.

Performance/memory boundary: the existing O(1) `local_types.len()` query stays
in place. No new iteration, materialized key array, cloning, or allocator call
was added in production. The bounded registry scenario verifies behavior and
nonmutation only; time, RSS, allocations, and native performance remain UNRUN.

Group 155 remains runtime-open until the source-matched compiler executes
these regressions. Groups 99/104/108/111/116/117/120 retain their prior unresolved
boundaries; no exact receiver proof for the Result unwrap diagnostics was
established here. No universal enum completion, formal proof, or release PASS
is claimed. Root controls the existing six-total retry cap and normal landing.
