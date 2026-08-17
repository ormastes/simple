# Coverage probe plan attributes 0 lines/decisions to executed struct methods

**Date:** 2026-08-15
**Status:** OPEN
**Severity:** P3 — coverage measurement blind spot, not a runtime defect

## Symptom

`src/lib/nogc_sync_mut/gpu/engine2d/vulkan_presenter.spl` struct methods
(`VulkanEngine2dPresenterReceipt.is_valid`,
`VulkanEngine2dPresentDamageReceipt.is_direct_partial_present`) demonstrably
execute under `bin/simple test --coverage` (11 assertions on their results
pass in
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl),
yet the coverage report attributes **0/91 lines and 0/0 decisions** to the
module — any `@cover` threshold on it fails vacuously.

## Impact

Modules whose logic lives in struct methods (as opposed to free functions or
class methods) cannot be coverage-gated; per-layer coverage campaigns must
skip them, understating real coverage.

## Unblock

Extend the probe plan/runtime store attribution to struct-method bodies, or
document the scope limit in the coverage guide. Cross-check whether class
methods and free functions in the same file attribute correctly (they do in
sibling modules, e.g. vulkan_present_damage_gate.spl 9/9).

## 2026-08-17 triage — BLOCKED in this lane, with the reason

Not closed and not fixed. Scoping pass located the candidate owners
(`src/compiler/10.frontend/core/ast_coverage_inventory.spl`,
`src/compiler/50.mir/mir_coverage_probe_admission.spl`, and the seed's
`src/compiler_rust/compiler/src/interpreter_extern/coverage.rs`); neither
`.spl` file branches on struct-vs-class-vs-free-function at all, which points
attribution at the seed side.

Two concrete blockers, stated rather than worked around:

1. `interpreter_extern/coverage.rs` currently carries ~1,369 lines of
   uncommitted changes from a parallel session in this shared working tree.
   Editing it now would either clobber that work or produce a fix that cannot
   be attributed; and any seed change needs a rebuild to take effect.
2. Confirming a fix requires a real coverage run
   (`SIMPLE_COVERAGE=1 bin/simple test <spec> --no-cache --no-cover-check
   --timeout 1800`), which exceeds this lane's one-process-at-a-time budget.

Unblock: once the seed changes in flight have landed, re-run the
`vulkan_present_damage_gate_branch_coverage_spec.spl` coverage measurement and
attribute struct-method bodies in the probe plan. Severity stays P3.
